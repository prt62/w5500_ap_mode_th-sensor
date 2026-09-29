// ==========================================================================
// ==========================================================================
// COMMAND LIST:
/*
 AUTH,123456#
 GET#
 WIFI#
 LAN#
 LOG#
 CONFIG#       <-- Web Configuration Mode On Karne ke liye
 WIFI,Ajeevi_Net,Pass1234#
 LANIP,192.168.1.100,192.168.1.1,255.255.255.0,8.8.8.8#   (actual parser prefix: NET,ip,subnet,gateway,dns#)
 DHCP#
 STATIC#
 SERVER,192.168.1.100,8080#
 DATA,60#
 TEMP,35.5#    <-- Temperature Alert Set (0 for Disable)
 HUM,80.0#     <-- Humidity Alert Set (0 for Disable)
 PASS,newpassword#
 REST#
 FACTORY#

  Isko use kaise karein?
1. Bluetooth par jao: AUTH,123456# bhej kar unlock karo.
2. Naya command bhejo: CONFIG#
3. Device Normal mode band kar dega aur Ajeevi_Setup_XXXX naam ka Wi-Fi hotspot bana lega.
4. Apne Phone ya Laptop se us Wi-Fi par jodo. (Password: 12345678)
5. Google Chrome me jao aur address bar me likho: 192.168.4.1
6. Login prompt aayega -> Username: admin, Password: aapka current BT/AUTH password.
7. Ek beautiful HTML Setup page khulega. Apna Data dalo aur "Save & Restart" par click karo.
8. Device automatically save karke normal operation me restart ho jayega!

*/

// ==========================================================================
// ==========================================================================

#include <Arduino.h>
#include <WiFi.h>
#include <SPI.h>
#include <Ethernet.h>
#include <WebServer.h>
#include "BluetoothSerial.h"
#include <Wire.h> // I2C Native Support
#include <Preferences.h>
#include <time.h>
#include <string.h>
#include <sys/time.h>
#include "esp_system.h"
#if __has_include("esp_mac.h")
#include "esp_mac.h" // Arduino-ESP32 3.x: esp_read_mac() / ESP_MAC_ETH yahan hai
#endif
#include "freertos/FreeRTOS.h" // FIX: semphr.h se pehle include karna zaroori hai,
                                // warna xSemaphoreCreateRecursiveMutex() jaise
                                // recursive-mutex macros define hi nahi hote
                                // (compile error: 'was not declared in this scope').
#include "freertos/semphr.h"
#include "freertos/task.h"

// --------------------------------------------------------------------------
// 1. PIN DEFINITIONS & TUNABLES
// --------------------------------------------------------------------------
#define AM2301B_ADDR 0x38 // I2C Address for AM2301B

#define W5500_MOSI 23
#define W5500_MISO 19
#define W5500_SCLK 18
#define W5500_CS 5
#define W5500_RST 25

#define LED_D3 14
#define LED_D4 12
#define WDT_DONE_PIN 33 // Connected to TPL5010 DONE (TP1)

#define AVG_SAMPLES 5 // 5 samples * 2 sec = 10 sec average

#define SENSOR_PERIOD_MS 2000UL      // har 2 sec me ek reading (V17.6 jaisa hi)
#define SENSOR_CONV_MS 80UL          // AM2301B measurement conversion time
#define SENSOR_INIT_WAIT_MS 20UL     // 0xBE init ke baad settle time
#define AUTH_SESSION_MS 300000UL     // 5 min BT auth session
#define AUTH_MAX_FAILS 5
#define WEB_AUTH_MAX_FAILS 8
#define WEB_AUTH_LOCK_MS 30000UL
#define LOOP_STALL_LIMIT_MS 15000UL  // Core1 itni der chup rahe to Core0 WDT feed band

float t_arr[AVG_SAMPLES] = {0};
float h_arr[AVG_SAMPLES] = {0};
int sample_idx = 0;
bool buffer_full = false;

// --------------------------------------------------------------------------
// 2. GLOBAL VARIABLES
// --------------------------------------------------------------------------
BluetoothSerial SerialBT;
Preferences preferences;
WebServer webServer(80);

WiFiClient wifiClient;
EthernetClient ethClient;
Client *tcpClient = &wifiClient;

bool nvsReady = false;
volatile bool isConfigMode = false;
volatile unsigned long configModeEnteredAt = 0;
const unsigned long CONFIG_MODE_TIMEOUT_MS = 600000UL; // 10 min timeout

char wifi_ssid[33] = {0};
char wifi_pass[64] = {0};

bool use_dhcp = true;
char lan_ip[16] = "192.168.1.100";
char lan_sn[16] = "255.255.255.0";
char lan_gw[16] = "192.168.1.1";
char lan_dns[16] = "8.8.8.8";

char server_ip[16] = {0};
int server_port = 0;
int data_freq = 60;

volatile int comm_mode = 2;
volatile int active_interface = 2;

uint8_t eth_mac[6];
char g_macStr[13] = "000000000000";
char g_macTail[5] = "0000"; // MAC ke aakhiri 4 chars (AP / BT naam ke liye)

float currentTemp = 0.0;
float currentHum = 0.0;
bool sensorValid = false;
uint8_t sensorFailCount = 0;
uint8_t sensorGoodCount = 0;
bool isContinuousLogActive = false;
unsigned long lastContinuousLogTime = 0;

char bt_pass[32] = {0};
bool btAuthenticated = false;
unsigned long lastAuthTime = 0;
uint8_t authFailedAttempts = 0;
uint8_t authLockoutRounds = 0;
unsigned long authLockoutTime = 0;

char tcpRxBuffer[257];
int tcpRxIndex = 0;
bool tcpRxOverflow = false;
unsigned long lastTcpRxActivity = 0;
char tcpLastChar = 0; // [RACE-4] pehle handleTcpIncoming() ke andar static tha

char btRxBuffer[129];
int btRxIndex = 0;
bool btRxOverflow = false;

// [OPT-5] Core1 heartbeat - Core0 isse dekh kar decide karta hai ki external
// watchdog ko feed karna safe hai ya nahi.
volatile unsigned long g_loopHeartbeat = 0;

enum ConnState
{
    NET_DISCONNECTED,
    NET_CONNECTING,
    NET_CONNECTED
};
ConnState netState = NET_DISCONNECTED;
unsigned long connectStartedAt = 0;
const unsigned long CONNECT_TIMEOUT_MS = 2000;

struct TcpState
{
    unsigned long lastDataSendTime = 0;
    uint32_t packetSerialNum = 0;
    bool isTimeSynced = false;
    unsigned long lastTimeReqSent = 0;
    bool wasConnected = false;
    unsigned long lastConnTryTime = 0;
};
TcpState tcpState;

struct TcpAckState
{
    char lastSentPacket[256] = {0};
    size_t lastSentLen = 0; // [OPT-4] baar-baar strlen() na karna pade
    bool isWaitingForAck = false;
    unsigned long packetSentAt = 0;
};
TcpAckState ackState;
int retryCount = 0;
unsigned long ACK_TIMEOUT_MS = 30000;

struct AlertConfig
{
    float threshold = 0.0f;
    bool enabled = false;
};
AlertConfig tempAlert;
AlertConfig humAlert;

// --------------------------------------------------------------------------
// 2b. DUAL-CORE SAFETY
// --------------------------------------------------------------------------
// BT command handling + the web config portal run on Core 0 (see commTask in
// section 10), while sensor read / TCP protocol / failover stay on Core 1
// (the normal Arduino loop task). Both sides touch the same globals
// (tcpClient, wifi_ssid/wifi_pass, server_ip/port, WiFi/Ethernet mode,
// tempAlert/humAlert, comm_mode, use_dhcp, NVS) so every place that mutates or
// acts on that shared state takes this recursive mutex first. NetLockGuard
// takes the lock in its constructor and always releases it when the enclosing
// scope ends (covers every early "return" automatically, no manual unlock).
//
// LOCK ORDER (deadlock se bachne ke liye):
//   netMutex  -> logMutex   (allowed: btLog() lock ke andar se call hota hai)
//   logMutex  -> netMutex   (NEVER: btLog() kabhi netMutex nahi leta)
// logMutex isliye ek "leaf" lock hai.
SemaphoreHandle_t netMutex = NULL;
SemaphoreHandle_t logMutex = NULL;

struct NetLockGuard
{
    // [RACE-3] agar mutex create hi na ho paaya ho to crash mat karo.
    bool held;
    NetLockGuard() : held(false)
    {
        if (netMutex != NULL)
            held = (xSemaphoreTakeRecursive(netMutex, portMAX_DELAY) == pdTRUE);
    }
    ~NetLockGuard()
    {
        if (held)
            xSemaphoreGiveRecursive(netMutex);
    }
};

struct LogLockGuard
{
    bool held;
    LogLockGuard() : held(false)
    {
        if (logMutex != NULL)
            held = (xSemaphoreTakeRecursive(logMutex, portMAX_DELAY) == pdTRUE);
    }
    ~LogLockGuard()
    {
        if (held)
            xSemaphoreGiveRecursive(logMutex);
    }
};

// Lightweight spinlock just for feedWatchdog()'s internal timestamp, which is
// called extremely frequently from BOTH cores. Using the heavier recursive
// netMutex here would be overkill (and could momentarily block on unrelated
// network work); a portMUX critical section is the right tool for a tiny,
// bounded, non-blocking check-and-set. [RACE FIX V17.6]
static portMUX_TYPE wdtMux = portMUX_INITIALIZER_UNLOCKED;

// --------------------------------------------------------------------------
// 3. FORWARD DECLARATIONS
// --------------------------------------------------------------------------
void btLog(const char *msg);
void safeSaveString(const char *key, const char *val);
void safeSaveInt(const char *key, int val);
void safeSaveFloat(const char *key, float val);
void safeSaveUChar(const char *key, uint8_t val);
bool isValidIP(const char *ip);
void feedWatchdog();
void initEthernet();
void activateInterface(int mode);
void resetNetworkRetryState();

// --------------------------------------------------------------------------
// 4. LOGGING / NVS / SMALL HELPERS
// --------------------------------------------------------------------------
// [SEC-1] btLog() ab serialized hai. Core0 (BT parser + web portal) aur Core1
// (main loop ka live-log) dono isko call karte hain; pehle bina lock ke dono
// SerialBT par likhte the -> lines aapas me mix ho jaati thi aur
// BluetoothSerial ke internal TX buffer par bhi race tha.
void btLog(const char *msg)
{
    if (msg == NULL)
        return;
    LogLockGuard _log;
    Serial.println(msg);
    if (SerialBT.hasClient())
    {
        SerialBT.print(msg);
        SerialBT.print("\r\n");
    }
}

// [SEC-2] NVS access ab hamesha netMutex ke andar. Preferences/NVS handle
// thread-safe nahi hai; pehle PASS,# (Core0) aur parseTcpMessage() ka
// "p_seq" write (Core1) ek saath chal sakte the.
void safeSaveString(const char *key, const char *val)
{
    if (!nvsReady || key == NULL || val == NULL)
        return;
    NetLockGuard _lock;
    String old = preferences.getString(key, "");
    if (!old.equals(val))
        preferences.putString(key, val);
}

void safeSaveInt(const char *key, int val)
{
    if (!nvsReady || key == NULL)
        return;
    NetLockGuard _lock;
    if (preferences.getInt(key, -1) != val)
        preferences.putInt(key, val);
}

void safeSaveFloat(const char *key, float val)
{
    if (!nvsReady || key == NULL)
        return;
    NetLockGuard _lock;
    if (preferences.getFloat(key, NAN) != val)
        preferences.putFloat(key, val);
}

void safeSaveUChar(const char *key, uint8_t val)
{
    if (!nvsReady || key == NULL)
        return;
    NetLockGuard _lock;
    if (preferences.getUChar(key, 0xFF) != val)
        preferences.putUChar(key, val);
}

// strncpy ke saath hamesha explicit null-termination. [BUG-4]
static void copyStr(char *dst, size_t dstSize, const char *src)
{
    if (dst == NULL || dstSize == 0)
        return;
    if (src == NULL)
    {
        dst[0] = '\0';
        return;
    }
    strncpy(dst, src, dstSize - 1);
    dst[dstSize - 1] = '\0';
}

// [SEC-4] Constant-time compare - BT/serial par password guess karte waqt
// response-time se prefix leak nahi hoga.
static bool constTimeEquals(const char *a, const char *b, size_t maxLen)
{
    if (a == NULL || b == NULL)
        return false;
    size_t la = strnlen(a, maxLen);
    size_t lb = strnlen(b, maxLen);
    uint8_t diff = (uint8_t)((la ^ lb) & 0xFF);
    diff |= (uint8_t)(((la ^ lb) >> 8) & 0xFF);
    for (size_t i = 0; i < maxLen; i++)
    {
        uint8_t ca = (i < la) ? (uint8_t)a[i] : 0;
        uint8_t cb = (i < lb) ? (uint8_t)b[i] : 0;
        diff |= (uint8_t)(ca ^ cb);
    }
    return diff == 0;
}

// [SEC-9] Strict dotted-quad parser.
// Purana version sscanf("%d.%d.%d.%d%c") use karta tha, jo:
//   - leading whitespace accept karta tha ("  1.2.3.4")
//   - "+1.-2.3.4" jaise signed tokens accept karta tha
//   - bahut bade numbers par signed-int overflow (undefined behaviour) deta tha
bool isValidIP(const char *ip)
{
    if (ip == NULL || ip[0] == '\0')
        return false;
    int octets = 0;
    const char *p = ip;
    while (1)
    {
        if (*p < '0' || *p > '9')
            return false;
        uint32_t val = 0;
        int digits = 0;
        while (*p >= '0' && *p <= '9')
        {
            val = val * 10u + (uint32_t)(*p - '0');
            digits++;
            if (digits > 3 || val > 255u)
                return false;
            p++;
        }
        octets++;
        if (*p == '.')
        {
            if (octets == 4)
                return false;
            p++;
            continue;
        }
        if (*p == '\0')
            return (octets == 4);
        return false;
    }
}

// Critical for I2C AM2301B Data Validation
uint8_t crc8_aht(const uint8_t *data, uint8_t len)
{
    uint8_t crc = 0xFF;
    for (uint8_t i = 0; i < len; i++)
    {
        crc ^= data[i];
        for (uint8_t b = 0; b < 8; b++)
        {
            crc = (crc & 0x80) ? (uint8_t)((crc << 1) ^ 0x31) : (uint8_t)(crc << 1);
        }
    }
    return crc;
}

void feedWatchdog()
{
    // [RACE FIX V17.6] "lastWdtFeed" pehle bina kisi protection ke dono cores se
    // (activateInterface()/initEthernet() ka Core0 BT/web command path, aur Core1
    // ka main loop()) check-then-set ho raha tha. Ab sirf timestamp check/update
    // ek chhoti si critical section me hoti hai (bounded, non-blocking spinlock),
    // GPIO toggle timing pehle jaisi hi rehti hai.
    static unsigned long lastWdtFeed = 0;
    bool shouldFeed;

    portENTER_CRITICAL(&wdtMux);
    shouldFeed = (millis() - lastWdtFeed > 1000);
    if (shouldFeed)
        lastWdtFeed = millis();
    portEXIT_CRITICAL(&wdtMux);

    if (shouldFeed)
    {
        digitalWrite(WDT_DONE_PIN, HIGH);
        delayMicroseconds(50);
        digitalWrite(WDT_DONE_PIN, LOW);
    }
}

void handleLEDs()
{
    static int8_t lastD3 = -1;
    static int8_t lastD4 = -1;

    bool wifiConnected =
        (active_interface == 2 && WiFi.status() == WL_CONNECTED);

    bool lanConnected =
        (active_interface == 1 && Ethernet.linkStatus() == LinkON);

    unsigned long currentMillis = millis();

    int d3 = LOW;
    int d4 = LOW;

    // =========================================================
    // 1. CONFIGURATION MODE
    // D3 and D4 alternate blink
    // =========================================================
    if (isConfigMode)
    {
        bool blink = (currentMillis % 1000) < 500;

        d3 = blink ? HIGH : LOW;
        d4 = blink ? LOW : HIGH;
    }

    // =========================================================
    // 2. WIFI CONNECTED
    // D3 = STABLE ON
    // D4 = BLINK
    // =========================================================
    else if (wifiConnected)
    {
        d3 = HIGH;

        bool blink = (currentMillis % 1000) < 500;
        d4 = blink ? HIGH : LOW;
    }

    // =========================================================
    // 3. LAN CONNECTED
    // D4 = STABLE ON
    // D3 = BLINK
    // =========================================================
    else if (lanConnected)
    {
        d4 = HIGH;

        bool blink = (currentMillis % 1000) < 500;
        d3 = blink ? HIGH : LOW;
    }

    // =========================================================
    // 4. NO CONNECTION / ERROR
    // Both LEDs blink together
    // =========================================================
    else
    {
        bool errorBlink = (currentMillis % 400) < 200;

        d3 = errorBlink ? HIGH : LOW;
        d4 = errorBlink ? HIGH : LOW;
    }

    // =========================================================
    // Write only when state actually changes
    // =========================================================
    if (d3 != lastD3)
    {
        digitalWrite(LED_D3, d3);
        lastD3 = (int8_t)d3;
    }

    if (d4 != lastD4)
    {
        digitalWrite(LED_D4, d4);
        lastD4 = (int8_t)d4;
    }
}


void checkDailyRestart()
{
    static const unsigned long RESTART_INTERVAL = 86400000UL;
    // [BUG-5] Config Mode ke beech me user ka setup mat kaato. Config Mode ka
    // apna 10-min timeout hai jo waise bhi restart kar deta hai.
    if (isConfigMode)
        return;
    if (millis() > RESTART_INTERVAL)
    {
        btLog("[SYS] 24-Hour Uptime Reached. Auto-Restarting...");
        delay(1000);
        esp_restart();
    }
}

void resetNetworkRetryState()
{
    netState = NET_DISCONNECTED;
    connectStartedAt = 0;
    tcpState.lastConnTryTime = 0;
    tcpState.wasConnected = false;
    ackState.isWaitingForAck = false;
    retryCount = 0;
    tcpRxIndex = 0;
    tcpRxOverflow = false;
    tcpLastChar = 0; // [RACE-4] parser ka stale byte bhi clear karo
    lastTcpRxActivity = millis();
}

// --------------------------------------------------------------------------
// 5. WEB SERVER FSM & HTML
// --------------------------------------------------------------------------
const char HTML_TEMPLATE[] PROGMEM = R"=====(
<!DOCTYPE html><html><head><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Ajeevi Sensor Configuration</title>
<style>
body {font-family: Arial, sans-serif; background: #eef2f3; padding: 20px; display: flex; justify-content: center;}
.box {background: #fff; padding: 25px; border-radius: 8px; box-shadow: 0 4px 10px rgba(0,0,0,0.1); width: 100%%; max-width: 450px;}
h2 {text-align: center; color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px;}
label {font-weight: bold; margin-top: 15px; display: block; color: #34495e; font-size: 14px;}
input, select {width: 100%%; padding: 10px; margin-top: 5px; border: 1px solid #bdc3c7; border-radius: 4px; box-sizing: border-box; font-size: 14px;}
.btn {width: 100%%; padding: 12px; background: #3498db; color: #fff; border: none; border-radius: 4px; margin-top: 25px; cursor: pointer; font-size: 16px; font-weight: bold;}
.btn:hover {background: #2980b9;}
.footer {text-align: center; margin-top: 20px; font-size: 12px; color: #7f8c8d;}
.section-title {background: #ecf0f1; padding: 8px; margin-top: 20px; border-radius: 4px; text-align: center; color: #2980b9; font-weight: bold;}
</style></head><body>
<div class="box"><h2>Ajeevi T&amp;H Sensor Setup</h2>
<form action="/save" method="POST">
<div class="section-title">Network &amp; Server</div>
<label>Primary Network Mode</label>
<select name="c_mode"><option value="2" %s>Wi-Fi</option><option value="1" %s>LAN (Ethernet)</option></select>
<label>Wi-Fi SSID</label><input type="text" name="w_ssid" maxlength="32" value="%s">
<label>Wi-Fi Password</label><input type="password" name="w_pass" maxlength="63" value="%s">
<label>LAN IPv4 Mode</label>
<select name="l_dhcp"><option value="1" %s>DHCP (Auto)</option><option value="0" %s>Static IP</option></select>
<label>LAN Static IP</label><input type="text" name="l_ip" maxlength="15" value="%s">
<label>LAN Subnet Mask</label><input type="text" name="l_sn" maxlength="15" value="%s">
<label>LAN Gateway</label><input type="text" name="l_gw" maxlength="15" value="%s">
<label>LAN DNS</label><input type="text" name="l_dns" maxlength="15" value="%s">
<label>Server IP (leave empty = server disabled)</label><input type="text" name="s_ip" maxlength="15" value="%s">
<label>Server Port</label><input type="number" name="s_port" min="0" max="65535" value="%d">
<label>Data Frequency (Seconds)</label><input type="number" name="d_freq" min="15" max="3600" value="%d">

<div class="section-title">Alerts &amp; Security</div>
<label>Temp Alert (&deg;C)</label>
<select name="tmp_en"><option value="1" %s>Enabled</option><option value="0" %s>Disabled</option></select>
<input type="number" step="0.1" min="-50" max="150" name="tmp_thr" value="%.1f" placeholder="Threshold e.g. 35.5">

<label>Humidity Alert (%%)</label>
<select name="hum_en"><option value="1" %s>Enabled</option><option value="0" %s>Disabled</option></select>
<input type="number" step="0.1" min="0" max="100" name="hum_thr" value="%.1f" placeholder="Threshold e.g. 80.0">

<label>Bluetooth Password</label><input type="password" name="bt_pass" maxlength="31" value="%s">

<button type="submit" class="btn">Save &amp; Restart</button>
</form>
<div class="footer">Ajeevi Industrial Gateway V17.7</div>
</div></body></html>
)=====";

// [OPT-3] Static pages ab PROGMEM me hain aur send_P() se jaate hain -
// pehle har request par ~700 byte ki Arduino String heap me banti thi.
const char PAGE_SAVED[] PROGMEM =
    "<!DOCTYPE html><html><head><meta name='viewport' content='width=device-width, initial-scale=1'>"
    "<style>body{font-family:Arial;text-align:center;padding:50px;background:#eef2f3;}"
    ".box{background:#fff;padding:30px;border-radius:8px;box-shadow:0 4px 10px rgba(0,0,0,0.1);display:inline-block;}</style>"
    "</head><body><div class='box'><h2 style='color:#2ecc71;'>Settings Saved Successfully!</h2>"
    "<p>Device is restarting. Please reconnect to your normal Wi-Fi network.</p></div></body></html>";

const char PAGE_ERR_FMT[] PROGMEM =
    "<!DOCTYPE html><html><head><meta name='viewport' content='width=device-width, initial-scale=1'>"
    "<style>body{font-family:Arial;text-align:center;padding:50px;background:#eef2f3;}"
    ".box{background:#fff;padding:30px;border-radius:8px;box-shadow:0 4px 10px rgba(0,0,0,0.1);display:inline-block;max-width:420px;}</style>"
    "</head><body><div class='box'><h2 style='color:#e74c3c;'>Invalid Settings</h2><p>%s</p>"
    "<p><a href='/'>&laquo; Go back and fix it</a></p></div></body></html>";

const char PAGE_TOO_MANY[] PROGMEM =
    "<!DOCTYPE html><html><body style='font-family:Arial;text-align:center;padding:50px;'>"
    "<h3>Too many failed logins. Please wait 30 seconds.</h3></body></html>";

void htmlEscape(const char *src, char *dst, size_t dstSize)
{
    if (dst == NULL || dstSize == 0)
        return;
    if (src == NULL)
    {
        dst[0] = '\0';
        return;
    }
    size_t o = 0;
    for (size_t i = 0; src[i] != '\0' && o < dstSize - 1; i++)
    {
        const char *rep = NULL;
        switch (src[i])
        {
        case '&':
            rep = "&amp;";
            break;
        case '<':
            rep = "&lt;";
            break;
        case '>':
            rep = "&gt;";
            break;
        case '"':
            rep = "&quot;";
            break;
        case '\'':
            rep = "&#39;";
            break;
        default:
            break;
        }
        if (rep)
        {
            size_t rlen = strlen(rep);
            if (o + rlen >= dstSize - 1)
                break;
            memcpy(dst + o, rep, rlen);
            o += rlen;
        }
        else
        {
            dst[o++] = src[i];
        }
    }
    dst[o] = '\0';
}

// Config portal itself has no gate once the AP is up (AP password is a fixed,
// published default). This closes that hole: anyone joining the AP still needs
// the device's BT/control password to view or change settings.
// [SEC-5] Ab brute-force backoff bhi hai: 8 galat login ke baad 30s block.
bool checkWebAuth()
{
    static uint8_t webAuthFails = 0;
    static unsigned long webAuthLockUntil = 0;

    if (webAuthFails >= WEB_AUTH_MAX_FAILS)
    {
        // signed difference -> millis() rollover-safe
        if ((int32_t)(millis() - webAuthLockUntil) < 0)
        {
            webServer.send_P(429, "text/html", PAGE_TOO_MANY);
            return false;
        }
        webAuthFails = 0; // lock window khatam
    }

    if (!webServer.authenticate("admin", bt_pass))
    {
        if (webAuthFails < 255)
            webAuthFails++;
        if (webAuthFails >= WEB_AUTH_MAX_FAILS)
            webAuthLockUntil = millis() + WEB_AUTH_LOCK_MS;
        webServer.requestAuthentication();
        return false;
    }
    webAuthFails = 0;
    return true;
}

void handleRoot()
{
    if (!checkWebAuth())
        return;

    // Worst case escaping = 6 bytes per source char (&quot;)
    char e_ssid[33 * 6 + 1], e_pass[64 * 6 + 1];
    char e_lan_ip[16 * 6 + 1], e_lan_sn[16 * 6 + 1], e_lan_gw[16 * 6 + 1], e_lan_dns[16 * 6 + 1];
    char e_server_ip[16 * 6 + 1], e_bt_pass[32 * 6 + 1];

    int l_comm, l_port, l_freq;
    bool l_dhcp, l_tEn, l_hEn;
    float l_tThr, l_hThr;

    // Shared state ka ek consistent snapshot lo, phir lock chhod do -
    // taaki page render/TX ke dauraan Core1 block na ho. [RACE-1]
    {
        NetLockGuard _lock;
        htmlEscape(wifi_ssid, e_ssid, sizeof(e_ssid));
        htmlEscape(wifi_pass, e_pass, sizeof(e_pass));
        htmlEscape(lan_ip, e_lan_ip, sizeof(e_lan_ip));
        htmlEscape(lan_sn, e_lan_sn, sizeof(e_lan_sn));
        htmlEscape(lan_gw, e_lan_gw, sizeof(e_lan_gw));
        htmlEscape(lan_dns, e_lan_dns, sizeof(e_lan_dns));
        htmlEscape(server_ip, e_server_ip, sizeof(e_server_ip));
        htmlEscape(bt_pass, e_bt_pass, sizeof(e_bt_pass));
        l_comm = comm_mode;
        l_dhcp = use_dhcp;
        l_port = server_port;
        l_freq = data_freq;
        l_tEn = tempAlert.enabled;
        l_tThr = tempAlert.threshold;
        l_hEn = humAlert.enabled;
        l_hThr = humAlert.threshold;
    }

    const size_t bufSize = 6144;
    char *htmlBuf = (char *)malloc(bufSize);
    if (!htmlBuf)
    {
        webServer.send(500, "text/plain", "Memory Error");
        return;
    }

    int n = snprintf(htmlBuf, bufSize, HTML_TEMPLATE,
                     (l_comm == 2) ? "selected" : "", (l_comm == 1) ? "selected" : "",
                     e_ssid, e_pass,
                     l_dhcp ? "selected" : "", !l_dhcp ? "selected" : "",
                     e_lan_ip, e_lan_sn, e_lan_gw, e_lan_dns,
                     e_server_ip, l_port, l_freq,
                     l_tEn ? "selected" : "", !l_tEn ? "selected" : "", l_tThr,
                     l_hEn ? "selected" : "", !l_hEn ? "selected" : "", l_hThr,
                     e_bt_pass);

    // [BUG-7] truncation check - pehle nahi tha, aadha HTML chala jata tha.
    if (n < 0 || n >= (int)bufSize)
    {
        free(htmlBuf);
        webServer.send(500, "text/plain", "Page render error");
        return;
    }

    // [OPT-2] setContentLength + sendContent => WebServer andar ek aur 6KB
    // String copy nahi banata. Peak RAM ~16KB se ~6KB.
    webServer.setContentLength((size_t)n);
    webServer.send(200, "text/html", "");
    webServer.sendContent(htmlBuf, (size_t)n);
    free(htmlBuf);
}

void sendConfigError(const char *msg)
{
    char esc[256];
    htmlEscape(msg ? msg : "Unknown error", esc, sizeof(esc));
    char page[900];
    int n = snprintf_P(page, sizeof(page), PAGE_ERR_FMT, esc);
    if (n < 0)
        n = 0;
    webServer.send(400, "text/html", page);
}

void handleSave()
{
    if (!checkWebAuth())
        return;

    char errors[256];
    errors[0] = '\0';
    size_t eLen = 0;
    // chhota helper macro: error text ko bina String ke append karo
#define ADD_ERR(txt)                                                     \
    do                                                                   \
    {                                                                    \
        size_t _l = strlen(txt);                                         \
        if (eLen + _l < sizeof(errors) - 1)                              \
        {                                                                \
            memcpy(errors + eLen, txt, _l);                              \
            eLen += _l;                                                  \
            errors[eLen] = '\0';                                         \
        }                                                                \
    } while (0)

    int c_mode = webServer.hasArg("c_mode") ? (int)webServer.arg("c_mode").toInt() : comm_mode;
    // [SEC-8] pehle koi bhi c_mode NVS me chala jata tha
    if (c_mode != 1 && c_mode != 2)
        ADD_ERR("Network mode must be Wi-Fi or LAN. ");

    String w_ssid = webServer.arg("w_ssid");
    String w_pass = webServer.arg("w_pass");
    if (w_ssid.length() > 32)
        ADD_ERR("Wi-Fi SSID too long. ");
    if (w_pass.length() > 63)
        ADD_ERR("Wi-Fi password too long. ");

    int l_dhcp = webServer.hasArg("l_dhcp") ? (int)webServer.arg("l_dhcp").toInt() : (use_dhcp ? 1 : 0);
    if (l_dhcp != 0 && l_dhcp != 1)
        ADD_ERR("LAN IPv4 mode invalid. ");

    String l_ip = webServer.arg("l_ip"), l_sn = webServer.arg("l_sn"), l_gw = webServer.arg("l_gw"), l_dns = webServer.arg("l_dns");
    if (l_dhcp == 0)
    {
        if (!isValidIP(l_ip.c_str()) || !isValidIP(l_sn.c_str()) || !isValidIP(l_gw.c_str()) || !isValidIP(l_dns.c_str()))
            ADD_ERR("LAN Static IP config is invalid. ");
    }

    // [BUG-6] Server IP khali = "server disabled" (boot default jaisa).
    // Pehle form hamesha s_port bhejta tha isliye khali IP hamesha
    // "Server IP is invalid" de deta tha - server ko off karna namumkin tha.
    String s_ip = webServer.arg("s_ip");
    s_ip.trim();
    long s_port = webServer.hasArg("s_port") ? webServer.arg("s_port").toInt() : server_port;
    bool serverEnabled = (s_ip.length() > 0);
    if (serverEnabled)
    {
        if (!isValidIP(s_ip.c_str()))
            ADD_ERR("Server IP is invalid. ");
        if (s_port < 1 || s_port > 65535)
            ADD_ERR("Server port must be 1-65535. ");
    }

    long d_freq = webServer.hasArg("d_freq") ? webServer.arg("d_freq").toInt() : data_freq;
    if (d_freq < 15 || d_freq > 3600)
        ADD_ERR("Data frequency must be 15-3600. ");

    int t_en = webServer.hasArg("tmp_en") ? (int)webServer.arg("tmp_en").toInt() : (tempAlert.enabled ? 1 : 0);
    float t_thr = webServer.hasArg("tmp_thr") ? webServer.arg("tmp_thr").toFloat() : tempAlert.threshold;
    if (t_en != 0 && t_en != 1)
        ADD_ERR("Temp alert flag invalid. ");
    if (isnan(t_thr) || t_thr < -50.0f || t_thr > 150.0f)
        ADD_ERR("Temp threshold must be -50 to 150. ");

    int h_en = webServer.hasArg("hum_en") ? (int)webServer.arg("hum_en").toInt() : (humAlert.enabled ? 1 : 0);
    float h_thr = webServer.hasArg("hum_thr") ? webServer.arg("hum_thr").toFloat() : humAlert.threshold;
    if (h_en != 0 && h_en != 1)
        ADD_ERR("Humidity alert flag invalid. ");
    if (isnan(h_thr) || h_thr < 0.0f || h_thr > 100.0f)
        ADD_ERR("Humidity threshold must be 0 to 100. ");

    String b_pass = webServer.arg("bt_pass");
    if (b_pass.length() < 1 || b_pass.length() > 31)
        ADD_ERR("BT Password must be 1-31 chars. ");

    if (eLen > 0)
    {
        sendConfigError(errors);
        return;
    }
#undef ADD_ERR

    // Saara persist ek hi lock ke andar -> NVS write atomic block. [SEC-2]
    {
        NetLockGuard _lock;

        safeSaveInt("c_mode", c_mode);
        safeSaveString("w_ssid", w_ssid.c_str());
        safeSaveString("w_pass", w_pass.c_str());
        safeSaveInt("l_dhcp", l_dhcp);
        if (l_dhcp == 0)
        {
            safeSaveString("l_ip", l_ip.c_str());
            safeSaveString("l_sn", l_sn.c_str());
            safeSaveString("l_gw", l_gw.c_str());
            safeSaveString("l_dns", l_dns.c_str());
        }

        if (serverEnabled)
        {
            safeSaveString("s_ip", s_ip.c_str());
            safeSaveInt("s_port", (int)s_port);
        }
        else
        {
            safeSaveString("s_ip", "");
            safeSaveInt("s_port", 0);
        }
        safeSaveInt("d_freq", (int)d_freq);

        tempAlert.enabled = (t_en == 1);
        tempAlert.threshold = t_thr;
        safeSaveUChar("tmp_en", (uint8_t)t_en);
        safeSaveFloat("tmp_thr", t_thr);

        humAlert.enabled = (h_en == 1);
        humAlert.threshold = h_thr;
        safeSaveUChar("hum_en", (uint8_t)h_en);
        safeSaveFloat("hum_thr", h_thr);

        copyStr(bt_pass, sizeof(bt_pass), b_pass.c_str());
        safeSaveString("bt_pass", bt_pass);
    }

    webServer.send_P(200, "text/html", PAGE_SAVED);
    // Response ko wire par jaane ka mauka do, phir hi restart karo.
    delay(1500);
    webServer.client().stop();
    delay(200);
    esp_restart();
}

void startWebConfigMode()
{
    // [SEC-6] CONFIG# dobara aane par handlers dobara register ho jaate the
    // (webServer.on() har call par ek naya RequestHandler alloc karta hai)
    // aur webServer.begin() dubara chalta tha -> leak + duplicate routes.
    if (isConfigMode)
    {
        btLog("[SYS] Config Mode already active. Open http://192.168.4.1");
        return;
    }

    isConfigMode = true;
    configModeEnteredAt = millis();

    char apName[32];
    snprintf(apName, sizeof(apName), "Ajeevi_Setup_%s", g_macTail);

    {
        NetLockGuard _lock;
        wifiClient.stop();
        ethClient.stop();
        WiFi.disconnect(true);
        WiFi.mode(WIFI_AP);
        // [SEC-7] max_connection = 1 -> setup ke dauraan sirf ek client
        WiFi.softAP(apName, "12345678", 1 /*channel*/, 0 /*hidden*/, 1 /*max_conn*/);
    }

    webServer.on("/", handleRoot);
    webServer.on("/save", HTTP_POST, handleSave);
    webServer.begin();

    btLog("[SYS] WEB CONFIG MODE ACTIVE!");
    btLog("[SYS] Connect Wi-Fi to:");
    btLog(apName);
    btLog("[SYS] Password: 12345678");
    btLog("[SYS] Open Chrome: http://192.168.4.1");
    btLog("[SYS] Login -> user: admin / pass: <your AUTH password>");
}

// --------------------------------------------------------------------------
// 6. INTERFACE / FAILOVER LOGIC
// --------------------------------------------------------------------------
// [OPT-1] Yahan pehle Arduino String concatenation hoti thi. Ye function LAN
// retry path se har 10 second par chal sakta hai, isliye 24x7 device par ye
// heap fragmentation ka seedha source tha. Ab fixed buffer + snprintf.
void initEthernet()
{
    NetLockGuard _lock;
    btLog("[ETH] Initializing Ethernet Hardware...");
    feedWatchdog();
    if (use_dhcp)
    {
        btLog("[ETH] Trying to get IP via DHCP...");
        Ethernet.begin(eth_mac, 2000, 1000);
    }
    else
    {
        btLog("[ETH] Applying Static IP Configuration...");
        IPAddress ip, sn, gw, dns;
        ip.fromString(lan_ip);
        sn.fromString(lan_sn);
        gw.fromString(lan_gw);
        dns.fromString(lan_dns);
        Ethernet.begin(eth_mac, ip, dns, gw, sn);
    }

    if (Ethernet.linkStatus() == LinkON)
    {
        IPAddress lip = Ethernet.localIP();
        char msg[64];
        snprintf(msg, sizeof(msg), "[ETH] Connected! LAN IP: %u.%u.%u.%u",
                 (unsigned)lip[0], (unsigned)lip[1], (unsigned)lip[2], (unsigned)lip[3]);
        btLog(msg);
    }
    else
    {
        btLog("[ETH_ERR] Cable Not Connected or Link Down.");
    }
    feedWatchdog();
}

void activateInterface(int mode)
{
    if (isConfigMode)
        return;
    NetLockGuard _lock;
    active_interface = mode;
    wifiClient.stop();
    ethClient.stop();
    resetNetworkRetryState();

    if (active_interface == 2)
    {
        tcpClient = &wifiClient;
        // [BUG FIX V17.6] Pehle condition "wifi_ssid[0] != '\0' && WiFi.getMode() != WIFI_STA"
        // ek hi if/else me thi, isliye jab SSID configured hota tha LEKIN WiFi already
        // STA mode me hota tha (e.g. LAN->WiFi failover revert ke case me), tab bhi
        // galat se "[WIFI_ERR] No SSID configured." print ho jata tha - jabki asal
        // wajah sirf itni thi ki dobara WiFi.begin() karne ki zaroorat nahi thi.
        // Ab dono cases alag-alag, sahi message ke saath handle ho rahe hain.
        if (wifi_ssid[0] != '\0')
        {
            if (WiFi.getMode() != WIFI_STA)
            {
                char msg[64];
                btLog("[WIFI] Initializing Wi-Fi Connection...");
                snprintf(msg, sizeof(msg), "[WIFI] Connecting to SSID: %s", wifi_ssid);
                btLog(msg);
                WiFi.mode(WIFI_STA);
                feedWatchdog();
                WiFi.begin(wifi_ssid, wifi_pass);
                feedWatchdog();
            }
            else
            {
                btLog("[WIFI] Already in STA mode, reusing existing connection state.");
            }
        }
        else
        {
            btLog("[WIFI_ERR] No SSID configured.");
        }
        btLog("[SYS] Interface Active: Wi-Fi");
    }
    else
    {
        tcpClient = &ethClient;
        if (comm_mode == 1)
        {
            WiFi.disconnect(true);
            WiFi.mode(WIFI_OFF);
        }
        btLog("[SYS] Interface Active: LAN");
        if (Ethernet.linkStatus() == LinkON)
            initEthernet();
    }
}

void switchCommunicationMode(int mode)
{
    // [RACE FIX V17.6] comm_mode ab NetLockGuard ke andar hi update hota hai.
    // Pehle yeh lock ke bahar set hota tha jabki handleAutoFailover() (Core1)
    // aur activateInterface() ismein comm_mode ko "protected shared state" maan
    // kar padhte hain. Isse ek chhota window ban sakta tha jahan comm_mode naya
    // ho chuka ho par active_interface abhi update na hua ho, aur failover logic
    // ek redundant/overlapping activateInterface() call trigger kar de. Ab poora
    // update ek hi lock ke andar atomic hai, behavior same hai.
    if (mode != 1 && mode != 2)
        return;
    NetLockGuard _lock;
    comm_mode = mode;
    safeSaveInt("c_mode", comm_mode);
    btLog(mode == 2 ? "[CMD] Preferred Mode: Wi-Fi" : "[CMD] Preferred Mode: LAN");
    activateInterface(mode);
}

void handleAutoFailover()
{
    if (isConfigMode)
        return;

    static unsigned long lastWifiConnectedTime = 0;
    static bool failoverInit = false;
    static unsigned long lastFailoverCheck = 0;

    if (!failoverInit)
    {
        lastWifiConnectedTime = millis();
        failoverInit = true;
    }

    if (millis() - lastFailoverCheck < 2000)
        return;
    lastFailoverCheck = millis();

    // [RACE-2] comm_mode / active_interface / wifi_ssid ek hi lock ke andar
    // padhe jaate hain, warna decision aadhe-purane snapshot par ban sakta tha.
    NetLockGuard _lock;

    bool lanLink = (Ethernet.linkStatus() == LinkON);
    bool wifiConfigured = (wifi_ssid[0] != '\0');
    bool wifiConnected = (WiFi.status() == WL_CONNECTED);

    if (wifiConnected)
        lastWifiConnectedTime = millis();

    if (comm_mode == 1)
    {
        if (active_interface == 1 && !lanLink && wifiConfigured)
        {
            btLog("[FAILOVER] LAN Cable Cut! Switching to Wi-Fi Backup...");
            activateInterface(2);
        }
        else if (active_interface == 2 && lanLink)
        {
            btLog("[FAILOVER] LAN Cable Restored! Reverting to Primary (LAN)...");
            activateInterface(1);
        }
    }
    else if (comm_mode == 2)
    {
        if (active_interface == 2)
        {
            if (millis() - lastWifiConnectedTime > 60000UL && lanLink)
            {
                btLog("[FAILOVER] Wi-Fi unreachable for 60s! Switching to LAN Backup...");
                activateInterface(1);
            }
        }
        else if (active_interface == 1)
        {
            if (wifiConnected)
            {
                btLog("[FAILOVER] Wi-Fi Restored! Reverting to Primary (Wi-Fi)...");
                activateInterface(2);
                lastWifiConnectedTime = millis();
            }
            else if (!lanLink)
            {
                btLog("[FAILOVER] LAN Backup Lost! Reverting to Wi-Fi...");
                activateInterface(2);
                lastWifiConnectedTime = millis();
            }
        }
    }
}

// --------------------------------------------------------------------------
// 7. NON-BLOCKING BLUETOOTH COMMAND PARSER
// --------------------------------------------------------------------------
void processBtCommand(char *cmd)
{
    if (cmd == NULL)
        return;

    if (strncmp(cmd, "AUTH,", 5) == 0)
    {
        // [SEC-3] millis() rollover-safe lockout + escalating backoff.
        // Purana code: "if (millis() > authLockoutTime)" - millis() ke 49.7-din
        // rollover ke baad ye turant true ho jata tha aur lockout bypass ho jata
        // tha. Ab signed difference se compare karte hain.
        if (authFailedAttempts >= AUTH_MAX_FAILS)
        {
            if ((int32_t)(millis() - authLockoutTime) >= 0)
            {
                authFailedAttempts = 0; // window khatam, dobara try karne do
            }
            else
            {
                btLog("[AUTH_ERR] Locked out. Please wait.");
                return;
            }
        }

        if (constTimeEquals(cmd + 5, bt_pass, sizeof(bt_pass)))
        {
            btAuthenticated = true;
            authFailedAttempts = 0;
            authLockoutRounds = 0;
            lastAuthTime = millis();
            btLog("[AUTH] SUCCESS. Device Unlocked for 5 mins.");
        }
        else
        {
            authFailedAttempts++;
            btLog("[AUTH] FAILED.");
            if (authFailedAttempts >= AUTH_MAX_FAILS)
            {
                if (authLockoutRounds < 4)
                    authLockoutRounds++;
                // 60s, 120s, 240s, 480s ... har round par double
                unsigned long lockMs = 60000UL << (authLockoutRounds - 1);
                authLockoutTime = millis() + lockMs;
                char msg[64];
                snprintf(msg, sizeof(msg), "[AUTH_ERR] Too many failures. Locked for %lus.", lockMs / 1000UL);
                btLog(msg);
            }
        }
        return;
    }
    else if (strcmp(cmd, "GET") == 0)
    {
        char statusMsg[512];
        NetLockGuard _lock; // snapshot consistent rahe
        const char *actStr = (active_interface == 2) ? "Wi-Fi" : "LAN";
        const char *prefStr = (comm_mode == 2) ? "Wi-Fi" : "LAN";
        const char *ipMode = use_dhcp ? "DHCP" : "STATIC";

        if (btAuthenticated)
        {
            lastAuthTime = millis();
            snprintf(statusMsg, sizeof(statusMsg),
                     "=== System Status ===\r\nMAC: %s\r\nACTIVE: %s (Pref: %s)\r\nLAN MODE: %s\r\nSSID: %s\r\nPASS: %s\r\nSERVER: %s:%d\r\nSYNC: %s\r\nFREQ: %d sec\r\nSENSOR: %s (T:%.1f H:%.1f)\r\nALERT: T=%.1f H=%.1f\r\n",
                     g_macStr, actStr, prefStr, ipMode, wifi_ssid, wifi_pass, server_ip, server_port,
                     tcpState.isTimeSynced ? "YES" : "NO", data_freq, sensorValid ? "OK" : "FAULT", currentTemp, currentHum,
                     tempAlert.enabled ? tempAlert.threshold : 0.0f, humAlert.enabled ? humAlert.threshold : 0.0f);
        }
        else
        {
            snprintf(statusMsg, sizeof(statusMsg),
                     "=== System Status (Public) ===\r\nAUTH: LOCKED\r\nMAC: %s\r\nACTIVE: %s\r\nSYNC: %s\r\nSENSOR: %s\r\n",
                     g_macStr, actStr, tcpState.isTimeSynced ? "YES" : "NO", sensorValid ? "OK" : "FAULT");
        }
        btLog(statusMsg);
        return;
    }

    if (!btAuthenticated)
    {
        btLog("[ERR] Send AUTH,password# first.");
        return;
    }
    lastAuthTime = millis();

    if (strcmp(cmd, "CONFIG") == 0)
        startWebConfigMode();
    else if (strcmp(cmd, "WIFI") == 0)
        switchCommunicationMode(2);
    else if (strcmp(cmd, "LAN") == 0)
        switchCommunicationMode(1);
    else if (strcmp(cmd, "DHCP") == 0)
    {
        // [RACE FIX V17.6] use_dhcp update + conditional activateInterface() ab
        // ek hi NetLockGuard ke andar atomic hain.
        NetLockGuard _lock;
        use_dhcp = true;
        safeSaveInt("l_dhcp", 1);
        btLog("[CMD] LAN MODE SET TO DHCP");
        // [BUG-8] Pehle "activateInterface(comm_mode)" tha. Normal case me
        // comm_mode == active_interface hota hai isliye farq nahi padta - lekin
        // agar device WiFi-primary hai (comm_mode=2) aur abhi failover ki wajah
        // se LAN backup par chal raha hai (active_interface=1), to comm_mode
        // yahan seedha WiFi par wapas switch kar deta - jo LAN setting abhi
        // change ki thi wo turant discard/unused ho jaati (agle failover tak
        // apply hi nahi hoti). Humein sirf currently-active LAN interface ko
        // naye DHCP mode ke saath re-apply karna hai, comm_mode par jump nahi.
        if (active_interface == 1)
            activateInterface(active_interface);
    }
    else if (strcmp(cmd, "STATIC") == 0)
    {
        // [RACE FIX V17.6] same as DHCP# above.
        NetLockGuard _lock;
        use_dhcp = false;
        safeSaveInt("l_dhcp", 0);
        btLog("[CMD] LAN MODE SET TO STATIC");
        // [BUG-8] same fix as DHCP# above - reactivate LAN, not comm_mode.
        if (active_interface == 1)
            activateInterface(active_interface);
    }
    else if (strcmp(cmd, "LOG") == 0)
    {
        isContinuousLogActive = !isContinuousLogActive;
        btLog(isContinuousLogActive ? "[CMD] Log STARTED" : "[CMD] Log STOPPED");
    }
    else if (strcmp(cmd, "FACTORY") == 0)
    {
        btLog("[CMD] FACTORY RESET! Restarting...");
        {
            NetLockGuard _lock; // NVS ko Core1 ke saath share kar rahe hain
            if (nvsReady)
            {
                preferences.clear();
                preferences.end();
                nvsReady = false;
            }
        }
        delay(500);
        esp_restart();
    }
    else if (strcmp(cmd, "REST") == 0)
    {
        btLog("[CMD] RESTARTING...");
        delay(500);
        esp_restart();
    }
    else if (strncmp(cmd, "TEMP,", 5) == 0)
    {
        char *endPtr;
        float thr = strtof(cmd + 5, &endPtr);
        if (endPtr != cmd + 5 && *endPtr == '\0' && !isnan(thr) && thr >= -50.0f && thr <= 150.0f)
        {
            NetLockGuard _lock;
            tempAlert.enabled = (thr > 0.0f);
            tempAlert.threshold = thr;
            safeSaveUChar("tmp_en", tempAlert.enabled ? 1 : 0);
            safeSaveFloat("tmp_thr", thr);
            btLog("[CMD] TEMP ALERT UPDATED");
        }
        else
            btLog("[ERR] Invalid TEMP value");
    }
    else if (strncmp(cmd, "HUM,", 4) == 0)
    {
        char *endPtr;
        float thr = strtof(cmd + 4, &endPtr);
        if (endPtr != cmd + 4 && *endPtr == '\0' && !isnan(thr) && thr >= 0.0f && thr <= 100.0f)
        {
            NetLockGuard _lock;
            humAlert.enabled = (thr > 0.0f);
            humAlert.threshold = thr;
            safeSaveUChar("hum_en", humAlert.enabled ? 1 : 0);
            safeSaveFloat("hum_thr", thr);
            btLog("[CMD] HUM ALERT UPDATED");
        }
        else
            btLog("[ERR] Invalid HUM value");
    }
    else if (strncmp(cmd, "PASS,", 5) == 0)
    {
        size_t passLen = strlen(cmd + 5);
        if (passLen < 1 || passLen > 31)
            btLog("[ERR] Password must be 1-31 chars");
        else
        {
            copyStr(bt_pass, sizeof(bt_pass), cmd + 5);
            safeSaveString("bt_pass", bt_pass);
            btAuthenticated = false;
            authFailedAttempts = 0;
            authLockoutRounds = 0;
            btLog("[CMD] AUTH PASSWORD UPDATED. Session locked.");
        }
    }
    else if (strncmp(cmd, "NET,", 4) == 0)
    {
        char *c1 = strchr(cmd, ',');
        char *c2 = c1 ? strchr(c1 + 1, ',') : NULL;
        char *c3 = c2 ? strchr(c2 + 1, ',') : NULL;
        char *c4 = c3 ? strchr(c3 + 1, ',') : NULL;
        if (c1 && c2 && c3 && c4)
        {
            *c2 = '\0';
            *c3 = '\0';
            *c4 = '\0';
            if (isValidIP(c1 + 1) && isValidIP(c2 + 1) && isValidIP(c3 + 1) && isValidIP(c4 + 1))
            {
                NetLockGuard _lock;
                copyStr(lan_ip, sizeof(lan_ip), c1 + 1);
                copyStr(lan_sn, sizeof(lan_sn), c2 + 1);
                copyStr(lan_gw, sizeof(lan_gw), c3 + 1);
                copyStr(lan_dns, sizeof(lan_dns), c4 + 1);
                safeSaveString("l_ip", lan_ip);
                safeSaveString("l_sn", lan_sn);
                safeSaveString("l_gw", lan_gw);
                safeSaveString("l_dns", lan_dns);
                btLog("[CMD] STATIC NET CONFIG UPDATED");
                // [BUG-8] same fix - reactivate LAN with the new static config,
                // don't jump to comm_mode (see DHCP#/STATIC# comment above).
                if (active_interface == 1 && !use_dhcp)
                    activateInterface(active_interface);
            }
            else
                btLog("[ERR] Invalid IP Configuration");
        }
        else
            btLog("[ERR] Usage: NET,ip,subnet,gateway,dns#");
    }
    else if (strncmp(cmd, "WIFI,", 5) == 0)
    {
        char *c1 = strchr(cmd, ',');
        char *c2 = c1 ? strchr(c1 + 1, ',') : NULL;
        if (c1 && c2)
        {
            *c2 = '\0';
            size_t ssidLen = strlen(c1 + 1);
            size_t passLen = strlen(c2 + 1);
            if (ssidLen < 1 || ssidLen > 32 || passLen > 63)
            {
                btLog("[ERR] SSID 1-32 chars, PASS max 63 chars");
            }
            else
            {
                NetLockGuard _lock;
                copyStr(wifi_ssid, sizeof(wifi_ssid), c1 + 1);
                copyStr(wifi_pass, sizeof(wifi_pass), c2 + 1);
                safeSaveString("w_ssid", wifi_ssid);
                safeSaveString("w_pass", wifi_pass);
                btLog("[CMD] WIFI UPDATED");
                if (active_interface == 2)
                {
                    wifiClient.stop();
                    resetNetworkRetryState();
                    WiFi.disconnect(true);
                    feedWatchdog();
                    WiFi.begin(wifi_ssid, wifi_pass);
                    feedWatchdog();
                }
            }
        }
        else
            btLog("[ERR] Usage: WIFI,ssid,password#");
    }
    else if (strncmp(cmd, "SERVER,", 7) == 0)
    {
        char *c1 = strchr(cmd, ',');
        char *c2 = c1 ? strchr(c1 + 1, ',') : NULL;
        if (c1 && c2)
        {
            *c2 = '\0';
            char tempIP[16] = {0};
            copyStr(tempIP, sizeof(tempIP), c1 + 1);
            char *endPtr;
            long tempPortLong = strtol(c2 + 1, &endPtr, 10);
            if (isValidIP(tempIP) && endPtr != c2 + 1 && *endPtr == '\0' && tempPortLong >= 1 && tempPortLong <= 65535)
            {
                NetLockGuard _lock;
                copyStr(server_ip, sizeof(server_ip), tempIP);
                server_port = (int)tempPortLong;
                safeSaveString("s_ip", server_ip);
                safeSaveInt("s_port", server_port);
                tcpClient->stop();
                resetNetworkRetryState();
                btLog("[CMD] SERVER UPDATED");
            }
            else
                btLog("[ERR] Invalid IP/Port");
        }
        else
            btLog("[ERR] Usage: SERVER,ip,port#");
    }
    else if (strncmp(cmd, "DATA,", 5) == 0)
    {
        char *c1 = strchr(cmd, ',');
        if (c1)
        {
            char *endPtr;
            long val = strtol(c1 + 1, &endPtr, 10);
            if (endPtr != c1 + 1 && *endPtr == '\0' && val >= 15 && val <= 3600)
            {
                NetLockGuard _lock;
                data_freq = (int)val;
                safeSaveInt("d_freq", data_freq);
                ACK_TIMEOUT_MS = (data_freq > 30) ? 30000UL : ((unsigned long)data_freq * 1000UL) / 2UL;
                btLog("[CMD] DATA FREQ UPDATED");
            }
            else
                btLog("[ERR] Freq must be 15-3600");
        }
    }
    else
        btLog("[ERR] Unknown command.");
}

void handleBluetoothIncoming()
{
    bool isBtConnected = SerialBT.hasClient();
    if (btAuthenticated && (millis() - lastAuthTime > AUTH_SESSION_MS))
    {
        btAuthenticated = false;
        btLog("[SYS] Auth session timeout. Locked.");
    }
    static bool wasBtConnected = false;
    if (wasBtConnected && !isBtConnected)
    {
        // Client chala gaya -> session turant band, taaki agla client
        // authenticated state inherit na kar le.
        btAuthenticated = false;
        btRxIndex = 0;
        btRxOverflow = false;
    }
    wasBtConnected = isBtConnected;

    static unsigned long lastCharTime = 0;
    int bytesProcessed = 0;

    // 1. Saara incoming data buffer me jama karo
    while (SerialBT.available() && bytesProcessed++ < 128)
    {
        int rc = SerialBT.read();
        if (rc < 0)
            break;
        char c = (char)rc;
        lastCharTime = millis(); // Har naye character par timer reset

        // Mobile apps dwara bheje gaye hidden newlines ko ignore karo
        if (c == '\n' || c == '\r')
            continue;

        if (btRxOverflow)
            continue; // Agar limit se zyada bada command hai toh ignore karo

        if (btRxIndex < (int)sizeof(btRxBuffer) - 1)
        {
            btRxBuffer[btRxIndex++] = c;
        }
        else
        {
            btRxOverflow = true;
            btLog("[BT_ERR] Cmd too long.");
        }
    }

    // 2. Jab data aana band ho jaye (50ms ka gap) tab processing shuru karo
    if (btRxIndex > 0 && (millis() - lastCharTime > 50))
    {
        if (!btRxOverflow)
        {
            btRxBuffer[btRxIndex] = '\0'; // String ko properly close karo

            // 3. String me SABSE AAKHIRI '#' dhundho (Reverse Search)
            char *lastHash = strrchr(btRxBuffer, '#');

            if (lastHash != NULL)
            {
                *lastHash = '\0'; // Aakhiri '#' ko null terminator bana do, uske aage ka sab cut
                processBtCommand(btRxBuffer);
            }
            else
            {
                btLog("[BT_ERR] Command format invalid (Missing # at the end)");
            }
        }

        // Processing ke baad agle command ke liye buffer reset kar do
        btRxIndex = 0;
        btRxOverflow = false;
        // Secret material ko RAM me pada mat chhodo (AUTH,/PASS,/WIFI, commands)
        memset(btRxBuffer, 0, sizeof(btRxBuffer));
    }
}

// --------------------------------------------------------------------------
// 8. TCP PROTOCOL HANDLERS
// --------------------------------------------------------------------------
void dropDeadConnection(const char *reason)
{
    btLog(reason);
    if (tcpClient != NULL)
        tcpClient->stop();
    resetNetworkRetryState();
}

// Caller (handleTcp) already holds netMutex.
bool sendDataPacket()
{
    struct tm timeinfo;
    char timeStr[10] = "000000";
    char dateStr[10] = "01012000"; // V2 default
    if (tcpState.isTimeSynced && getLocalTime(&timeinfo, 10))
    {
        strftime(timeStr, sizeof(timeStr), "%H%M%S", &timeinfo);
        strftime(dateStr, sizeof(dateStr), "%d%m%Y", &timeinfo);
    }

    int alertCode = 101;
    if (!sensorValid)
        alertCode = 999;
    else if (tempAlert.enabled && currentTemp >= tempAlert.threshold)
        alertCode = 201;
    else if (humAlert.enabled && currentHum >= humAlert.threshold)
        alertCode = 202;

    int sigStrength = (active_interface == 2) ? abs((int)WiFi.RSSI()) : 0;
    float sendTemp = sensorValid ? currentTemp : -999.0f;
    float sendHum = sensorValid ? currentHum : -999.0f;

    // EXACT V2 Format: 1,1, hardcoded & Serial Number limit matching V2
    int n = snprintf(ackState.lastSentPacket, sizeof(ackState.lastSentPacket),
                     "*@,1001,%s,1,1,%d,%s,%s,1226,%d,1,%d,%.2f,%.2f,##\r\n",
                     g_macStr, (unsigned int)tcpState.packetSerialNum, timeStr, dateStr,
                     sigStrength, alertCode, sendTemp, sendHum);
                     
    if (n < 0 || n >= (int)sizeof(ackState.lastSentPacket))
    {
        dropDeadConnection("[NET_ERR_TX_FORMAT] Pkt truncated!");
        return false;
    }
    ackState.lastSentLen = (size_t)n;

    btLog("[TCP_TX] Sending Data Packet to Server:");
    btLog(ackState.lastSentPacket);

    if (tcpClient->write((const uint8_t *)ackState.lastSentPacket, ackState.lastSentLen) != ackState.lastSentLen)
    {
        dropDeadConnection("[NET_ERR_TX_FAILED] Dropping connection.");
        return false;
    }

    ackState.packetSentAt = millis();
    ackState.isWaitingForAck = true;
    retryCount = 0;
    return true;
}

void handleTcp()
{
    NetLockGuard _lock;

    if (server_ip[0] == '\0' || server_port == 0)
        return;
    if (tcpClient == NULL)
        return;

    bool interfaceReady = false;
    if (active_interface == 2 && WiFi.status() == WL_CONNECTED)
        interfaceReady = true;
    if (active_interface == 1 && Ethernet.linkStatus() == LinkON)
        interfaceReady = true;

    if (!interfaceReady)
    {
        if (netState != NET_DISCONNECTED)
        {
            if (active_interface == 2)
                btLog("[NET_ERR_WIFI_LOST] Interface down.");
            else
                btLog("[NET_ERR_LAN_LINK_DOWN] Interface down.");
            tcpClient->stop();
            resetNetworkRetryState();
        }
        return;
    }

    if (!tcpClient->connected())
    {
        if (tcpState.wasConnected)
        {
            dropDeadConnection("[TCP] Connection Lost. States Cleared.");
            return;
        }
        if (netState == NET_CONNECTING)
        {
            if (millis() - connectStartedAt > CONNECT_TIMEOUT_MS)
                netState = NET_DISCONNECTED;
            else
                return;
        }

        unsigned long t_retry = SerialBT.hasClient() ? 20000UL : 5000UL;
        if (netState == NET_DISCONNECTED && millis() - tcpState.lastConnTryTime > t_retry)
        {
            tcpState.lastConnTryTime = millis();
            netState = NET_CONNECTING;
            connectStartedAt = millis();
            btLog("[TCP] Connecting to Server...");
            feedWatchdog();
            bool ok = false;
            if (active_interface == 2)
                ok = wifiClient.connect(server_ip, (uint16_t)server_port, 1500);
            else
                ok = ethClient.connect(server_ip, (uint16_t)server_port);
            feedWatchdog();

            if (ok)
            {
                tcpClient->setTimeout(200);
                tcpState.wasConnected = true;
                tcpState.lastTimeReqSent = 0;
                netState = NET_CONNECTED;
                btLog("[TCP] Connected to Server Successfully!");
            }
            else
            {
                netState = NET_DISCONNECTED;
                btLog("[NET_ERR_SERVER_TIMEOUT] Connect attempt failed.");
            }
        }
        return;
    }
    else
        netState = NET_CONNECTED;

    if (!tcpState.isTimeSynced)
    {
        if (tcpState.lastTimeReqSent == 0 || millis() - tcpState.lastTimeReqSent >= 15000UL)
        {
            tcpState.lastTimeReqSent = millis();
            static const char timeReq[] = "*@,3,205,##\r\n";
            const size_t timeReqLen = sizeof(timeReq) - 1;
            btLog("[TCP_TX] Sending Time and Date Request Packet to Server...");
            if (tcpClient->write((const uint8_t *)timeReq, timeReqLen) != timeReqLen)
                dropDeadConnection("[NET_ERR_TX_FAILED] Time Sync TX Failed!");
        }
        return;
    }

    if (ackState.isWaitingForAck)
    {
        if (millis() - ackState.packetSentAt >= ACK_TIMEOUT_MS)
        {
            if (retryCount < 3)
            {
                retryCount++;
                btLog("[TCP_RETRY] Retrying Pkt.");
                if (tcpClient->write((const uint8_t *)ackState.lastSentPacket, ackState.lastSentLen) != ackState.lastSentLen)
                {
                    dropDeadConnection("[NET_ERR_TX_FAILED] Retry TX Failed!");
                    return;
                }
                ackState.packetSentAt = millis();
            }
            else
            {
                btLog("[NET_ERR_ACK_TIMEOUT] Server Response: FAIL (Timeout). Dropped Pkt.");
                ackState.isWaitingForAck = false;

                if (++tcpState.packetSerialNum > 9999u)
                    tcpState.packetSerialNum = 1;
                // if (++tcpState.packetSerialNum > 999999u)
                //     tcpState.packetSerialNum = 0;
                tcpState.lastDataSendTime = millis();
            }
        }
        return;
    }

    if (data_freq > 0 && (millis() - tcpState.lastDataSendTime >= ((unsigned long)data_freq * 1000UL)))
    {
        if (sendDataPacket())
            tcpState.lastDataSendTime = millis();
    }
}

// Caller (handleTcpIncoming) already holds netMutex.
// Caller (handleTcpIncoming) already holds netMutex.
void parseTcpMessage()
{
    if (tcpRxIndex < 5)
        return;

    // 1. TIME SYNC PARSING (Matches V2 EXACTLY)
    if (!tcpState.isTimeSynced && strncmp(tcpRxBuffer, "*@,", 3) == 0)
    {
        int hr, mn, sc, day, mon, yr;
        // V2 sscanf: %*[^,] ka use karke beech ki values skip karta hai
        int parsed = sscanf(tcpRxBuffer, "*@,%*[^,],%*[^,],%*[^,],%d,%d,%d,%d,%d,%d", &hr, &mn, &sc, &day, &mon, &yr);
        
        if (parsed == 6)
        {
            if (yr < 100) yr += 2000; // V2 2-digit year fix
            
            if (hr >= 0 && hr <= 23 && mn >= 0 && mn <= 59 && sc >= 0 && sc <= 59 &&
                day >= 1 && day <= 31 && mon >= 1 && mon <= 12 && yr >= 2000 && yr <= 2099)
            {
                struct tm tm_s = {};
                tm_s.tm_hour = hr;
                tm_s.tm_min = mn;
                tm_s.tm_sec = sc;
                tm_s.tm_mday = day;
                tm_s.tm_mon = mon - 1;
                tm_s.tm_year = yr - 1900;
                tm_s.tm_isdst = -1;
                
                struct tm check = tm_s;
                time_t t = mktime(&tm_s);
                
                if (t != (time_t)-1 && tm_s.tm_mday == check.tm_mday && tm_s.tm_mon == check.tm_mon && tm_s.tm_year == check.tm_year)
                {
                    struct timeval tv = {.tv_sec = t, .tv_usec = 0};
                    if (settimeofday(&tv, NULL) == 0)
                    {
                        tcpState.isTimeSynced = true;
                        tcpState.lastDataSendTime = millis() - ((unsigned long)data_freq * 1000UL);
                        btLog("[TCP_RX] Server Response: SUCCESS (Time Synced)");
                    }
                    else btLog("[TCP_ERR] settimeofday failed");
                }
                else btLog("[TCP_ERR] Invalid calendar date rejected");
            }
            else btLog("[TCP_ERR] Time payload out of bounds");
        }
        else btLog("[TCP_ERR] Time sync parse FAILED — bad format");
    }
    // 2. DATA ACK PARSING (Matches V2 EXACTLY)
    else if (tcpState.isTimeSynced && strncmp(tcpRxBuffer, "@$,2,", 5) == 0)
    {
        uint32_t ackNum = 0;
        int status = -1;
        // V2 sscanf format: @$,2,%d,%d,#
        int parsed = sscanf(tcpRxBuffer, "@$,2,%u,%d,#", &ackNum, &status);
        
        if (parsed == 2)
        {
            if (ackNum == tcpState.packetSerialNum)
            {
                ackState.isWaitingForAck = false;
                tcpState.lastDataSendTime = millis();
                // V2 rollover limit (10000)
                // tcpState.packetSerialNum = (tcpState.packetSerialNum + 1) % 10000;
                // if (tcpState.packetSerialNum % 50 == 0)
                //     safeSaveInt("p_seq", (int)tcpState.packetSerialNum);

                if (++tcpState.packetSerialNum > 9999u)
                    tcpState.packetSerialNum = 1;

                if (status == 101 || status == 201 || status == 202 || status == 999 || status == 1) {
                    btLog("[SERVER RESP] Data Sent SUCCESSFULLY (ACK Received from Server)");
                } else {
                    char unk[80];
                    snprintf(unk, sizeof(unk), "[TCP] Server Response: UNKNOWN (%d)", status);
                    btLog(unk);
                }
            }
            else btLog("[SERVER RESP] FAIL (ACK ignored - seq mismatch)");
        }
        else btLog("[TCP_ERR] Server Response: FAIL (Payload malformed)");
    }
}
void handleTcpIncoming()
{
    NetLockGuard _lock;

    if (tcpClient == NULL)
        return;

    if (tcpClient->available())
        lastTcpRxActivity = millis();

    int bytesProcessed = 0;
    while (tcpClient->available() && bytesProcessed++ < 256)
    {
        int rc = tcpClient->read();
        if (rc < 0)
            break;
        char c = (char)rc;

        if (c == '\n' || c == '\r')
            continue;

        if (tcpRxOverflow)
        {
            if (tcpLastChar == '#' && c == '#')
            {
                tcpRxIndex = 0;
                tcpRxOverflow = false;
                tcpLastChar = 0;
                continue;
            }
            tcpLastChar = c;
            continue;
        }

        if (tcpRxIndex < 255)
        {
            tcpRxBuffer[tcpRxIndex++] = c;
            tcpRxBuffer[tcpRxIndex] = '\0';
        }
        else
        {
            tcpRxOverflow = true;
            tcpLastChar = c;
            continue;
        }

        // V2 EXACT LOGIC: Packet ending check (Double ## OR Single # for ACK)
        bool isComplete = false;
        if (tcpRxIndex >= 2 && tcpRxBuffer[tcpRxIndex - 2] == '#' && tcpRxBuffer[tcpRxIndex - 1] == '#') 
        {
            isComplete = true; // Ends with "##" (Time Packet)
        } 
        else if (tcpRxIndex >= 1 && tcpRxBuffer[tcpRxIndex - 1] == '#') 
        {
            if (strncmp(tcpRxBuffer, "@$,2,", 5) == 0) 
            {
                isComplete = true; // Ends with single "#" (Data ACK Packet)
            }
        }

        if (isComplete)
        {
            parseTcpMessage();
            tcpRxIndex = 0;
            tcpRxBuffer[0] = '\0';
            tcpLastChar = 0;
            continue;
        }
        tcpLastChar = c;
    }

    if ((tcpRxIndex > 0 || tcpRxOverflow) && millis() - lastTcpRxActivity > 10000UL)
    {
        btLog("[NET_ERR_RX_TIMEOUT] Resync: clearing stale buffer.");
        tcpRxIndex = 0;
        tcpRxBuffer[0] = '\0';
        tcpRxOverflow = false;
        tcpLastChar = 0;
    }
}
// --------------------------------------------------------------------------
// 9. AM2301B / AHT-SERIES SENSOR (NON-BLOCKING STATE MACHINE)
// --------------------------------------------------------------------------
// [BUG-3] V17.6 me sensor read har 2 second par 80ms ka blocking delay() karta
// tha (aur uske andar feedWatchdog() manually call karna padta tha). Us 80ms me
// loop() ka TCP/RX/failover kuch bhi nahi chal pata tha. Ab ye ek 3-phase state
// machine hai - koi delay() nahi, loop latency ~80ms kam.
//
// [BUG-1] AHT20/AM2301B kabhi initialize (0xBE) nahi hota tha. Agar sensor
// uncalibrated boot hota hai (status bit 0x08 = 0) to har reading fail hoti thi
// aur device hamesha "SENSOR: FAULT" bhejta rehta tha. Ab status byte padh kar
// zaroorat padne par auto-init hota hai.
enum SensorPhase
{
    SENSOR_IDLE,      // agli reading ka wait
    SENSOR_WAIT_INIT, // 0xBE init command bheja hai, settle hone do
    SENSOR_WAIT_CONV  // 0xAC measurement trigger kiya hai, conversion ka wait
};

static SensorPhase sensorPhase = SENSOR_IDLE;
static unsigned long sensorPhaseStart = 0;
static unsigned long lastSensorRead = 0;

static void sensorResetAveraging()
{
    // [BUG-2] Fault ke baad ring buffer reset zaroori hai. Pehle ye nahi hota
    // tha, isliye sensor wapas aane par 10-second average me purani (kai minute
    // purani) readings mix ho jaati thi.
    sample_idx = 0;
    buffer_full = false;
    for (int i = 0; i < AVG_SAMPLES; i++)
    {
        t_arr[i] = 0.0f;
        h_arr[i] = 0.0f;
    }
}

static void sensorTriggerMeasurement()
{
    Wire.beginTransmission(AM2301B_ADDR);
    Wire.write(0xAC);
    Wire.write(0x33);
    Wire.write(0x00);
    Wire.endTransmission();
    sensorPhase = SENSOR_WAIT_CONV;
    sensorPhaseStart = millis();
}

static void sensorMarkFailure()
{
    sensorGoodCount = 0;
    if (sensorFailCount < 3)
        sensorFailCount++;
    if (sensorFailCount >= 3)
    {
        NetLockGuard _lock; // sensorValid ko Core0 (GET#) bhi padhta hai
        if (sensorValid)
            sensorResetAveraging();
        sensorValid = false;
    }
}

static void sensorCollectResult()
{
    float t = NAN;
    float h = NAN;

    uint8_t got = Wire.requestFrom((uint8_t)AM2301B_ADDR, (uint8_t)7);
    if (got == 7 && Wire.available() >= 7)
    {
        uint8_t data[7];
        for (int i = 0; i < 7; i++)
            data[i] = (uint8_t)Wire.read();

        bool crcOk = (crc8_aht(data, 6) == data[6]);
        if (crcOk && (data[0] & 0x80) == 0)
        {
            uint32_t hum_raw = ((uint32_t)data[1] << 12) | ((uint32_t)data[2] << 4) | (uint32_t)(data[3] >> 4);
            uint32_t temp_raw = (((uint32_t)(data[3] & 0x0F)) << 16) | ((uint32_t)data[4] << 8) | (uint32_t)data[5];

            h = ((float)hum_raw * 100.0f) / 1048576.0f;
            t = ((float)temp_raw * 200.0f) / 1048576.0f - 50.0f;
        }
    }
    // Bache hue bytes (agar koi hon) drain kar do, warna agli read shift ho jaayegi
    while (Wire.available())
        (void)Wire.read();

    if (!isnan(t) && !isnan(h) && t >= -40.0f && t <= 80.0f && h >= 0.0f && h <= 100.0f)
    {
        sensorFailCount = 0;

        t_arr[sample_idx] = t;
        h_arr[sample_idx] = h;
        sample_idx++;
        if (sample_idx >= AVG_SAMPLES)
        {
            sample_idx = 0;
            buffer_full = true;
        }

        if (sensorGoodCount < 3)
            sensorGoodCount++;

        // Sensor stable hone ke baad hi pichhle ~10 second ka average publish karo
        if (sensorGoodCount >= 3)
        {
            float sum_t = 0.0f, sum_h = 0.0f;
            int count = buffer_full ? AVG_SAMPLES : sample_idx;
            if (count > 0)
            {
                for (int i = 0; i < count; i++)
                {
                    sum_t += t_arr[i];
                    sum_h += h_arr[i];
                }
                NetLockGuard _lock; // currentTemp/currentHum Core0 se bhi padhe jaate hain
                currentTemp = sum_t / (float)count;
                currentHum = sum_h / (float)count;
                sensorValid = true;
            }
        }
    }
    else
    {
        sensorMarkFailure();
    }
}

void handleSensor()
{
    switch (sensorPhase)
    {
    case SENSOR_IDLE:
    {
        if (millis() - lastSensorRead < SENSOR_PERIOD_MS)
            return;
        lastSensorRead = millis();

        // [BUG-1] Status byte padho - calibration bit (0x08) set hai ya nahi
        uint8_t status = 0;
        bool statusOk = false;
        Wire.beginTransmission(AM2301B_ADDR);
        Wire.write(0x71);
        if (Wire.endTransmission() == 0)
        {
            if (Wire.requestFrom((uint8_t)AM2301B_ADDR, (uint8_t)1) == 1 && Wire.available())
            {
                status = (uint8_t)Wire.read();
                statusOk = true;
            }
        }

        if (!statusOk)
        {
            // Sensor I2C par jawab hi nahi de raha
            sensorMarkFailure();
            return;
        }

        if ((status & 0x08) == 0)
        {
            // Uncalibrated -> init sequence bhejo (0xBE, 0x08, 0x00)
            btLog("[SENSOR] Not calibrated. Sending init command...");
            Wire.beginTransmission(AM2301B_ADDR);
            Wire.write(0xBE);
            Wire.write(0x08);
            Wire.write(0x00);
            Wire.endTransmission();
            sensorPhase = SENSOR_WAIT_INIT;
            sensorPhaseStart = millis();
            return;
        }

        sensorTriggerMeasurement();
        return;
    }

    case SENSOR_WAIT_INIT:
    {
        if (millis() - sensorPhaseStart < SENSOR_INIT_WAIT_MS)
            return;
        sensorTriggerMeasurement();
        return;
    }

    case SENSOR_WAIT_CONV:
    {
        if (millis() - sensorPhaseStart < SENSOR_CONV_MS)
            return;
        sensorCollectResult();
        sensorPhase = SENSOR_IDLE;
        return;
    }
    }
}
// --------------------------------------------------------------------------
// 10. COMM TASK (CORE 0) & SETUP()
// --------------------------------------------------------------------------
// commTask Core 0 par chalta hai - iske paas Bluetooth command parsing aur web
// config portal (webServer.handleClient()) hai. Core 0 par WiFi/BT radio stack
// ke apne internal tasks pehle se chalte hain, isliye comm-facing kaam usi core
// par rakha gaya hai; sensor + TCP protocol Core 1 (Arduino loop) par hai.
// Ye task tcpClient/WiFi/Ethernet state ko kabhi seedha nahi chhoota - hamesha
// upar wale NetLockGuard-protected functions ke through jaata hai.
void commTask(void *pvParameters)
{
    (void)pvParameters;
    for (;;)
    {
        handleBluetoothIncoming();

        if (isConfigMode)
        {
            webServer.handleClient();

            // [OPT-5] Config Mode me Core1 ka loop() jaldi return kar deta hai
            // par network call ke dauraan wo 1-2 second block bhi ho sakta hai.
            // Core0 se bhi WDT feed karo - LEKIN sirf tab jab Core1 ne pichhle
            // 15 second me heartbeat update kiya ho. Isse:
            //   - lambi blocking network call par spurious hardware reset nahi hota
            //   - asli Core1 hang par TPL5010 ab bhi device ko reset karta hai
            unsigned long hb = g_loopHeartbeat;
            if ((unsigned long)(millis() - hb) < LOOP_STALL_LIMIT_MS)
                feedWatchdog();
        }

        vTaskDelay(pdMS_TO_TICKS(2));
    }
}

void setup()
{
    // [BUG FIX V17.6] Asli FreeRTOS API ka naam "xSemaphoreCreateRecursiveMutex()"
    // hai - "xSemaphoreCreateMutexRecursive()" (jo pehle likha tha) ek galat/
    // non-existent function name hai jiski wajah se compile hi fail ho raha tha.
    netMutex = xSemaphoreCreateRecursiveMutex();
    logMutex = xSemaphoreCreateRecursiveMutex(); // [SEC-1]

    Serial.begin(115200);
    delay(1000);

     // ---- YE ADD KARO ----
    esp_reset_reason_t rr = esp_reset_reason();
    const char* reasonStr = "UNKNOWN";
    switch (rr) {
        case ESP_RST_POWERON:   reasonStr = "POWERON (normal boot)"; break;
        case ESP_RST_EXT:       reasonStr = "EXT_PIN (external reset pin)"; break;
        case ESP_RST_SW:        reasonStr = "SW (esp_restart() call)"; break;
        case ESP_RST_PANIC:     reasonStr = "PANIC (crash / exception)"; break;
        case ESP_RST_INT_WDT:   reasonStr = "INT_WDT (interrupt watchdog)"; break;
        case ESP_RST_TASK_WDT:  reasonStr = "TASK_WDT (task watchdog)"; break;
        case ESP_RST_WDT:       reasonStr = "WDT (other watchdog)"; break;
        case ESP_RST_DEEPSLEEP: reasonStr = "DEEPSLEEP wake"; break;
        case ESP_RST_BROWNOUT:  reasonStr = "BROWNOUT (power dip!)"; break;
        case ESP_RST_SDIO:      reasonStr = "SDIO reset"; break;
        default: break;
    }
    Serial.printf("\n*** RESET REASON: %d - %s ***\n\n", (int)rr, reasonStr);
    // ---- END ----

    setenv("TZ", "IST-5:30", 1);
    tzset();

    pinMode(LED_D3, OUTPUT);
    pinMode(LED_D4, OUTPUT);
    pinMode(WDT_DONE_PIN, OUTPUT);
    digitalWrite(WDT_DONE_PIN, LOW);
    digitalWrite(LED_D3, LOW);
    digitalWrite(LED_D4, LOW);

    g_loopHeartbeat = millis();

    Serial.println("\n--- Industrial Sensor Node V17.7 ---");
    btLog("[SYS] Firmware Starting Up...");

    if (netMutex == NULL || logMutex == NULL)
        btLog("[SYS_WARN] Mutex alloc failed - running without lock protection!");

    if (preferences.begin("sensor_app", false))
        nvsReady = true;
    else
        btLog("[SYS_WARN] NVS init failed. Settings will not persist.");

    // [BUG-4] Har NVS read ab nvsReady ke andar hai aur har copy explicit
    // null-terminate hoti hai (purana code seedha strncpy karta tha, jo source
    // ke poore-size hone par terminator nahi likhta).
    if (nvsReady)
    {
        String t_btpass = preferences.getString("bt_pass", "123456");
        copyStr(bt_pass, sizeof(bt_pass), t_btpass.c_str());

        String t_ssid = preferences.getString("w_ssid", "");
        copyStr(wifi_ssid, sizeof(wifi_ssid), t_ssid.c_str());
        String t_pass = preferences.getString("w_pass", "");
        copyStr(wifi_pass, sizeof(wifi_pass), t_pass.c_str());

        use_dhcp = (preferences.getInt("l_dhcp", 1) == 1);

        String t_lan_ip = preferences.getString("l_ip", "192.168.1.100");
        if (isValidIP(t_lan_ip.c_str()))
            copyStr(lan_ip, sizeof(lan_ip), t_lan_ip.c_str());
        String t_lan_sn = preferences.getString("l_sn", "255.255.255.0");
        if (isValidIP(t_lan_sn.c_str()))
            copyStr(lan_sn, sizeof(lan_sn), t_lan_sn.c_str());
        String t_lan_gw = preferences.getString("l_gw", "192.168.1.1");
        if (isValidIP(t_lan_gw.c_str()))
            copyStr(lan_gw, sizeof(lan_gw), t_lan_gw.c_str());
        String t_lan_dns = preferences.getString("l_dns", "8.8.8.8");
        if (isValidIP(t_lan_dns.c_str()))
            copyStr(lan_dns, sizeof(lan_dns), t_lan_dns.c_str());

        String t_ip = preferences.getString("s_ip", "");
        if (isValidIP(t_ip.c_str()))
            copyStr(server_ip, sizeof(server_ip), t_ip.c_str());

        server_port = preferences.getInt("s_port", 0);
        if (server_port < 1 || server_port > 65535)
            server_port = 0;

        int savedFreq = preferences.getInt("d_freq", 60);
        data_freq = (savedFreq >= 15 && savedFreq <= 3600) ? savedFreq : 60;

        int savedMode = preferences.getInt("c_mode", 2);
        comm_mode = (savedMode == 1 || savedMode == 2) ? savedMode : 2;

        // Reboot par sequence number 50 aage badha dete hain taaki NVS me har
        // packet write na karna pade (wear-levelling) aur phir bhi duplicate
        // serial numbers server tak na jaayein.
       
       // packet serial numner in nvs
       
        // int savedSeq = preferences.getInt("p_seq", 0);
        // if (savedSeq < 0 || savedSeq > 999999)
        //     savedSeq = 0;
        // savedSeq += 50;
        // if (savedSeq > 999999)
        //     savedSeq = 0;
        // tcpState.packetSerialNum = (uint32_t)savedSeq;
        // safeSaveInt("p_seq", savedSeq);/

        // NVS save disabled. Har naye session me packet 1 se shuru hoga.
        tcpState.packetSerialNum = 1;

        tempAlert.enabled = (preferences.getUChar("tmp_en", 0) == 1);
        tempAlert.threshold = preferences.getFloat("tmp_thr", 0.0f);
        humAlert.enabled = (preferences.getUChar("hum_en", 0) == 1);
        humAlert.threshold = preferences.getFloat("hum_thr", 0.0f);

        // Corrupt/aadhe-likhe NVS values ko sane range me clamp karo
        if (isnan(tempAlert.threshold) || tempAlert.threshold < -50.0f || tempAlert.threshold > 150.0f)
        {
            tempAlert.threshold = 0.0f;
            tempAlert.enabled = false;
        }
        if (isnan(humAlert.threshold) || humAlert.threshold < 0.0f || humAlert.threshold > 100.0f)
        {
            humAlert.threshold = 0.0f;
            humAlert.enabled = false;
        }
    }
    else
    {
        copyStr(bt_pass, sizeof(bt_pass), "123456");
    }

    ACK_TIMEOUT_MS = (data_freq > 30) ? 30000UL : ((unsigned long)data_freq * 1000UL) / 2UL;

    uint64_t chipid = ESP.getEfuseMac();
    uint8_t *mac = (uint8_t *)&chipid;
    snprintf(g_macStr, sizeof(g_macStr), "%02X%02X%02X%02X%02X%02X",
             mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
    copyStr(g_macTail, sizeof(g_macTail), g_macStr + 8); // aakhiri 4 hex chars
    esp_read_mac(eth_mac, ESP_MAC_ETH);

    btLog("[SYS] Initializing I2C for AM2301B Sensor...");
    Wire.begin(21, 22);

    char btName[32];
    snprintf(btName, sizeof(btName), "Ajeevi_TH_%s", g_macTail); // [OPT-1] no String
    SerialBT.begin(btName);

    btLog("[SYS] Initializing SPI for W5500 Ethernet...");
    pinMode(W5500_RST, OUTPUT);
    digitalWrite(W5500_RST, LOW);
    delay(50);
    digitalWrite(W5500_RST, HIGH);
    delay(200);
    SPI.begin(W5500_SCLK, W5500_MISO, W5500_MOSI, W5500_CS);
    Ethernet.init(W5500_CS);
    ethClient.setConnectionTimeout(1000);

    activateInterface(comm_mode);
    lastTcpRxActivity = millis();
    lastSensorRead = millis();
    g_loopHeartbeat = millis();

    // Stack 8192 -> 10240: handleRoot() ke HTML-escape buffers (~1.3 KB) +
    // WebServer/BluetoothSerial ke internal frames ke liye thoda headroom.
    // Ye extra 2 KB heap se aata hai, ek baar, boot par.
    xTaskCreatePinnedToCore(commTask, "commTask", 10240, NULL, 1, NULL, 0);

    btLog("[SYS] Boot complete.");
}
// --------------------------------------------------------------------------
// 11. MAIN LOOP (CORE 1)
// --------------------------------------------------------------------------
void loop()
{

    // [OPT-5] Core0 isi heartbeat se decide karta hai ki WDT feed karna safe hai
    g_loopHeartbeat = millis();

    feedWatchdog();
    checkDailyRestart();
    handleLEDs();

    if (isConfigMode)
    {
        if (millis() - configModeEnteredAt > CONFIG_MODE_TIMEOUT_MS)
        {
            btLog("[SYS] Config mode timed out with no save. Restarting to normal operation...");
            delay(500);
            esp_restart();
        }
        delay(10);
        return;
    }

    handleAutoFailover();

    // ---------------- SMART STEP-BY-STEP LIVE LOG BLOCK ----------------
    // [RACE-1] Ye block active_interface / tcpClient / wifi_ssid / server_ip
    // padhta hai - wahi state jo Core0 (BT command / web save) activateInterface()
    // ke through badal sakta hai. V17.6 me ye bilkul bina lock ke chal raha tha,
    // yaani tcpClient ek dangling pointer ban sakta tha jab exactly usi waqt
    // Core0 interface switch kar de. Ab poora snapshot lock ke andar banta hai.
    // [OPT-1] Arduino String concatenation hata di - ye block har second chalta
    // hai, 24x7, aur heap fragmentation ka sabse bada source tha.
   // ---------------- SMART STEP-BY-STEP LIVE LOG BLOCK ----------------
    // 🛠️ SAFETY GUARD ADDED: Auto-Stop after 5 mins to prevent BT Crash
    static bool wasLogActive = false;
    static unsigned long logActiveSince = 0;

    if (isContinuousLogActive)
    {
        // Jaise hi user log ON kare, timer shuru kar do
        if (!wasLogActive) {
            logActiveSince = millis();
            wasLogActive = true;
        }

        // 5 Minute (300,000 ms) poore hote hi force STOP kar do
        if (millis() - logActiveSince > 300000UL) 
        {
            isContinuousLogActive = false;
            wasLogActive = false; // Agli baar ke liye reset
            btLog("\r\n[SYS_WARN] Live Log Auto-Stopped to prevent BT Crash.\r\n");
        }
        // Agar 5 minute nahi huye hain, toh har 1 second me log print karo
        else if (millis() - lastContinuousLogTime >= 1000)
        {
            lastContinuousLogTime = millis();

            char logMsg[288];
            logMsg[0] = '\0';

            {
                NetLockGuard _lock;

                bool isNetworkUp = false;
                char currentIP[16] = "0.0.0.0";

                // STEP 1: Network Check
                if (active_interface == 2)
                {
                    isNetworkUp = (WiFi.status() == WL_CONNECTED);
                    if (isNetworkUp)
                    {
                        IPAddress wip = WiFi.localIP();
                        snprintf(currentIP, sizeof(currentIP), "%u.%u.%u.%u",
                                 (unsigned)wip[0], (unsigned)wip[1], (unsigned)wip[2], (unsigned)wip[3]);
                    }
                    else
                    {
                        snprintf(logMsg, sizeof(logMsg),
                                 "[LOG-STEP 1] Wi-Fi connecting to SSID: %s ...", wifi_ssid);
                    }
                }
                else
                {
                    isNetworkUp = (Ethernet.linkStatus() == LinkON);
                    if (isNetworkUp)
                    {
                        IPAddress lip = Ethernet.localIP();
                        snprintf(currentIP, sizeof(currentIP), "%u.%u.%u.%u",
                                 (unsigned)lip[0], (unsigned)lip[1], (unsigned)lip[2], (unsigned)lip[3]);
                    }
                    else
                    {
                        snprintf(logMsg, sizeof(logMsg),
                                 "[LOG-STEP 1] LAN Cable Disconnected. Waiting for link...");
                    }
                }

                // STEP 2 & 3: TCP & Server Sync Check
                if (isNetworkUp)
                {
                    if (tcpClient == NULL || !tcpClient->connected())
                    {
                        snprintf(logMsg, sizeof(logMsg),
                                 "[LOG-STEP 2] Network UP (IP: %s). TCP connecting to %s:%d ...",
                                 currentIP, server_ip[0] ? server_ip : "(not set)", server_port);
                    }
                    else if (!tcpState.isTimeSynced)
                    {
                        snprintf(logMsg, sizeof(logMsg),
                                 "[LOG-STEP 3] TCP Connected! Waiting for Server Time Sync...");
                    }
                    // STEP 4: All Connected! Show Live Sensor Data
                    else
                    {
                        long timeLeft = 0;
                        if (data_freq > 0)
                        {
                            long elapsed = (long)((millis() - tcpState.lastDataSendTime) / 1000UL);
                            timeLeft = (long)data_freq - elapsed;
                            if (timeLeft < 0)
                                timeLeft = 0;
                        }

                        snprintf(logMsg, sizeof(logMsg),
                                 "\r\n=========================\r\n"
                                 "Temperature : %.1f \xC2\xB0" "C\r\n"
                                 "Humidity    : %.1f %%\r\n"
                                 "Mode        : %s\r\n"
                                 "Time left   : %ld Sec\r\n"
                                 "=========================",
                                 currentTemp, currentHum,
                                 (active_interface == 2) ? "Wi-Fi" : "LAN",
                                 timeLeft);
                    }
                }
            } // NetLockGuard release

            if (logMsg[0] != '\0')
                btLog(logMsg);
        }
    }
    else 
    {
        // Agar user khud command bhej kar log band kare, toh flag reset kar do
        wasLogActive = false; 
    }
    // -------------------------------
    // -------------------------------

    // Sensor: non-blocking state machine [BUG-3]
    handleSensor();

   // ---------------- Wi-Fi KEEPALIVE (PASSIVE & SAFE) ----------------
    {
        NetLockGuard _lock;
        if (comm_mode == 2 || active_interface == 2)
        {
            static unsigned long lastWifiConnectedTime = millis();
            static bool wifiIPPrinted = false;
            bool wifiNowConnected = (WiFi.status() == WL_CONNECTED);

            if (wifiNowConnected)
            {
                lastWifiConnectedTime = millis(); // 🛠️ Timer hamesha reset hoga
                if (!wifiIPPrinted)
                {
                    IPAddress wip = WiFi.localIP();
                    char ipLog[48];
                    snprintf(ipLog, sizeof(ipLog), "[WIFI] Connected! IP: %u.%u.%u.%u",
                             (unsigned)wip[0], (unsigned)wip[1], (unsigned)wip[2], (unsigned)wip[3]);
                    btLog(ipLog);
                    wifiIPPrinted = true;
                }
            }
            else if (wifi_ssid[0] != '\0')
            {
                wifiIPPrinted = false;
                
                // 🛠️ PASSIVE WAIT: Router ki key rotation par ESP32 khud reconnect karega.
                // Hum tabhi force karenge jab 60 sec tak connection down rahe.
                if (millis() - lastWifiConnectedTime > 60000UL)
                {
                    lastWifiConnectedTime = millis();
                    feedWatchdog();
                    btLog("[WIFI_WARN] Disconnected for 60s. Forcing reconnect...");
                    WiFi.disconnect();
                    WiFi.begin(wifi_ssid, wifi_pass);
                    feedWatchdog();
                }
            }
        }
    }
    // ---------------- LAN KEEPALIVE ----------------
    // [RACE-1] Ethernet.maintain() / initEthernet() ab lock ke andar
    {
        NetLockGuard _lock;
        if (comm_mode == 1 || active_interface == 1)
        {
            if (use_dhcp)
                Ethernet.maintain();

            static unsigned long lastLanRetry = 0;
            if (Ethernet.linkStatus() == LinkON && Ethernet.localIP() == IPAddress(0, 0, 0, 0))
            {
                if (millis() - lastLanRetry > 10000UL)
                {
                    lastLanRetry = millis();
                    initEthernet();
                }
            }
        }
    }

    handleTcp();
    handleTcpIncoming();
}
