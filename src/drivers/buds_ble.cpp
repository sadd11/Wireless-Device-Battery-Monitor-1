// OPPO Enco, realme Buds and Xiaomi Redmi Buds earbuds over Bluetooth LE.
//
// Paired with Windows these buds are audio only: the classic (A2DP) link carries no battery level
// for many models, so the Bluetooth fallback has nothing to show. Their companion apps (HeyMelody,
// realme Link, Xiaomi Earbuds) talk over a separate Bluetooth LE side, which the buds keep
// advertising for, and that side carries the standard Battery Service (0x180F / 0x2A19, one byte
// 0-100) readable without pairing -- the same channel the Marshall EMBERTON II (marshall.cpp) and
// the BigBigWon Armor X Pro (armorx.cpp) are read on. Nothing is ever written: the buds are only
// listened to, and the LE connection is dropped after each read.
//
// The buds advertise their name, so the shared advertisement watcher (ble_adverts.cpp, active scan)
// matches the name of a paired, connected classic device to its current LE address, the way the
// Armor X is matched by its "ARMOR-X..." name. A TWS set is normally paired one at a time, so if
// the names do not line up exactly, one candidate bud and one fresh advert are paired anyway.
//
// The Battery Level characteristic carries no charging flag, so charging is guessed from the
// reading trend, the way armorx.cpp does it (ArmorX::Trend).
//
// Hardware status: worked out from the published behaviour of the companion apps, untested on real
// buds so far. Models whose LE side keeps the Battery Service locked simply fail the read and stay
// unlisted, so a wrong guess cannot show a wrong level.
#include "drivers.h"
#include "armorx_trend.h"
#include "ble_adverts.h"

#include <setupapi.h>
#include <initguid.h>
#include <devpkey.h>
#include <roapi.h>

#include <cwchar>
#include <cwctype>
#include <map>
#include <mutex>
#include <string>
#include <vector>

namespace {

const DEVPROPKEY kIsConnected = { { 0x83DA6326, 0x97A6, 0x4088, { 0x94, 0x53, 0xA1, 0x92, 0x3F, 0x57, 0x3B, 0x29 } }, 15 };

const ULONGLONG kQueryEveryMs = 120 * 1000;  // successful reads
const ULONGLONG kRetryMs = 60 * 1000;        // after a failed read (buds off, out of range, service locked)
const ULONGLONG kStaleMs = 6 * 60 * 1000;    // stop reporting a reading this old
const ULONGLONG kAdvertFreshMs = 5 * 60 * 1000;  // match against adverts heard this recently

struct Bud {
    std::wstring name;
    ULONGLONG addr = 0;      // Classic (public) address
    std::wstring addrText;   // 12 hex digits
};

struct Query {
    ULONGLONG classic = 0;   // Classic address, keys the state
    ULONGLONG le = 0;        // LE address heard advertising
};

struct Entry {
    ULONGLONG lastAttempt = 0, lastOk = 0;
    int percent = -1;
    bool charging = false;
    ArmorX::Trend trend;
};

struct State {
    std::mutex m;
    bool running = false;
    std::map<ULONGLONG, Entry> entries;        // by Classic address
    std::map<ULONGLONG, ULONGLONG> heard;      // LE address -> tick of the last matching advert
    std::map<ULONGLONG, std::wstring> names;   // LE address -> lower-cased advert name
    std::vector<Query> pending;                // handed to the query thread
};
State g_state;

std::wstring Lower(std::wstring s) {
    for (auto& ch : s) ch = towlower(ch);
    return s;
}

// OPPO Enco ("OPPO Enco Air2", "Enco Buds2"), realme ("realme Buds Air 6") and Redmi ("Redmi Buds
// 4 Pro") buds. A bare "buds" is not matched: Samsung, Nothing, Huawei and dozens of other names
// contain it, and "realme" alone also matches phones.
bool IsBudName(const std::wstring& lower) {
    return lower.find(L"enco") != std::wstring::npos ||
           lower.find(L"redmi buds") != std::wstring::npos ||
           (lower.find(L"realme") != std::wstring::npos && lower.find(L"buds") != std::wstring::npos);
}

// Paired, connected buds whose Classic Bluetooth link is up (audio playing or in the case nearby).
std::vector<Bud> FindConnectedBuds() {
    std::vector<Bud> out;
    HDEVINFO di = SetupDiGetClassDevsW(nullptr, L"BTHENUM", nullptr, DIGCF_ALLCLASSES | DIGCF_PRESENT);
    if (di == INVALID_HANDLE_VALUE) return out;
    SP_DEVINFO_DATA dd{ sizeof(dd) };
    for (DWORD i = 0; SetupDiEnumDeviceInfo(di, i, &dd); i++) {
        wchar_t inst[512];
        if (!SetupDiGetDeviceInstanceIdW(di, &dd, inst, 512, nullptr)) continue;
        if (_wcsnicmp(inst, L"BTHENUM\\DEV_", 12) != 0) continue;
        std::wstring hex(inst + 12, wcsnlen(inst + 12, 12));
        if (hex.size() != 12) continue;
        wchar_t* end = nullptr;
        ULONGLONG addr = wcstoull(hex.c_str(), &end, 16);
        if (!addr || *end) continue;
        DEVPROPTYPE t;
        DEVPROP_BOOLEAN conn = DEVPROP_FALSE;
        if (!SetupDiGetDevicePropertyW(di, &dd, &kIsConnected, &t, (PBYTE)&conn, sizeof(conn), nullptr, 0) ||
            t != DEVPROP_TYPE_BOOLEAN || conn == DEVPROP_FALSE)
            continue;
        wchar_t name[256] = {};
        if (!SetupDiGetDevicePropertyW(di, &dd, &DEVPKEY_Device_FriendlyName, &t, (PBYTE)name, sizeof(name) - sizeof(wchar_t),
                                       nullptr, 0) ||
            t != DEVPROP_TYPE_STRING)
            continue;
        if (!IsBudName(Lower(name))) continue;
        for (auto& ch : hex) ch = towupper(ch);
        out.push_back({ name, addr, hex });
    }
    SetupDiDestroyDeviceInfoList(di);
    // One physical device can show up as several nodes with the same address: keep the first.
    std::vector<Bud> unique;
    std::map<ULONGLONG, bool> seen;
    for (const Bud& b : out)
        if (!seen[b.addr]) {
            seen[b.addr] = true;
            unique.push_back(b);
        }
    return unique;
}

DWORD WINAPI QueryThread(LPVOID) {
    std::vector<Query> list;
    {
        std::lock_guard<std::mutex> lock(g_state.m);
        list.swap(g_state.pending);
    }
    HRESULT init = RoInitialize(RO_INIT_MULTITHREADED);
    for (const Query& q : list) {
        // The buds' address type is not known from the advertisement here: try random, then public.
        int raw = ReadLeBatteryLevel(q.le, true, true);
        if (raw < 0) raw = ReadLeBatteryLevel(q.le, false, true);
        std::lock_guard<std::mutex> lock(g_state.m);
        Entry& e = g_state.entries[q.classic];
        if (raw >= 0) {
            e.percent = e.trend.Add(raw, e.charging);
            e.lastOk = GetTickCount64();
        }
    }
    if (SUCCEEDED(init)) RoUninitialize();
    std::lock_guard<std::mutex> lock(g_state.m);
    g_state.running = false;
    return 0;
}

}  // namespace

// Called by the shared watcher for every advertisement whose name matches IsBudName.
void BudsBleOnAdvert(UINT64 addr, const std::wstring& name) {
    if (!addr) return;
    std::wstring lower = Lower(name);
    if (!IsBudName(lower)) return;
    ULONGLONG now = GetTickCount64();
    std::lock_guard<std::mutex> lock(g_state.m);
    g_state.heard[addr] = now;
    g_state.names[addr] = lower;
    for (auto it = g_state.heard.begin(); it != g_state.heard.end();) {
        if (now - it->second >= kAdvertFreshMs) {
            g_state.names.erase(it->first);
            it = g_state.heard.erase(it);
        } else {
            ++it;
        }
    }
}

void PollBudsBle(PollContext& ctx) {
    std::vector<Bud> buds = FindConnectedBuds();
    if (buds.empty()) return;

    HANDLE first = nullptr;  // the very first read is waited for (app start, --list)
    {
        ULONGLONG now = GetTickCount64();
        std::lock_guard<std::mutex> lock(g_state.m);
        std::vector<std::pair<ULONGLONG, std::wstring>> fresh;  // heard recently
        for (const auto& h : g_state.heard)
            if (now - h.second < kAdvertFreshMs) fresh.push_back({ h.first, g_state.names[h.first] });
        if (!g_state.running) {
            std::vector<Query> due;
            bool isFirst = false;
            for (const Bud& b : buds) {
                Entry& e = g_state.entries[b.addr];
                ULONGLONG wait = e.lastOk && e.lastOk >= e.lastAttempt ? kQueryEveryMs : kRetryMs;
                if (e.lastAttempt && now - e.lastAttempt < wait) continue;
                ULONGLONG le = 0;
                for (const auto& f : fresh)
                    if (f.second == Lower(b.name)) le = f.first;
                if (!le && buds.size() == 1 && fresh.size() == 1) le = fresh[0].first;
                if (!le) continue;
                isFirst |= !e.lastAttempt;
                e.lastAttempt = now;
                due.push_back({ b.addr, le });
            }
            if (!due.empty()) {
                // On this (poll) thread: EnsureBleWatcher is not thread-safe, and PollBluetooth calls it here too.
                EnsureBleWatcher();
                BleWantActiveScan();  // the buds' names can be in the scan response
                g_state.pending = due;
                if (HANDLE t = CreateThread(nullptr, 0, QueryThread, nullptr, 0, nullptr)) {
                    g_state.running = true;
                    if (isFirst) first = t;
                    else CloseHandle(t);
                }
            }
        }
    }
    if (first) {
        // One absolute 4 s deadline, once per bud, so the first refresh (and --list) can show the
        // level when the buds answer quickly. Later polls never wait; a slower read finishes on its
        // thread and shows on the next refresh.
        WaitForSingleObject(first, 4000);
        CloseHandle(first);
    }

    std::lock_guard<std::mutex> lock(g_state.m);
    ULONGLONG now = GetTickCount64();
    for (const Bud& b : buds) {
        const Entry& e = g_state.entries[b.addr];
        if (!e.lastOk || now - e.lastOk >= kStaleMs) continue;
        DeviceStatus s;
        s.key = L"budsle:" + b.addrText;
        s.name = b.name;
        s.kind = DeviceKind::Headset;
        s.via = L"Bluetooth";
        s.percent = e.percent;
        s.charging = e.charging;
        s.graceSec = 600;
        ctx.out.push_back(s);
    }
}
