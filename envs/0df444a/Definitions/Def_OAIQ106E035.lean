-- Prove2me | Definitions.Def_OAIQ106E035
-- name    : OAIQ106E035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:58:51.199743+00:00
-- url     : https://prove2.me/theorems/3c32226e-b16f-4541-ae9e-8a64ec24542e
-- title:
--   Definitions bundle OAIQ106E035 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3714 declarations of OpenAI's Lean: 3714 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block5.entry1_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry1_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry2_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry2_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry2_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_2` and 3674 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block128`, `MutuallyUnbiased_GramRows_Block129`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block133`, `MutuallyUnbiased_GramRows_Block134`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block149`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block151`, `MutuallyUnbiased_GramRows_Block152`, `MutuallyUnbiased_GramRows_Block153`, `MutuallyUnbiased_GramRows_Block154`, `MutuallyUnbiased_GramRows_Block155`, `MutuallyUnbiased_GramRows_Block156`, `MutuallyUnbiased_GramRows_Block157`, `MutuallyUnbiased_GramRows_Block158`, `MutuallyUnbiased_GramRows_Block159`, `MutuallyUnbiased_GramRows_Block160`, `MutuallyUnbiased_GramRows_Block161`, `MutuallyUnbiased_GramRows_Block162`, `MutuallyUnbiased_GramRows_Block163`, `MutuallyUnbiased_GramRows_Block164`, `MutuallyUnbiased_GramRows_Block165`, `MutuallyUnbiased_GramRows_Block166`, `MutuallyUnbiased_GramRows_Block167`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block175`, `MutuallyUnbiased_GramRows_Block176`, `MutuallyUnbiased_GramRows_Block177`, `MutuallyUnbiased_GramRows_Block178`, `MutuallyUnbiased_GramRows_Block181`, `MutuallyUnbiased_GramRows_Block182`, `MutuallyUnbiased_Moments_GramNormalization`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E036`, `OAIQ106E037`, `OAIQ106E038`, `OAIQ106E040` and `OAIQ106E151`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

def Key.leftCharge (K : Key) : Charge := fun i => (K.rows.getD i.val (0, 0)).1

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2353, 720), (key2359, 2160), (key2448, 2160), (key2454, 4320), (key2515, 2880), (key2566, 1440), (key2578, 720)]

def entry1_0 : Integer.Sparse Key := [(key970, 2880), (key1084, 8640), (key1226, 2880)]

def entry1_1 : Integer.Sparse Key := [(key0, 2880), (key83, 11520)]

def entry2_0 : Integer.Sparse Key := [(key2370, 360), (key2376, 720), (key2388, 480), (key2398, 360), (key2404, 720), (key2435, 480), (key2464, 480), (key2470, 576), (key2478, 720), (key2501, 720), (key2568, 360), (key2570, 240), (key2575, 240), (key2583, 360), (key2589, 720), (key2604, 240), (key2762, 360), (key2768, 720), (key2839, 960), (key2845, 864), (key2876, 1080), (key2916, 720), (key2925, 480), (key3005, 240), (key3019, 720), (key3028, 480)]

def entry2_1 : Integer.Sparse Key := [(key991, 2880), (key1026, 2880), (key1104, 5760), (key1230, 2880)]

def entry2_2 : Integer.Sparse Key := [(key2608, 240), (key2614, 480), (key2624, 480), (key2630, 480), (key2638, 640), (key2657, 320), (key2659, 240), (key2663, 240), (key2669, 480), (key2698, 640), (key2704, 576), (key2724, 720), (key2752, 480), (key2757, 320), (key2778, 320), (key2784, 384), (key2792, 480), (key2801, 480), (key2807, 480), (key2827, 640), (key2851, 480), (key2858, 576), (key2868, 576), (key2918, 384), (key2919, 480), (key2922, 480), (key3007, 240), (key3009, 160), (key3011, 320), (key3016, 240), (key3021, 384), (key3022, 480), (key3025, 480)]

def entry3_0 : Integer.Sparse Key := [(key2355, 2880), (key2450, 8640), (key2512, 2880)]

def entry3_1 : Integer.Sparse Key := [(key968, 2880), (key1082, 11520)]

def entry3_2 : Integer.Sparse Key := [(key2585, 2880), (key2764, 2880), (key2841, 5760), (key2873, 2880)]

def entry3_3 : Integer.Sparse Key := [(key2351, 2880), (key2446, 11520)]

def entry4_0 : Integer.Sparse Key := [(key971, 720), (key979, 2160), (key1085, 2160), (key1093, 4320), (key1164, 2160), (key1228, 2160), (key1245, 720)]

def entry4_1 : Integer.Sparse Key := [(key3, 2880), (key86, 8640), (key147, 2880)]

def entry4_2 : Integer.Sparse Key := [(key993, 720), (key1001, 1440), (key1015, 720), (key1028, 720), (key1036, 1440), (key1071, 720), (key1106, 1440), (key1114, 1440), (key1123, 1440), (key1150, 1440), (key1232, 1440), (key1235, 720), (key1242, 720)]

def entry4_3 : Integer.Sparse Key := [(key973, 2880), (key1087, 8640), (key1160, 2880)]

def entry4_4 : Integer.Sparse Key := [(key1, 720), (key7, 2160), (key84, 2160), (key90, 4320), (key151, 2880), (key193, 1440), (key202, 720)]

def entry5_0 : Integer.Sparse Key := [(key2357, 720), (key2361, 720), (key2363, 960), (key2366, 480), (key2452, 1440), (key2456, 1440), (key2458, 864), (key2461, 576), (key2517, 960), (key2519, 1080), (key2523, 1440), (key2528, 480), (key2530, 1440), (key2560, 960), (key2567, 360), (key2579, 480)]

def entry5_1 : Integer.Sparse Key := [(key974, 2880), (key1088, 5760), (key1178, 5760)]

def entry5_2 : Integer.Sparse Key := [(key2378, 480), (key2383, 192), (key2390, 320), (key2394, 480), (key2406, 480), (key2411, 192), (key2437, 320), (key2443, 480), (key2472, 384), (key2480, 480), (key2484, 384), (key2503, 480), (key2509, 384), (key2524, 480), (key2569, 96), (key2571, 240), (key2576, 240), (key2580, 160), (key2587, 480), (key2593, 288), (key2598, 160), (key2600, 480), (key2766, 480), (key2772, 288), (key2843, 576), (key2880, 384), (key2887, 480), (key2889, 576), (key2910, 720), (key2929, 160), (key2931, 480), (key2966, 480), (key2968, 576), (key2989, 720), (key2995, 480), (key3002, 320)]

def entry5_3 : Integer.Sparse Key := [(key2360, 2880), (key2455, 5760), (key2516, 5760)]

def entry5_4 : Integer.Sparse Key := [(key976, 1440), (key984, 1440), (key1090, 2880), (key1098, 1440), (key1169, 1440), (key1180, 1440), (key1183, 2880), (key1220, 1440)]

def entry5_5 : Integer.Sparse Key := [(key2362, 480), (key2365, 1920), (key2367, 480), (key2457, 960), (key2460, 1920), (key2521, 2560), (key2525, 1152), (key2532, 1280), (key2533, 768), (key2562, 960), (key2564, 1920)]

def entry6_0 : Integer.Sparse Key := [(key2354, 720), (key2358, 2160), (key2449, 2160), (key2453, 4320), (key2514, 2160), (key2529, 2160), (key2559, 720)]

def entry6_1 : Integer.Sparse Key := [(key969, 2880), (key1083, 8640), (key1177, 2880)]

def entry6_2 : Integer.Sparse Key := [(key2584, 720), (key2588, 1440), (key2599, 720), (key2763, 720), (key2767, 1440), (key2840, 1440), (key2844, 1440), (key2875, 1440), (key2888, 1440), (key2909, 720), (key2930, 720), (key2967, 1440), (key2988, 720)]

def entry6_3 : Integer.Sparse Key := [(key2352, 2880), (key2447, 8640), (key2511, 2880)]

def entry6_4 : Integer.Sparse Key := [(key972, 720), (key977, 2160), (key1086, 2160), (key1091, 4320), (key1162, 2160), (key1181, 2160), (key1218, 720)]

def entry6_5 : Integer.Sparse Key := [(key2361, 1440), (key2364, 1440), (key2456, 2880), (key2459, 1440), (key2517, 1440), (key2520, 2880), (key2531, 1440), (key2561, 1440)]

def entry6_6 : Integer.Sparse Key := [(key2353, 720), (key2356, 2160), (key2448, 2160), (key2451, 4320), (key2513, 2880), (key2527, 1440), (key2558, 720)]

def entry7_0 : Integer.Sparse Key := [(key2372, 2160), (key2385, 720), (key2400, 2160), (key2432, 720), (key2466, 4320), (key2475, 2160), (key2498, 2160)]

def entry7_1 : Integer.Sparse Key := [(key989, 2880), (key1024, 2880), (key1102, 8640)]

def entry7_2 : Integer.Sparse Key := [(key2610, 720), (key2626, 1440), (key2635, 720), (key2665, 720), (key2700, 1440), (key2721, 720), (key2780, 1440), (key2789, 720), (key2803, 1440), (key2824, 720), (key2853, 1440), (key2855, 1440), (key2865, 1440)]

def entry7_3 : Integer.Sparse Key := [(key2368, 1440), (key2396, 1440), (key2462, 2880), (key2581, 1440), (key2760, 1440), (key2837, 5760)]

def entry7_4 : Integer.Sparse Key := [(key995, 2160), (key1011, 720), (key1030, 2160), (key1067, 720), (key1108, 4320), (key1119, 2160), (key1146, 2160)]

def entry7_5 : Integer.Sparse Key := [(key2377, 1440), (key2389, 1440), (key2405, 1440), (key2436, 1440), (key2471, 1440), (key2479, 2880), (key2502, 2880), (key2518, 1440)]

def entry7_6 : Integer.Sparse Key := [(key2369, 2160), (key2384, 720), (key2397, 2160), (key2431, 720), (key2463, 4320), (key2474, 2160), (key2497, 2160)]

def entry7_7 : Integer.Sparse Key := [(key2606, 720), (key2622, 2160), (key2661, 720), (key2696, 2880), (key2776, 1440), (key2799, 2160), (key2849, 4320)]

def entry8_0 : Integer.Sparse Key := [(key1850, 2880), (key1852, 8640), (key1884, 2880)]

def entry8_1 : Integer.Sparse Key := [(key685, 11520), (key692, 2880)]

def entry8_2 : Integer.Sparse Key := [(key1859, 2880), (key1861, 5760), (key1867, 2880), (key1877, 2880)]

def entry8_3 : Integer.Sparse Key := [(key1957, 11520), (key1969, 2880)]

def entry8_4 : Integer.Sparse Key := [(key617, 2880), (key619, 8640), (key645, 2880)]

def entry8_5 : Integer.Sparse Key := [(key1851, 5760), (key1855, 5760), (key1886, 2880)]

def entry8_6 : Integer.Sparse Key := [(key1932, 2880), (key1933, 8640), (key1953, 2880)]

def entry8_7 : Integer.Sparse Key := [(key1958, 8640), (key1960, 2880), (key1966, 2880)]

def entry8_8 : Integer.Sparse Key := [(key288, 2880), (key289, 11520)]

def entry9_0 : Integer.Sparse Key := [(key2416, 4320), (key2423, 4320), (key2489, 1440), (key2491, 4320)]

def entry9_1 : Integer.Sparse Key := [(key1045, 8640), (key1131, 5760)]

def entry9_2 : Integer.Sparse Key := [(key2681, 2880), (key2688, 1440), (key2712, 1440), (key2714, 2880), (key2815, 1440), (key2817, 2880), (key2863, 1440)]

def entry9_3 : Integer.Sparse Key := [(key2412, 2880), (key2485, 1440), (key3031, 5760), (key3118, 4320)]

def entry9_4 : Integer.Sparse Key := [(key1050, 4320), (key1058, 4320), (key1136, 1440), (key1138, 4320)]

def entry9_5 : Integer.Sparse Key := [(key2420, 1440), (key2427, 5760), (key2438, 1440), (key2495, 2880), (key2504, 2880)]

def entry9_6 : Integer.Sparse Key := [(key2413, 4320), (key2422, 4320), (key2486, 1440), (key2490, 4320)]

def entry9_7 : Integer.Sparse Key := [(key2677, 2160), (key2708, 2160), (key2811, 1440), (key2861, 576), (key3045, 2160), (key3059, 2160), (key3094, 2880), (key3122, 864)]

def entry9_8 : Integer.Sparse Key := [(key1962, 5760), (key1964, 8640)]

def entry9_9 : Integer.Sparse Key := [(key3079, 1440), (key3084, 8640), (key3099, 4320)]

def entry10_0 : Integer.Sparse Key := [(key1273, 720), (key1278, 2160), (key1696, 2160), (key1701, 4320), (key1751, 2160), (key1933, 2160), (key1953, 720)]

def entry10_2 : Integer.Sparse Key := [(key1358, 720), (key1364, 1440), (key1374, 720), (key1484, 720), (key1490, 1440), (key1513, 720), (key1710, 1440), (key1716, 1440), (key1723, 1440), (key1741, 1440), (key1937, 1440), (key1940, 720), (key1949, 720)]

def entry10_3 : Integer.Sparse Key := [(key1275, 2880), (key1698, 8640), (key1750, 2880)]

def entry10_4 : Integer.Sparse Key := [(key220, 720), (key225, 2160), (key492, 2160), (key497, 4320), (key551, 2160), (key664, 2160), (key681, 720)]

def entry10_5 : Integer.Sparse Key := [(key1277, 1440), (key1283, 1440), (key1700, 2880), (key1706, 1440), (key1756, 1440), (key1851, 1440), (key1855, 2880), (key1886, 1440)]

def entry10_6 : Integer.Sparse Key := [(key1274, 720), (key1278, 2160), (key1697, 2160), (key1701, 4320), (key1751, 2160), (key1852, 2160), (key1884, 720)]

def entry10_7 : Integer.Sparse Key := [(key1360, 2160), (key1372, 720), (key1486, 2160), (key1511, 720), (key1712, 4320), (key1721, 2160), (key1739, 2160)]

def entry10_8 : Integer.Sparse Key := [(key513, 2880), (key515, 8640), (key547, 2880)]

def entry10_9 : Integer.Sparse Key := [(key1501, 4320), (key1506, 4320), (key1733, 1440), (key1735, 4320)]

def entry10_10 : Integer.Sparse Key := [(key288, 720), (key289, 2160), (key513, 2160), (key515, 4320), (key547, 2880), (key670, 1440), (key680, 720)]

def entry11_0 : Integer.Sparse Key := [(key1251, 720), (key1259, 1440), (key1271, 720), (key1526, 720), (key1534, 1440), (key1604, 1440), (key1612, 1440), (key1640, 1440), (key1679, 1440), (key1693, 720), (key1894, 720), (key1916, 1440), (key1930, 720)]

def entry11_1 : Integer.Sparse Key := [(key208, 2880), (key377, 2880), (key428, 5760), (key456, 2880)]

def entry11_2 : Integer.Sparse Key := [(key1291, 240), (key1299, 480), (key1311, 480), (key1319, 480), (key1327, 480), (key1352, 480), (key1355, 240), (key1386, 240), (key1394, 480), (key1419, 480), (key1427, 480), (key1445, 480), (key1473, 480), (key1481, 240), (key1541, 480), (key1549, 480), (key1557, 480), (key1568, 480), (key1576, 480), (key1594, 480), (key1617, 480), (key1625, 480), (key1634, 480), (key1682, 480), (key1684, 480), (key1690, 480), (key1897, 480), (key1900, 240), (key1904, 480), (key1912, 240), (key1919, 480), (key1921, 480), (key1927, 480)]

def entry11_3 : Integer.Sparse Key := [(key1253, 2880), (key1528, 2880), (key1606, 5760), (key1636, 2880)]

def entry11_4 : Integer.Sparse Key := [(key18, 360), (key23, 720), (key35, 480), (key43, 360), (key48, 720), (key74, 480), (key100, 480), (key105, 576), (key115, 720), (key137, 720), (key195, 360), (key196, 240), (key200, 240), (key206, 360), (key212, 720), (key218, 240), (key375, 360), (key381, 720), (key426, 960), (key432, 864), (key460, 1080), (key486, 720), (key490, 480), (key654, 240), (key659, 720), (key663, 480)]

def entry11_5 : Integer.Sparse Key := [(key1256, 960), (key1261, 480), (key1265, 480), (key1268, 960), (key1531, 960), (key1536, 480), (key1609, 960), (key1642, 480), (key1648, 960), (key1651, 960), (key1674, 960), (key1765, 480), (key1768, 960), (key1806, 960), (key1809, 960), (key1832, 960), (key1837, 960), (key1848, 480)]

def entry11_6 : Integer.Sparse Key := [(key1252, 720), (key1257, 1440), (key1266, 720), (key1527, 720), (key1532, 1440), (key1605, 1440), (key1610, 1440), (key1638, 1440), (key1649, 1440), (key1672, 720), (key1766, 720), (key1807, 1440), (key1830, 720)]

def entry11_7 : Integer.Sparse Key := [(key1293, 720), (key1313, 1440), (key1323, 720), (key1388, 720), (key1421, 1440), (key1441, 720), (key1543, 1440), (key1553, 720), (key1570, 1440), (key1590, 720), (key1619, 1440), (key1621, 1440), (key1630, 1440)]

def entry11_8 : Integer.Sparse Key := [(key626, 2880), (key627, 5760), (key629, 2880), (key640, 2880)]

def entry11_9 : Integer.Sparse Key := [(key1407, 2880), (key1411, 1440), (key1435, 1440), (key1436, 2880), (key1584, 1440), (key1585, 2880), (key1628, 1440)]

def entry11_10 : Integer.Sparse Key := [(key280, 720), (key283, 1440), (key292, 720), (key349, 720), (key352, 1440), (key369, 720), (key506, 1440), (key509, 1440), (key520, 1440), (key541, 1440), (key667, 1440), (key671, 720), (key677, 720)]

def entry11_11 : Integer.Sparse Key := [(key236, 240), (key241, 480), (key248, 480), (key253, 480), (key263, 640), (key277, 320), (key278, 240), (key302, 240), (key307, 480), (key316, 640), (key321, 576), (key331, 720), (key346, 480), (key347, 320), (key385, 320), (key390, 384), (key400, 480), (key406, 480), (key411, 480), (key421, 640), (key435, 480), (key445, 576), (key453, 576), (key487, 384), (key488, 480), (key489, 480), (key655, 240), (key656, 160), (key657, 320), (key658, 240), (key660, 384), (key661, 480), (key662, 480)]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13205 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13206 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13207 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13208 : Integer.Sparse Key := [(key1090, -12), (key1098, 12), (key1180, 12), (key1183, -12)]

def row13209 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13210 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13211 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13212 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13213 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13214 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13215 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13216 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13217 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13218 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13219 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13220 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13221 : Integer.Sparse Key := [(key1090, -12), (key1098, 12), (key1180, 12), (key1183, -12)]

def row13222 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13223 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13224 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13225 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13226 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13227 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13228 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key90, 12), (key151, -6), (key193, -6), (key202, 6)]

def row13229 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13230 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13231 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13232 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13233 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13234 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -4), (key202, 2)]

def row13235 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -4), (key202, 2)]

def row13236 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13237 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13238 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13239 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13240 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13241 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key90, 12), (key151, -6), (key193, -6), (key202, 6)]

def row13242 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13243 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13244 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13245 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

def row13246 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

def row13247 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

def row13248 : Integer.Sparse Key := [(key2452, -12), (key2458, 12), (key2528, 12), (key2530, -12)]

def row13249 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

def row13250 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

def row13251 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

def row13252 : Integer.Sparse Key := [(key2452, -4), (key2458, 4), (key2528, 4), (key2530, -4)]

def row13253 : Integer.Sparse Key := [(key2357, -4), (key2361, 4), (key2452, -4), (key2458, 4), (key2528, 4), (key2530, -4)]

def row13254 : Integer.Sparse Key := [(key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4)]

def row13255 : Integer.Sparse Key := [(key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4)]

def row13256 : Integer.Sparse Key := [(key2357, -4), (key2361, 4), (key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4), (key2560, -4), (key2579, 4)]

def row13257 : Integer.Sparse Key := [(key2357, -4), (key2361, 4), (key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4), (key2560, -4), (key2579, 4)]

def row13258 : Integer.Sparse Key := [(key2357, 4), (key2361, -4), (key2363, -4), (key2366, 4), (key2452, 8), (key2456, -4), (key2458, -4), (key2517, -4), (key2523, 8), (key2530, -4)]

def row13259 : Integer.Sparse Key := [(key2357, 4), (key2361, -4), (key2363, -4), (key2366, 4), (key2452, 8), (key2456, -4), (key2458, -4), (key2517, -4), (key2523, 8), (key2530, -4)]

def row13260 : Integer.Sparse Key := [(key2357, 4), (key2361, -4), (key2363, -4), (key2366, 4), (key2452, 8), (key2456, -4), (key2458, -4), (key2517, -4), (key2523, 8), (key2530, -4)]

def row13261 : Integer.Sparse Key := [(key2456, -12), (key2461, 12), (key2517, 12), (key2523, -12)]

def row13262 : Integer.Sparse Key := [(key2456, 4), (key2461, -4), (key2517, -4), (key2523, 4)]

def row13263 : Integer.Sparse Key := [(key2456, 4), (key2461, -4), (key2517, -4), (key2523, 4)]

def row13264 : Integer.Sparse Key := [(key2456, 4), (key2461, -4), (key2517, -4), (key2523, 4)]

def row13265 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13266 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13267 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13268 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1093, 12), (key1164, -6), (key1228, -6), (key1245, 6)]

def row13269 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13270 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13271 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13272 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

def row13273 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

def row13274 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

def row13275 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

def row13276 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

def row13277 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

def row13278 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13279 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13280 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13281 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1093, 12), (key1164, -6), (key1228, -6), (key1245, 6)]

def row13282 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13283 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13284 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

def row13285 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

def row13286 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

def row13287 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

def row13288 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2454, 12), (key2515, -6), (key2566, -6), (key2578, 6)]

def row13289 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

def row13290 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

def row13291 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

def row13292 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

def row13293 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

def row13294 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -4), (key2578, 2)]

def row13295 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -4), (key2578, 2)]

def row13296 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

def row13297 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

def row13298 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

def row13299 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

def row13300 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

def row13301 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2454, 12), (key2515, -6), (key2566, -6), (key2578, 6)]

def row13302 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

def row13303 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

def row13304 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

def row13305 : Integer.Sparse Key := [(key2471, 12), (key2479, -12), (key2502, -12), (key2518, 12)]

def row13306 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13307 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13308 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13309 : Integer.Sparse Key := [(key2471, 12), (key2479, -12), (key2502, -12), (key2518, 12)]

def row13310 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13311 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13312 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13313 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13314 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13315 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13316 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13317 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13318 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row13319 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

def row13320 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

def row13321 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

def row13322 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

def row13323 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

def row13324 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

def row13325 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, -6), (key1067, 6), (key1108, 12), (key1119, -6), (key1146, -6)]

def row13326 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13327 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13328 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13329 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, -6), (key1067, 6), (key1108, 12), (key1119, -6), (key1146, -6)]

def row13330 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13331 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13332 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13333 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13334 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13335 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13336 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13337 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13338 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

def row13339 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

def row13340 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

def row13341 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

def row13342 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

def row13343 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

def row13344 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

def row13345 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, -6), (key2432, 6), (key2466, 12), (key2475, -6), (key2498, -6)]

def row13346 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13347 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13348 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13349 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, -6), (key2432, 6), (key2466, 12), (key2475, -6), (key2498, -6)]

def row13350 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13351 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13352 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13353 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13354 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13355 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13356 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13357 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13358 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

def row13359 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

def row13360 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

def row13361 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

def row13362 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

def row13363 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

def row13364 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

def row13365 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, 6), (key2696, -6), (key2776, -6), (key2799, -6), (key2849, 12)]

def row13366 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, 2), (key2849, -4)]

def row13367 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, 2), (key2849, -4)]

def row13368 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, 2), (key2849, -4)]

def row13369 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, 6), (key2696, -12), (key2799, -6), (key2849, 12)]

def row13370 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 4), (key2799, 2), (key2849, -4)]

def row13371 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 4), (key2799, 2), (key2849, -4)]

def row13372 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 4), (key2799, 2), (key2849, -4)]

def row13373 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, -6), (key2776, 10), (key2799, 2), (key2849, -4)]

def row13374 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, -6), (key2776, 10), (key2799, 2), (key2849, -4)]

def row13375 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, -6), (key2776, 10), (key2799, 2), (key2849, -4)]

def row13376 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 6), (key2776, -2), (key2799, 2), (key2849, -4)]

def row13377 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 6), (key2776, -2), (key2799, 2), (key2849, -4)]

def row13378 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 6), (key2776, -2), (key2799, 2), (key2849, -4)]

def row13379 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

def row13380 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

def row13381 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, -4), (key2799, -2), (key2849, 4)]

def row13382 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, -4), (key2799, -2), (key2849, 4)]

def row13383 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

def row13384 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

def row13385 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13386 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13387 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13388 : Integer.Sparse Key := [(key1090, -12), (key1097, 12), (key1180, 12), (key1182, -12)]

def row13389 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13390 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13391 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13392 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

def row13393 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

def row13394 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

def row13395 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

def row13396 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

def row13397 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

def row13398 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13399 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13400 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13401 : Integer.Sparse Key := [(key1090, -12), (key1097, 12), (key1180, 12), (key1182, -12)]

def row13402 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13403 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13404 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row13405 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13406 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13407 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13408 : Integer.Sparse Key := [(key2, 6), (key6, -6), (key85, -6), (key89, 12), (key150, -6), (key166, -6), (key186, 6)]

def row13409 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13410 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13411 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13412 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

def row13413 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

def row13414 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

def row13415 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

def row13416 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

def row13417 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

def row13418 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13419 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13420 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13421 : Integer.Sparse Key := [(key2, 6), (key6, -6), (key85, -6), (key89, 12), (key150, -6), (key166, -6), (key186, 6)]

def row13422 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13423 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13424 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

def row13425 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13426 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13427 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13428 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1092, 12), (key1163, -6), (key1227, -6), (key1244, 6)]

def row13429 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13430 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13431 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13432 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

def row13433 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

def row13434 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

def row13435 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

def row13436 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

def row13437 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

def row13438 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13439 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13440 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13441 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1092, 12), (key1163, -6), (key1227, -6), (key1244, 6)]

def row13442 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13443 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13444 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

def row13445 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13446 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13447 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13448 : Integer.Sparse Key := [(key992, -6), (key1010, 6), (key1027, -6), (key1066, 6), (key1105, 12), (key1118, -6), (key1145, -6)]

def row13449 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13450 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13451 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13452 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

def row13453 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

def row13454 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

def row13455 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

def row13456 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

def row13457 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, -2), (key1066, 2), (key1105, 4), (key1118, -2), (key1145, -2)]

def row13458 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13459 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13460 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13461 : Integer.Sparse Key := [(key992, -6), (key1010, 6), (key1027, -6), (key1066, 6), (key1105, 12), (key1118, -6), (key1145, -6)]

def row13462 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13463 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13464 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, 2), (key1066, -2), (key1105, -4), (key1118, 2), (key1145, 2)]

def row13465 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

def row13466 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

def row13467 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

def row13468 : Integer.Sparse Key := [(key1, 6), (key4, -6), (key84, -6), (key87, 12), (key148, -6), (key164, -6), (key184, 6)]

def row13469 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

def row13470 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

def row13471 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

def row13472 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

def row13473 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

def row13474 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -4), (key184, 2)]

def row13475 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -4), (key184, 2)]

def row13476 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

def row13477 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key87, 4), (key148, -6), (key164, 2), (key184, 2)]

def row13478 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

def row13479 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

def row13480 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 8), (key164, -4), (key184, -2)]

def row13481 : Integer.Sparse Key := [(key1, 6), (key4, -6), (key84, -6), (key87, 12), (key148, -6), (key164, -6), (key184, 6)]

def row13482 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

def row13483 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

def row13484 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key87, -4), (key148, 2), (key164, 2), (key184, -2)]

def row13485 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1171, -8), (key1175, 8), (key1222, 8), (key1224, -8)]

def row13486 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1171, -8), (key1175, 8), (key1222, 8), (key1224, -8)]

def row13487 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1171, -8), (key1175, 8), (key1222, 8), (key1224, -8)]

def row13488 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13489 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13490 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13491 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13492 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13493 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13494 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13495 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13496 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13497 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13498 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13499 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row13500 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1185, -8), (key1186, 8)]

def row13501 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1185, -8), (key1186, 8)]

def row13502 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1185, -8), (key1186, 8)]

def row13503 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, -4), (key88, -8), (key94, 6), (key97, 6), (key153, 4), (key156, -4), (key161, -8), (key203, 4)]

def row13504 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, -4), (key88, -8), (key94, 6), (key97, 6), (key153, 2), (key156, -4), (key161, -8), (key165, 2), (key187, 4)]

def row13505 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, -4), (key88, -8), (key94, 6), (key97, 6), (key153, 2), (key156, -4), (key161, -8), (key165, 2), (key187, 4)]

def row13506 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

def row13507 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

def row13508 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

def row13509 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

def row13510 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

def row13511 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key11, 2), (key14, -2), (key88, 6), (key92, -2), (key94, -2), (key97, -2), (key153, -2), (key161, 4), (key165, -2)]

def row13512 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

def row13513 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

def row13514 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

def row13515 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

def row13516 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

def row13517 : Integer.Sparse Key := [(key5, 2), (key9, -2), (key92, 4), (key94, -4), (key153, -2), (key165, -2), (key167, 4)]

def row13518 : Integer.Sparse Key := [(key5, -2), (key9, -2), (key11, 4), (key88, -4), (key92, -4), (key94, 4), (key153, 6), (key156, 4), (key165, 6), (key167, -8), (key187, -4)]

def row13519 : Integer.Sparse Key := [(key5, -2), (key9, -2), (key11, 4), (key88, -4), (key92, -4), (key94, 4), (key153, 6), (key156, 4), (key165, 6), (key167, -8), (key187, -4)]

def row13520 : Integer.Sparse Key := [(key5, -2), (key9, -2), (key11, 4), (key88, -4), (key92, -4), (key94, 4), (key153, 6), (key156, 4), (key165, 6), (key167, -8), (key187, -4)]

def row13521 : Integer.Sparse Key := [(key981, 4), (key987, -4), (key1095, -8), (key1101, 12), (key1166, 4), (key1173, -8), (key1229, -4), (key1246, 4)]

def row13522 : Integer.Sparse Key := [(key981, 4), (key987, -4), (key1095, -8), (key1101, 12), (key1166, 4), (key1173, -8), (key1229, -4), (key1246, 4)]

def row13523 : Integer.Sparse Key := [(key981, 4), (key987, -4), (key1095, -8), (key1101, 12), (key1166, 4), (key1173, -8), (key1229, -4), (key1246, 4)]

def row13524 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13525 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13526 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13527 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13528 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13529 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13530 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13531 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13532 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13533 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13534 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13535 : Integer.Sparse Key := [(key1095, 4), (key1101, -4), (key1166, -4), (key1173, 4)]

def row13536 : Integer.Sparse Key := [(key981, -4), (key987, 4), (key1095, -8), (key1101, 4), (key1166, 12), (key1173, -8), (key1229, 4), (key1246, -4)]

def row13537 : Integer.Sparse Key := [(key981, -4), (key987, 4), (key1095, -8), (key1101, 4), (key1166, 12), (key1173, -8), (key1229, 4), (key1246, -4)]

def row13538 : Integer.Sparse Key := [(key981, -4), (key987, 4), (key1095, -8), (key1101, 4), (key1166, 12), (key1173, -8), (key1229, 4), (key1246, -4)]

def row13539 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, -4), (key1072, 4), (key1115, 12), (key1124, -8), (key1151, -8), (key1167, 4)]

def row13540 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, -4), (key1072, 4), (key1115, 12), (key1124, -8), (key1151, -8), (key1167, 4)]

def row13541 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, -4), (key1072, 4), (key1115, 12), (key1124, -8), (key1151, -8), (key1167, 4)]

def row13542 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13543 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13544 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13545 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13546 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13547 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13548 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13549 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13550 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13551 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13552 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13553 : Integer.Sparse Key := [(key1115, -4), (key1124, 4), (key1151, 4), (key1167, -4)]

def row13554 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, -4), (key1115, 4), (key1124, -8), (key1151, -8), (key1167, 12)]

def row13555 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, -4), (key1115, 4), (key1124, -8), (key1151, -8), (key1167, 12)]

def row13556 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, -4), (key1115, 4), (key1124, -8), (key1151, -8), (key1167, 12)]

def row13557 : Integer.Sparse Key := [(key9, 4), (key12, -4), (key92, -8), (key95, 12), (key153, 4), (key157, -8), (key168, -4), (key188, 4)]

def row13558 : Integer.Sparse Key := [(key9, 4), (key12, -4), (key92, -8), (key95, 12), (key153, 4), (key157, -8), (key168, -4), (key188, 4)]

def row13559 : Integer.Sparse Key := [(key9, 4), (key12, -4), (key92, -8), (key95, 12), (key153, 4), (key157, -8), (key168, -4), (key188, 4)]

def row13560 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13561 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13562 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13563 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13564 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13565 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13566 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13567 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13568 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13569 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13570 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13571 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

def row13572 : Integer.Sparse Key := [(key9, -4), (key12, 4), (key92, -8), (key95, 4), (key153, 12), (key157, -8), (key168, 4), (key188, -4)]

def row13573 : Integer.Sparse Key := [(key9, -4), (key12, 4), (key92, -8), (key95, 4), (key153, 12), (key157, -8), (key168, 4), (key188, -4)]

def row13574 : Integer.Sparse Key := [(key9, -4), (key12, 4), (key92, -8), (key95, 4), (key153, 12), (key157, -8), (key168, 4), (key188, -4)]

def row13575 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key158, -8), (key163, 8), (key189, 8), (key192, -8)]

def row13576 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key158, -8), (key163, 8), (key189, 8), (key192, -8)]

def row13577 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key158, -8), (key163, 8), (key189, 8), (key192, -8)]

def row13578 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13579 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13580 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13581 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13582 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13583 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13584 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13585 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13586 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13587 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13588 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13589 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

def row13590 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key93, 8), (key96, -8), (key158, -8), (key163, 8)]

def row13591 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key93, 8), (key96, -8), (key158, -8), (key163, 8)]

def row13592 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key93, 8), (key96, -8), (key158, -8), (key163, 8)]

def row13614 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13615 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13616 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13617 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13618 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13619 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13623 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13624 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13625 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13626 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13627 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13628 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13650 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13651 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13652 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13653 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13654 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13655 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13659 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13660 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13661 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13662 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13663 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13664 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row13686 : Integer.Sparse Key := [(key2370, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2589, -2), (key2762, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

def row13687 : Integer.Sparse Key := [(key2370, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2589, -2), (key2762, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

def row13688 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, -2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2583, -2), (key2589, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

def row13689 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, -2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2583, -2), (key2589, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

def row13690 : Integer.Sparse Key := [(key2370, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, 4), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2589, -2), (key2762, -2), (key2768, -2), (key2845, -2), (key2876, 6)]

def row13691 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, -2), (key2404, 2), (key2435, 2), (key2464, 4), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2583, -2), (key2589, -2), (key2768, -2), (key2845, -2), (key2876, 6)]

def row13695 : Integer.Sparse Key := [(key2370, -2), (key2388, 2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, -2), (key2839, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13696 : Integer.Sparse Key := [(key2370, -2), (key2388, 2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, -2), (key2839, -2)]

def row13697 : Integer.Sparse Key := [(key2388, 2), (key2398, -2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, -2), (key2839, -2)]

def row13698 : Integer.Sparse Key := [(key2388, 2), (key2398, -2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, -2), (key2839, -2)]

def row13699 : Integer.Sparse Key := [(key2370, -2), (key2388, 2), (key2435, 2), (key2464, 4), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, -2)]

def row13700 : Integer.Sparse Key := [(key2388, 2), (key2398, -2), (key2435, 2), (key2464, 4), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, -2)]

def row13722 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13723 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13724 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13725 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13726 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13727 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13731 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13732 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13733 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13734 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13735 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13736 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

def row13758 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13759 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13760 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13761 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13762 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13763 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13767 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13768 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13769 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13770 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13771 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13772 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row13794 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13795 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13796 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13797 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13798 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13799 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13803 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13804 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13805 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13806 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13807 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

def row13808 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13830 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13831 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13832 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13833 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13834 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13835 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13839 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13840 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13841 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13842 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13843 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13844 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13845 : Integer.Sparse Key := [(key2420, 4), (key2427, -8), (key2438, 4)]

def row13846 : Integer.Sparse Key := [(key2420, 4), (key2427, -8), (key2438, 4)]

def row13847 : Integer.Sparse Key := [(key2420, 4), (key2427, -8), (key2438, 4)]

def row13848 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row13849 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row13850 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row13851 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row13852 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row13853 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row13854 : Integer.Sparse Key := [(key2420, 12), (key2427, -24), (key2438, 12)]

def row13855 : Integer.Sparse Key := [(key1050, -4), (key1058, 4), (key1136, 4), (key1138, -4)]

def row13856 : Integer.Sparse Key := [(key1050, -4), (key1058, 4), (key1136, 4), (key1138, -4)]

def row13857 : Integer.Sparse Key := [(key1050, -4), (key1058, 4), (key1136, 4), (key1138, -4)]

def row13858 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

def row13859 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

def row13860 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

def row13861 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

def row13862 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

def row13863 : Integer.Sparse Key := [(key1050, 4), (key1058, -4), (key1136, -4), (key1138, 4)]

def row13864 : Integer.Sparse Key := [(key1050, -12), (key1058, 12), (key1136, 12), (key1138, -12)]

def row13865 : Integer.Sparse Key := [(key2416, -4), (key2423, 4), (key2489, 4), (key2491, -4)]

def row13866 : Integer.Sparse Key := [(key2416, -4), (key2423, 4), (key2489, 4), (key2491, -4)]

def row13867 : Integer.Sparse Key := [(key2416, -4), (key2423, 4), (key2489, 4), (key2491, -4)]

def row13868 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

def row13869 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

def row13870 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

def row13871 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

def row13872 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

def row13873 : Integer.Sparse Key := [(key2416, 4), (key2423, -4), (key2489, -4), (key2491, 4)]

def row13874 : Integer.Sparse Key := [(key2416, -12), (key2423, 12), (key2489, 12), (key2491, -12)]

def row13875 : Integer.Sparse Key := [(key2677, 10), (key2708, -4), (key3045, -6), (key3094, -4), (key3122, 4)]

def row13876 : Integer.Sparse Key := [(key2677, 10), (key2708, -4), (key3045, -6), (key3094, -4), (key3122, 4)]

def row13877 : Integer.Sparse Key := [(key2677, 10), (key2708, -4), (key3045, -6), (key3094, -4), (key3122, 4)]

def row13878 : Integer.Sparse Key := [(key2677, -6), (key2708, 4), (key2811, 6), (key3045, 2), (key3094, -2), (key3122, -4)]

def row13879 : Integer.Sparse Key := [(key2677, -6), (key2708, 4), (key2811, 6), (key3045, 2), (key3094, -2), (key3122, -4)]

def row13880 : Integer.Sparse Key := [(key2677, -6), (key2708, 4), (key2811, 4), (key3045, 2), (key3122, -4)]

def row13881 : Integer.Sparse Key := [(key2677, -6), (key2811, 2), (key2861, -4), (key3045, 2), (key3059, 4), (key3094, 2)]

def row13882 : Integer.Sparse Key := [(key2677, -6), (key2811, 2), (key2861, -4), (key3045, 2), (key3059, 4), (key3094, 2)]

def row13883 : Integer.Sparse Key := [(key2677, -6), (key2861, -4), (key3045, 2), (key3059, 4), (key3094, 4)]

def row13884 : Integer.Sparse Key := [(key2677, 6), (key2708, -12), (key2811, -12), (key2861, 12), (key3045, 6)]

def row13885 : Integer.Sparse Key := [(key1047, -4), (key1057, 4), (key1133, 4), (key1137, -4)]

def row13886 : Integer.Sparse Key := [(key1047, -4), (key1057, 4), (key1133, 4), (key1137, -4)]

def row13887 : Integer.Sparse Key := [(key1047, -4), (key1057, 4), (key1133, 4), (key1137, -4)]

def row13888 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

def row13889 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

def row13890 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

def row13891 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

def row13892 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

def row13893 : Integer.Sparse Key := [(key1047, 4), (key1057, -4), (key1133, -4), (key1137, 4)]

def row13894 : Integer.Sparse Key := [(key1047, -12), (key1057, 12), (key1133, 12), (key1137, -12)]

def row13895 : Integer.Sparse Key := [(key1055, 4), (key1063, -8), (key1074, 4)]

def row13896 : Integer.Sparse Key := [(key1055, 4), (key1063, -8), (key1074, 4)]

def row13897 : Integer.Sparse Key := [(key1055, 4), (key1063, -8), (key1074, 4)]

def row13898 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

def row13899 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

def row13900 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

def row13901 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

def row13902 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

def row13903 : Integer.Sparse Key := [(key1055, -4), (key1063, 8), (key1074, -4)]

def row13904 : Integer.Sparse Key := [(key1055, 12), (key1063, -24), (key1074, 12)]

def row13905 : Integer.Sparse Key := [(key2681, -4), (key2688, 4), (key2712, 4), (key2714, -4)]

def row13906 : Integer.Sparse Key := [(key2681, -4), (key2688, 4), (key2712, 4), (key2714, -4)]

def row13907 : Integer.Sparse Key := [(key2681, -4), (key2688, 4), (key2712, 4), (key2714, -4)]

def row13908 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

def row13909 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

def row13910 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

def row13911 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

def row13912 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

def row13913 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, -4), (key2714, 4)]

def row13914 : Integer.Sparse Key := [(key2681, -12), (key2688, 12), (key2712, 12), (key2714, -12)]

def row13915 : Integer.Sparse Key := [(key3079, 4), (key3084, -8), (key3099, 4)]

def row13916 : Integer.Sparse Key := [(key3079, 4), (key3084, -8), (key3099, 4)]

def row13917 : Integer.Sparse Key := [(key3079, 4), (key3084, -8), (key3099, 4)]

def row13918 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

def row13919 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

def row13920 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

def row13921 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

def row13922 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

def row13923 : Integer.Sparse Key := [(key3079, -4), (key3084, 8), (key3099, -4)]

def row13924 : Integer.Sparse Key := [(key3079, 12), (key3084, -24), (key3099, 12)]

def row13925 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13926 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13927 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13928 : Integer.Sparse Key := [(key2456, -12), (key2459, 12), (key2517, 12), (key2520, -12)]

def row13929 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13930 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13931 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13932 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

def row13933 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

def row13934 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

def row13935 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

def row13936 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

def row13937 : Integer.Sparse Key := [(key2456, -4), (key2459, 4), (key2517, 4), (key2520, -4)]

def row13938 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13939 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13940 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13941 : Integer.Sparse Key := [(key2456, -12), (key2459, 12), (key2517, 12), (key2520, -12)]

def row13942 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13943 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13944 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row13945 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13946 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13947 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13948 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1091, 12), (key1162, -6), (key1181, -6), (key1218, 6)]

def row13949 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13950 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13951 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13952 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

def row13953 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

def row13954 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

def row13955 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

def row13956 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

def row13957 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

def row13958 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13959 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13960 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13961 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1091, 12), (key1162, -6), (key1181, -6), (key1218, 6)]

def row13962 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13963 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13964 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

def row13965 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13966 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13967 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13968 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2453, 12), (key2514, -6), (key2529, -6), (key2559, 6)]

def row13969 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13970 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13971 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13972 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

def row13973 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

def row13974 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

def row13975 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

def row13976 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

def row13977 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

def row13978 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13979 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13980 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13981 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2453, 12), (key2514, -6), (key2529, -6), (key2559, 6)]

def row13982 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13983 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13984 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

def row13985 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13986 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13987 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13988 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, -6), (key2431, 6), (key2463, 12), (key2474, -6), (key2497, -6)]

def row13989 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13990 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13991 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13992 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

def row13993 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

def row13994 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

def row13995 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

def row13996 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

def row13997 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

def row13998 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row13999 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row14000 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row14001 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, -6), (key2431, 6), (key2463, 12), (key2474, -6), (key2497, -6)]

def row14002 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row14003 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row14004 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

def row14005 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14006 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14007 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14008 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1089, 12), (key1161, -6), (key1179, -6), (key1217, 6)]

def row14009 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14010 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14011 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14012 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

def row14013 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

def row14014 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

def row14015 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

def row14016 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

def row14017 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

def row14018 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14019 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14020 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14021 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1089, 12), (key1161, -6), (key1179, -6), (key1217, 6)]

def row14022 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14023 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14024 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

def row14025 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14026 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14027 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14028 : Integer.Sparse Key := [(key1095, -12), (key1099, 12), (key1166, 12), (key1170, -12)]

def row14029 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14030 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14031 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14032 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

def row14033 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

def row14034 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

def row14035 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

def row14036 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

def row14037 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

def row14038 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14039 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14040 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14041 : Integer.Sparse Key := [(key1095, -12), (key1099, 12), (key1166, 12), (key1170, -12)]

def row14042 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14043 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14044 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

def row14045 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14046 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14047 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14048 : Integer.Sparse Key := [(key2763, 6), (key2767, -6), (key2840, -6), (key2844, 12), (key2875, -6), (key2888, -6), (key2909, 6)]

def row14049 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14050 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14051 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14052 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

def row14053 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

def row14054 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

def row14055 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

def row14056 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

def row14057 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

def row14058 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14059 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14060 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14061 : Integer.Sparse Key := [(key2763, 6), (key2767, -6), (key2840, -6), (key2844, 12), (key2875, -6), (key2888, -6), (key2909, 6)]

def row14062 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14063 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14064 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

def row14065 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14066 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14067 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14068 : Integer.Sparse Key := [(key2413, -12), (key2422, 12), (key2486, 12), (key2490, -12)]

def row14069 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14070 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14071 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14072 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

def row14073 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

def row14074 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

def row14075 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

def row14076 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

def row14077 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

def row14078 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14079 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14080 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14081 : Integer.Sparse Key := [(key2413, -12), (key2422, 12), (key2486, 12), (key2490, -12)]

def row14082 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14083 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14084 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

def row14085 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

def row14086 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

def row14087 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

def row14088 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2451, 12), (key2513, -6), (key2527, -6), (key2558, 6)]

def row14089 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

def row14090 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

def row14091 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

def row14092 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

def row14093 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

def row14094 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -4), (key2558, 2)]

def row14095 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -4), (key2558, 2)]

def row14096 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

def row14097 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2451, 4), (key2513, -6), (key2527, 2), (key2558, 2)]

def row14098 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

def row14099 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

def row14100 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 8), (key2527, -4), (key2558, -2)]

def row14101 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2451, 12), (key2513, -6), (key2527, -6), (key2558, 6)]

def row14102 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

def row14103 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

def row14104 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2451, -4), (key2513, 2), (key2527, 2), (key2558, -2)]

def row14105 : Integer.Sparse Key := [(key1975, 4), (key1980, -8), (key1996, 4)]

def row14106 : Integer.Sparse Key := [(key1975, 4), (key1980, -8), (key1996, 4)]

def row14107 : Integer.Sparse Key := [(key1975, 4), (key1980, -8), (key1996, 4)]

def row14108 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row14109 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row14110 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row14111 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row14112 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row14113 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row14114 : Integer.Sparse Key := [(key1975, 12), (key1980, -24), (key1996, 12)]

def row14115 : Integer.Sparse Key := [(key55, -4), (key61, 4), (key123, 4), (key126, -4)]

def row14116 : Integer.Sparse Key := [(key55, -4), (key61, 4), (key123, 4), (key126, -4)]

def row14117 : Integer.Sparse Key := [(key55, -4), (key61, 4), (key123, 4), (key126, -4)]

def row14118 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

def row14119 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

def row14120 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

def row14121 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

def row14122 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

def row14123 : Integer.Sparse Key := [(key55, 4), (key61, -4), (key123, -4), (key126, 4)]

def row14124 : Integer.Sparse Key := [(key55, -12), (key61, 12), (key123, 12), (key126, -12)]

def row14125 : Integer.Sparse Key := [(key1972, -4), (key1984, 4), (key2208, 4), (key2225, -4)]

def row14126 : Integer.Sparse Key := [(key1972, -4), (key1984, 4), (key2208, 4), (key2225, -4)]

def row14127 : Integer.Sparse Key := [(key1972, -4), (key1984, 4), (key2208, 4), (key2225, -4)]

def row14128 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

def row14129 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

def row14130 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

def row14131 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

def row14132 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

def row14133 : Integer.Sparse Key := [(key1972, 4), (key1984, -4), (key2208, -4), (key2225, 4)]

def row14134 : Integer.Sparse Key := [(key1972, -12), (key1984, 12), (key2208, 12), (key2225, -12)]

def row14135 : Integer.Sparse Key := [(key2010, 4), (key2039, -4), (key2124, -4), (key2211, 4)]

def row14136 : Integer.Sparse Key := [(key2010, 4), (key2039, -4), (key2124, -4), (key2211, 4)]

def row14137 : Integer.Sparse Key := [(key2010, 4), (key2039, -4), (key2124, -4), (key2211, 4)]

def row14138 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

def row14139 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

def row14140 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

def row14141 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

def row14142 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

def row14143 : Integer.Sparse Key := [(key2010, -4), (key2039, 4), (key2124, 4), (key2211, -4)]

def row14144 : Integer.Sparse Key := [(key2010, 12), (key2039, -12), (key2124, -12), (key2211, 12)]

def row14145 : Integer.Sparse Key := [(key53, -4), (key59, 4), (key121, 4), (key124, -4)]

def row14146 : Integer.Sparse Key := [(key53, -4), (key59, 4), (key121, 4), (key124, -4)]

def row14147 : Integer.Sparse Key := [(key53, -4), (key59, 4), (key121, 4), (key124, -4)]

def row14148 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

def row14149 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

def row14150 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

def row14151 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

def row14152 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

def row14153 : Integer.Sparse Key := [(key53, 4), (key59, -4), (key121, -4), (key124, 4)]

def row14154 : Integer.Sparse Key := [(key53, -12), (key59, 12), (key121, 12), (key124, -12)]

def row14155 : Integer.Sparse Key := [(key57, 4), (key64, -8), (key77, 4)]

def row14156 : Integer.Sparse Key := [(key57, 4), (key64, -8), (key77, 4)]

def row14157 : Integer.Sparse Key := [(key57, 4), (key64, -8), (key77, 4)]

def row14158 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

def row14159 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

def row14160 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

def row14161 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

def row14162 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

def row14163 : Integer.Sparse Key := [(key57, -4), (key64, 8), (key77, -4)]

def row14164 : Integer.Sparse Key := [(key57, 12), (key64, -24), (key77, 12)]

def row14165 : Integer.Sparse Key := [(key2012, -4), (key2025, 4), (key2041, 4), (key2054, -4)]

def row14166 : Integer.Sparse Key := [(key2012, -4), (key2025, 4), (key2041, 4), (key2054, -4)]

def row14167 : Integer.Sparse Key := [(key2012, -4), (key2025, 4), (key2041, 4), (key2054, -4)]

def row14168 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

def row14169 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

def row14170 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

def row14171 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

def row14172 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

def row14173 : Integer.Sparse Key := [(key2012, 4), (key2025, -4), (key2041, -4), (key2054, 4)]

def row14174 : Integer.Sparse Key := [(key2012, -12), (key2025, 12), (key2041, 12), (key2054, -12)]

def row14175 : Integer.Sparse Key := [(key2100, 4), (key2105, -8), (key2130, 4)]

def row14176 : Integer.Sparse Key := [(key2100, 4), (key2105, -8), (key2130, 4)]

def row14177 : Integer.Sparse Key := [(key2100, 4), (key2105, -8), (key2130, 4)]

def row14178 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

def row14179 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

def row14180 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

def row14181 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

def row14182 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

def row14183 : Integer.Sparse Key := [(key2100, -4), (key2105, 8), (key2130, -4)]

def row14184 : Integer.Sparse Key := [(key2100, 12), (key2105, -24), (key2130, 12)]

def row14185 : Integer.Sparse Key := [(key1971, -4), (key1979, 4), (key2207, 4), (key2216, -4)]

def row14186 : Integer.Sparse Key := [(key1971, -4), (key1979, 4), (key2207, 4), (key2216, -4)]

def row14187 : Integer.Sparse Key := [(key1971, -4), (key1979, 4), (key2207, 4), (key2216, -4)]

def row14188 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

def row14189 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

def row14190 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

def row14191 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

def row14192 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

def row14193 : Integer.Sparse Key := [(key1971, 4), (key1979, -4), (key2207, -4), (key2216, 4)]

def row14194 : Integer.Sparse Key := [(key1971, -12), (key1979, 12), (key2207, 12), (key2216, -12)]

def row14195 : Integer.Sparse Key := [(key756, 4), (key760, -8), (key787, 4)]

def row14196 : Integer.Sparse Key := [(key756, 4), (key760, -8), (key787, 4)]

def row14197 : Integer.Sparse Key := [(key756, 4), (key760, -8), (key787, 4)]

def row14198 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

def row14199 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

def row14200 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

def row14201 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

def row14202 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

def row14203 : Integer.Sparse Key := [(key756, -4), (key760, 8), (key787, -4)]

def row14204 : Integer.Sparse Key := [(key756, 12), (key760, -24), (key787, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15889 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15890 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15891 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15892 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15893 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15894 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15895 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15896 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16095 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16096 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16097 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16098 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16099 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16100 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16101 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16102 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16103 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16104 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16105 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16106 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16107 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 4), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16108 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 4), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16109 : Integer.Sparse Key := [(key2393, 4), (key2407, -2), (key2441, 2), (key2565, 4), (key2592, -2), (key2595, 2), (key2602, -2), (key2603, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16110 : Integer.Sparse Key := [(key2393, 4), (key2407, -2), (key2441, 2), (key2565, 4), (key2592, -2), (key2595, 2), (key2602, -2), (key2603, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16111 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 2), (key2544, -2), (key2555, -2), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2914, -2), (key2934, -2), (key2993, -2)]

def row16112 : Integer.Sparse Key := [(key2393, 2), (key2407, -2), (key2441, 2), (key2544, -2), (key2555, -2), (key2565, 4), (key2592, -2), (key2595, 2), (key2603, -2), (key2774, 2), (key2882, 4), (key2914, -2), (key2934, -2), (key2993, -2)]

def row16113 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16114 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16115 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16116 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16117 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16118 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16119 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 4), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2933, -2), (key2991, -2)]

def row16120 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 4), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2933, -2), (key2991, -2)]

def row16121 : Integer.Sparse Key := [(key2382, -2), (key2393, 4), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2602, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2991, -2)]

def row16122 : Integer.Sparse Key := [(key2382, -2), (key2393, 4), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2602, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2991, -2)]

def row16123 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2544, -2), (key2545, -2), (key2555, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4)]

def row16124 : Integer.Sparse Key := [(key2382, -2), (key2393, 2), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2544, -2), (key2545, -2), (key2555, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

def row16125 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4), (key2848, 4)]

def row16126 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4), (key2848, 4)]

def row16127 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4), (key2848, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16128 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4), (key2848, 4)]

def row16129 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2473, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4)]

def row16130 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2473, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4)]

def row16131 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16132 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16133 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16134 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16135 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16136 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16137 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16138 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16139 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16140 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16141 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16142 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16143 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16144 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16145 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16146 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16147 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16148 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16149 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16150 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16151 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16152 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16153 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16154 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16155 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16156 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16157 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16158 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16159 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16160 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16161 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16162 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16163 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16164 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16165 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16166 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16167 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

def row16168 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

def row16169 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

def row16170 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16171 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16172 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16173 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16174 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16175 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16176 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

def row16177 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

def row16178 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

def row16179 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16180 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16181 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16182 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16183 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16184 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16185 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16186 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16187 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16188 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16189 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16190 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16191 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16192 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16193 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16194 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16195 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16196 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16197 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16198 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16199 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16200 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16201 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16202 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16203 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16204 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16205 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16206 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16207 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16208 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16209 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16210 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16211 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16212 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16213 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16214 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16215 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16216 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16217 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16218 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16219 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16220 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16221 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16222 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16223 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16224 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16225 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16226 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16227 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16228 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16229 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16230 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16231 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16232 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16233 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16234 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16235 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16236 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16237 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16238 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16239 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16240 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16241 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16242 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16243 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16244 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16245 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16246 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16247 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16248 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16249 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16250 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16251 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16252 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16253 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16254 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16255 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16256 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16257 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16258 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16259 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16260 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16261 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16262 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16263 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16264 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16265 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16266 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16267 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16268 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16269 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16270 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16271 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16272 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16273 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16274 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16275 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16276 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16277 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16278 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16279 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16280 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16281 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16282 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16283 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16284 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16285 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16286 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16287 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16288 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16289 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16290 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16291 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16292 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16293 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16294 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16295 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16296 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16297 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16298 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16299 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16300 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16301 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16302 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16303 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16304 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16305 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16306 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16307 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16308 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16309 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16310 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16311 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -2), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key3017, -2), (key3026, -2), (key3030, 4)]

def row16312 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key2948, -1), (key2960, -2), (key3026, -2), (key3030, 4)]

def row16313 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key2948, -1), (key2960, -2), (key3026, -2), (key3030, 4)]

def row16314 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16315 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16316 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16317 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16318 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16319 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16320 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -2), (key2835, 4), (key2885, -2), (key2927, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3017, -2), (key3030, 4)]

def row16321 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2885, -2), (key2927, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3030, 4)]

def row16322 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2885, -2), (key2927, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3030, 4)]

def row16323 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16324 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16325 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16326 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16327 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16328 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16329 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16330 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16331 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16332 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16333 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16334 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16335 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16336 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16337 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16338 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16339 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16340 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16341 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16342 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16343 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16344 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16345 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16346 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16347 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16348 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16349 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16350 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16351 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16352 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16353 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16354 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16355 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16356 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16357 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16358 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16359 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16360 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16361 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16362 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16363 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16364 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16365 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16366 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16367 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16368 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16369 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16370 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16371 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16372 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16373 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16374 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16375 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16376 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16377 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16378 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16379 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16380 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16381 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16382 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16383 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16384 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16385 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16386 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16387 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16388 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16389 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16390 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16391 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16392 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16393 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16394 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16395 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16396 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16397 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16398 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16399 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16400 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16401 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16402 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16403 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16404 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16405 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16406 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16407 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16408 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16409 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16410 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16411 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16412 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16413 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16414 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16415 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16416 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16417 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16418 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16419 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16420 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16421 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16422 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16423 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16424 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16425 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16426 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16427 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16428 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16429 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16430 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16431 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16432 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16433 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16434 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16435 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16436 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16437 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16438 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16439 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16440 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16441 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16442 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16443 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16444 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16445 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16446 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16447 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16448 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16449 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16450 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16451 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16452 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16453 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16454 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16455 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16456 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16457 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16458 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16459 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16460 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16461 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16462 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16463 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16464 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16465 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16466 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16467 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16468 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16469 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16470 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16471 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16472 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16473 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16474 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16475 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16476 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16477 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16478 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16479 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16480 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16481 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16482 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16483 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16484 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16485 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16486 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16487 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16488 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16489 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16490 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16491 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16492 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16493 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16494 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16495 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16496 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16497 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16498 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16499 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16500 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16501 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16502 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16503 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16504 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16505 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16506 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16507 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16508 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16509 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16510 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16511 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16512 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16513 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16514 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16515 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16516 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16517 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16518 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16519 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16520 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16521 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16522 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16523 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16524 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16525 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16526 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16527 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

def row16528 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

def row16529 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

def row16530 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16531 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16532 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16533 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16534 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16535 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16536 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

def row16537 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

def row16538 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

def row16539 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2933, -1), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16540 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2933, -1), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16541 : Integer.Sparse Key := [(key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2592, -1), (key2595, 3), (key2602, -1), (key2603, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16542 : Integer.Sparse Key := [(key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2592, -1), (key2595, 3), (key2602, -1), (key2603, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16543 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 1), (key2555, 1), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2914, -3), (key2934, -1), (key2993, -3)]

def row16544 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 1), (key2555, 1), (key2565, 2), (key2592, -1), (key2595, 3), (key2603, -1), (key2774, 3), (key2882, 2), (key2914, -3), (key2934, -1), (key2993, -3)]

def row16545 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16546 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16547 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16548 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16549 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16550 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16551 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2933, -1), (key2991, -1)]

def row16552 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2933, -1), (key2991, -1)]

def row16553 : Integer.Sparse Key := [(key2382, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2602, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2991, -1)]

def row16554 : Integer.Sparse Key := [(key2382, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2602, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2991, -1)]

def row16555 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, -3), (key2555, 1), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4)]

def row16556 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, -3), (key2555, 1), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

def row16557 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4), (key2848, 4)]

def row16558 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4), (key2848, 4)]

def row16559 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4), (key2848, 4)]

def row16560 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4), (key2848, 4)]

def row16561 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2473, 4), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4)]

def row16562 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2473, 4), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4)]

def row16563 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -2), (key2831, 2), (key2860, -2), (key2870, -2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row16564 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, -2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row16565 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, -2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row16566 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16567 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16568 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16569 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16570 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16571 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16572 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -2), (key2831, 2), (key2893, -2), (key2904, -2), (key2972, -2), (key2983, -2), (key3017, -2), (key3030, 4)]

def row16573 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2893, -2), (key2904, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2983, -2), (key3030, 4)]

def row16574 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2893, -2), (key2904, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2983, -2), (key3030, 4)]

def row16575 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16576 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16577 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16578 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16579 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16580 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16581 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16582 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16583 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16584 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16585 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16586 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16587 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16588 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16589 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16590 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16591 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16592 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16593 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16594 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16595 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16596 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16597 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16598 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16599 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 2), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key3017, 2), (key3023, -2), (key3026, 2)]

def row16600 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 1), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key2948, 1), (key2960, 2), (key3023, -2), (key3026, 2)]

def row16601 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 1), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key2948, 1), (key2960, 2), (key3023, -2), (key3026, 2)]

def row16602 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16603 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16604 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16605 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16606 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16607 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16608 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 2), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2972, 2), (key2976, -4), (key2983, 2), (key3017, 2)]

def row16609 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 1), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2948, 1), (key2960, 2), (key2972, 2), (key2976, -4), (key2983, 2)]

def row16610 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 1), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2948, 1), (key2960, 2), (key2972, 2), (key2976, -4), (key2983, 2)]

def row16611 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16612 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16613 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16614 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16615 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16616 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16617 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16618 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16619 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16620 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16621 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16622 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16623 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16624 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16625 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16626 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16627 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16628 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16629 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16630 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16631 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16632 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16633 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16634 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16635 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16636 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16637 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16638 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16639 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16640 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16641 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16642 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16643 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16644 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16645 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16646 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16647 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16648 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16649 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16650 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16651 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16652 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16653 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16654 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16655 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16656 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16657 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16658 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16659 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16660 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16661 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16662 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16663 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16664 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16665 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16666 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16667 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16668 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16669 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16670 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16671 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

def row16672 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

def row16673 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

def row16674 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16675 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16676 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2899, 1), (key2906, 2), (key2915, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16677 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2899, 1), (key2906, 2), (key2915, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16678 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16679 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16680 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

def row16681 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

def row16682 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

def row16683 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16684 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16685 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16686 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16687 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16688 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16689 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16690 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16691 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16692 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16693 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16694 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16695 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16696 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16697 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2751, -2), (key2797, 2), (key2833, 2), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16698 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2751, -2), (key2797, 2), (key2833, 2), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16699 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16700 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16701 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16702 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16703 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 4), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16704 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 4), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16705 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16706 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16707 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

def row16708 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

def row16709 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

def row16710 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16711 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16712 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16713 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16714 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16715 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16716 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16717 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16718 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16719 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16720 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16721 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16722 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

def row16723 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

def row16724 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

def row16725 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

def row16726 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

def row16727 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

def row16728 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16729 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16730 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16731 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16732 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16733 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16734 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16735 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16736 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16737 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16738 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16739 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16740 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

def row16741 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

def row16742 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

def row16743 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

def row16744 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

def row16745 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

def row16746 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16747 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16748 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16749 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16750 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16751 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16752 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16753 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16754 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16755 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16756 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16757 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16758 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

def row16759 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

def row16760 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

def row16761 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

def row16762 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

def row16763 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

def row16764 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16765 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16766 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16767 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16768 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16769 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16770 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16771 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16772 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16773 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16774 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16775 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16776 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

def row16777 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

def row16778 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

def row16779 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

def row16780 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

def row16781 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

def row16782 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16783 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16784 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16785 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16786 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16787 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16788 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16789 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16790 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16791 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16792 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16793 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16794 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

def row16795 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

def row16796 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

def row16797 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

def row16798 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

def row16799 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

def row16800 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16801 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16802 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16803 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16804 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16805 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16806 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16807 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16808 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16809 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16810 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16811 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16812 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

def row16813 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

def row16814 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

def row16815 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

def row16816 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

def row16817 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

def row16818 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16819 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16820 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16821 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16822 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16823 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16824 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16825 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16826 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16827 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16828 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16829 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16830 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

def row16831 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

def row16832 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

def row16833 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

def row16834 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

def row16835 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

def row16836 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16837 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16838 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16839 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16840 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16841 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16842 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16843 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16844 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16845 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16846 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16847 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16848 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

def row16849 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

def row16850 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

def row16851 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

def row16852 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

def row16853 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

def row16854 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16855 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16856 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16857 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16858 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16859 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16860 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16861 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16862 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16863 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16864 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16865 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16866 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

def row16867 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

def row16868 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

def row16869 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

def row16870 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

def row16871 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

def row16872 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16873 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16874 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16875 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16876 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16877 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16878 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16879 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16880 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16881 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16882 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16883 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16884 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

def row16885 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

def row16886 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

def row16887 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

def row16888 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

def row16889 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

def row16890 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16891 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16892 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16893 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16894 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16895 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16896 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16897 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16898 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16899 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16900 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16901 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16902 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

def row16903 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

def row16904 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

def row16905 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

def row16906 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

def row16907 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

def row16908 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16909 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16910 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16911 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16912 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16913 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16914 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16915 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16916 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16917 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16918 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16919 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16920 : Integer.Sparse Key := [(key360, 2), (key366, 2), (key529, -4), (key531, 6), (key537, -8), (key731, 2), (key733, -8), (key750, 2), (key867, 6), (key881, -4), (key938, 4)]

def row16921 : Integer.Sparse Key := [(key360, 2), (key366, 2), (key529, -4), (key531, 6), (key537, -8), (key731, 2), (key733, -8), (key750, 2), (key867, 6), (key881, -4), (key938, 4)]

def row16922 : Integer.Sparse Key := [(key360, 2), (key366, 4), (key529, -4), (key531, 6), (key537, -8), (key676, 4), (key731, 2), (key733, -8), (key867, 6), (key881, -4)]

def row16923 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

def row16924 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

def row16925 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

def row16926 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16927 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16928 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16929 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16930 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16931 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16932 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16933 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16934 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16935 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16936 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16937 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16938 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

def row16939 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

def row16940 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

def row16941 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

def row16942 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

def row16943 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

def row16944 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16945 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16946 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16947 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16948 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16949 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16950 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16951 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16952 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16953 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16954 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16955 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16956 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

def row16957 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

def row16958 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

def row16959 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

def row16960 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

def row16961 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

def row16962 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16963 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16964 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16965 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16966 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16967 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16968 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16969 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16970 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16971 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16972 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16973 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16974 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

def row16975 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

def row16976 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

def row16977 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

def row16978 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

def row16979 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

def row16980 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16981 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16982 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16983 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16984 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16985 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16986 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16987 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16988 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16989 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16990 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16991 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16992 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

def row16993 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

def row16994 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

def row16995 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

def row16996 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

def row16997 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

def row16998 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row16999 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17000 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17001 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17002 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17003 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17004 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17005 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17006 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17007 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17008 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17009 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17010 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

def row17011 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

def row17012 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

def row17013 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

def row17014 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

def row17015 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

def row17016 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17017 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17018 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17019 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17020 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17021 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17022 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17023 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17024 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17025 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17026 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17027 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17028 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

def row17029 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

def row17030 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

def row17031 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17032 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17033 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17034 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17035 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17036 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17037 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17038 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17039 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17040 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17041 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17042 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17043 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17044 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17045 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17046 : Integer.Sparse Key := [(key1976, 12), (key1981, -12), (key1983, -12), (key1997, 12)]

def row17047 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17048 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17049 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17050 : Integer.Sparse Key := [(key1976, 12), (key1981, -12), (key1983, -12), (key1997, 12)]

def row17051 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17052 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17053 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17054 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17055 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17056 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17057 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17058 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17059 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17060 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17061 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17062 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17063 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

def row17064 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

def row17065 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

def row17066 : Integer.Sparse Key := [(key54, -2), (key63, 12), (key122, 6), (key128, -6), (key199, -6), (key693, -4), (key697, -6), (key848, 6)]

def row17067 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

def row17068 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

def row17069 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

def row17070 : Integer.Sparse Key := [(key54, -2), (key56, -6), (key63, 12), (key122, 6), (key128, -6), (key198, 6), (key199, -6), (key693, -4)]

def row17071 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17072 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17073 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17074 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17075 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17076 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17077 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17078 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17079 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17080 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17081 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17082 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17083 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17084 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17085 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17086 : Integer.Sparse Key := [(key1973, -6), (key1978, -6), (key1985, 12), (key2209, 6), (key2215, 6), (key2226, -6), (key2230, -6)]

def row17087 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17088 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17089 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17090 : Integer.Sparse Key := [(key1973, -6), (key1978, -6), (key1985, 12), (key2209, 6), (key2215, 6), (key2226, -6), (key2230, -6)]

def row17091 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17092 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17093 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17094 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17095 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17096 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17097 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17098 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17099 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17100 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17101 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17102 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17103 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17104 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17105 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17106 : Integer.Sparse Key := [(key2015, 12), (key2044, -6), (key2045, -6), (key2129, -6), (key2132, -6), (key2212, 6), (key2213, 6)]

def row17107 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17108 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17109 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17110 : Integer.Sparse Key := [(key2015, 12), (key2044, -6), (key2045, -6), (key2129, -6), (key2132, -6), (key2212, 6), (key2213, 6)]

def row17111 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17112 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17113 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17114 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17115 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17116 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17117 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17118 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17119 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17120 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17121 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17122 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17123 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17124 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17125 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17126 : Integer.Sparse Key := [(key694, -6), (key696, -6), (key699, 12), (key846, 6), (key847, 6), (key850, -6), (key852, -6)]

def row17127 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17128 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17129 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17130 : Integer.Sparse Key := [(key694, -6), (key696, -6), (key699, 12), (key846, 6), (key847, 6), (key850, -6), (key852, -6)]

def row17131 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17132 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17133 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17134 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17135 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17136 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17137 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17138 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17139 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17140 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17141 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17142 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17143 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17144 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17145 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17146 : Integer.Sparse Key := [(key65, -12), (key82, 12), (key695, 12), (key700, -12)]

def row17147 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

def row17148 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

def row17149 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

def row17150 : Integer.Sparse Key := [(key58, 12), (key65, -12), (key68, -12), (key82, 12)]

def row17151 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17152 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17153 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17154 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17155 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17156 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17157 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17158 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17159 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17160 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17161 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17162 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17163 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17164 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17165 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17166 : Integer.Sparse Key := [(key2013, -6), (key2019, -6), (key2026, 12), (key2042, 6), (key2047, 6), (key2055, -6), (key2056, -6)]

def row17167 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17168 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17169 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17170 : Integer.Sparse Key := [(key2013, -6), (key2019, -6), (key2026, 12), (key2042, 6), (key2047, 6), (key2055, -6), (key2056, -6)]

def row17171 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17172 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17173 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17174 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17175 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17176 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17177 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17178 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17179 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17180 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17181 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17182 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17183 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17184 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17185 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17186 : Integer.Sparse Key := [(key2103, 12), (key2108, -12), (key2109, -12), (key2131, 12)]

def row17187 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17188 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17189 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17190 : Integer.Sparse Key := [(key2103, 12), (key2108, -12), (key2109, -12), (key2131, 12)]

def row17191 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17192 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17193 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17194 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17195 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17196 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17197 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17198 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17199 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17200 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17201 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17202 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17203 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17204 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17205 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17206 : Integer.Sparse Key := [(key1974, -6), (key1977, -6), (key1982, 12), (key2210, 6), (key2214, 6), (key2219, -6), (key2223, -6)]

def row17207 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17208 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17209 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17210 : Integer.Sparse Key := [(key1974, -6), (key1977, -6), (key1982, 12), (key2210, 6), (key2214, 6), (key2219, -6), (key2223, -6)]

def row17211 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17212 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17213 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17214 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17215 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17216 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17217 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17218 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17219 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17220 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17221 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17222 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17223 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17224 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17225 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17226 : Integer.Sparse Key := [(key758, 12), (key762, -12), (key764, -12), (key789, 12)]

def row17227 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17228 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17229 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17230 : Integer.Sparse Key := [(key758, 12), (key762, -12), (key764, -12), (key789, 12)]

def row17231 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17232 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17233 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17234 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17235 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17236 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17237 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17238 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17239 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17240 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17241 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17242 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17243 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17244 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17245 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17246 : Integer.Sparse Key := [(key2014, -6), (key2018, -6), (key2023, 12), (key2043, 6), (key2046, 6), (key2051, -6), (key2052, -6)]

def row17247 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17248 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17249 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17250 : Integer.Sparse Key := [(key2014, -6), (key2018, -6), (key2023, 12), (key2043, 6), (key2046, 6), (key2051, -6), (key2052, -6)]

def row17251 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17252 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17253 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17254 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17255 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17256 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17257 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17258 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17259 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17260 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17261 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17262 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17263 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17264 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17265 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17266 : Integer.Sparse Key := [(key357, -6), (key359, -6), (key365, 12), (key527, 6), (key535, -6), (key674, 6), (key675, -6)]

def row17267 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17268 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17269 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17270 : Integer.Sparse Key := [(key357, -6), (key359, -6), (key365, 12), (key527, 6), (key535, -6), (key674, 6), (key675, -6)]

def row17271 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17272 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17273 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17274 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17275 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17276 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17277 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17278 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17279 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17280 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17281 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17282 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17283 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17284 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17285 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17286 : Integer.Sparse Key := [(key1976, 12), (key1981, -6), (key1983, -6), (key2218, -6), (key2224, -6), (key2262, 6), (key2266, 6)]

def row17287 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17288 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17289 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17290 : Integer.Sparse Key := [(key1976, 12), (key1981, -6), (key1983, -6), (key2218, -6), (key2224, -6), (key2262, 6), (key2266, 6)]

def row17291 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17292 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17293 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17294 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17295 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17296 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17297 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17298 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17299 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17300 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17301 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17302 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17303 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17304 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17305 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17306 : Integer.Sparse Key := [(key2026, 12), (key2055, -6), (key2056, -6), (key2144, -6), (key2145, -6), (key2228, 6), (key2229, 6)]

def row17307 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17308 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17309 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17310 : Integer.Sparse Key := [(key2026, 12), (key2055, -6), (key2056, -6), (key2144, -6), (key2145, -6), (key2228, 6), (key2229, 6)]

def row17311 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17312 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17313 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17314 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17315 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17316 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17317 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17318 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17319 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17320 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17321 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17322 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17323 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17324 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17325 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17326 : Integer.Sparse Key := [(key2042, -6), (key2047, -6), (key2055, 6), (key2056, 6), (key2127, 6), (key2134, 6), (key2144, -6), (key2145, -6)]

def row17327 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17328 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17329 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17330 : Integer.Sparse Key := [(key2042, -6), (key2047, -6), (key2055, 6), (key2056, 6), (key2127, 6), (key2134, 6), (key2144, -6), (key2145, -6)]

def row17331 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17332 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17333 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17334 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17335 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17336 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17337 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17338 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17339 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17340 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17341 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17342 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17343 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17344 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17345 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17346 : Integer.Sparse Key := [(key2043, -6), (key2046, -6), (key2051, 6), (key2052, 6), (key2128, 6), (key2133, 6), (key2138, -6), (key2141, -6)]

def row17347 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17348 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17349 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17350 : Integer.Sparse Key := [(key2043, -6), (key2046, -6), (key2051, 6), (key2052, 6), (key2128, 6), (key2133, 6), (key2138, -6), (key2141, -6)]

def row17351 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17352 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17353 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17354 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17355 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17356 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17357 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17358 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17359 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17360 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17361 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17362 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17363 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17364 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17365 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17366 : Integer.Sparse Key := [(key2017, 12), (key2022, -6), (key2024, -6), (key2050, -6), (key2053, -6), (key2075, 6), (key2076, 6)]

def row17367 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17368 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17369 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17370 : Integer.Sparse Key := [(key2017, 12), (key2022, -6), (key2024, -6), (key2050, -6), (key2053, -6), (key2075, 6), (key2076, 6)]

def row17371 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17372 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17373 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17374 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17375 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17376 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17377 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17378 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17379 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17380 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17381 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17382 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17383 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17384 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17385 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17386 : Integer.Sparse Key := [(key783, 12), (key808, -12), (key837, -12), (key932, 12)]

def row17387 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17388 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17389 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17390 : Integer.Sparse Key := [(key783, 12), (key808, -12), (key837, -12), (key932, 12)]

def row17391 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17392 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17393 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key768, 4), (key769, 2), (key793, -4)]

def row17394 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key768, 4), (key769, 2), (key793, -4)]

def row17395 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17396 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17397 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

def row17398 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

def row17399 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

def row17400 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

def row17401 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

def row17402 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

def row17403 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

def row17404 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

def row17405 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

def row17406 : Integer.Sparse Key := [(key757, -6), (key759, -6), (key761, 6), (key766, 12), (key769, 6), (key793, -12)]

def row17407 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17408 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

def row17409 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

def row17410 : Integer.Sparse Key := [(key757, -6), (key759, -6), (key761, 6), (key766, 6), (key768, 6), (key769, 6), (key793, -12)]

def row17411 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

def row17412 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

def row17413 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

def row17414 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17415 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17416 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17417 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17418 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17419 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17420 : Integer.Sparse Key := [(key1854, 12), (key1856, -24), (key1858, 12)]

def row17421 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

def row17422 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

def row17423 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

def row17424 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17425 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17426 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17427 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17428 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17429 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17430 : Integer.Sparse Key := [(key620, -12), (key624, 12), (key646, 12), (key652, -12)]

def row17431 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

def row17432 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

def row17433 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

def row17434 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17435 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17436 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17437 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17438 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17439 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17440 : Integer.Sparse Key := [(key1853, -12), (key1857, 12), (key1885, 12), (key1888, -12)]

def row17441 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

def row17442 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

def row17443 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

def row17444 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17445 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17446 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17447 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17448 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17449 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17450 : Integer.Sparse Key := [(key1959, 12), (key1961, -12), (key1967, -12), (key1970, 12)]

def row17451 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

def row17452 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

def row17453 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

def row17454 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17455 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17456 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17457 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17458 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17459 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17460 : Integer.Sparse Key := [(key665, -12), (key666, 12), (key682, 12), (key683, -12)]

def row17461 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

def row17462 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

def row17463 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

def row17464 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17465 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17466 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17467 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17468 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17469 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17470 : Integer.Sparse Key := [(key621, 12), (key623, -24), (key625, 12)]

def row17471 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

def row17472 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

def row17473 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

def row17474 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17475 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17476 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17477 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17478 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17479 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17480 : Integer.Sparse Key := [(key1862, -12), (key1866, 12), (key1868, 12), (key1871, -12)]

def row17481 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

def row17482 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

def row17483 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

def row17484 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17485 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17486 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17487 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17488 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17489 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17490 : Integer.Sparse Key := [(key1963, 12), (key1965, -24), (key1968, 12)]

def row17491 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

def row17492 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

def row17493 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

def row17494 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17495 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17496 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17497 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17498 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17499 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17500 : Integer.Sparse Key := [(key1934, -12), (key1935, 12), (key1954, 12), (key1955, -12)]

def row17501 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

def row17502 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

def row17503 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

def row17504 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17505 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17506 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17507 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17508 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17509 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17510 : Integer.Sparse Key := [(key688, 12), (key689, -24), (key691, 12)]

def row17511 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

def row17512 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

def row17513 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

def row17514 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17515 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17516 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17517 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17518 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17519 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17520 : Integer.Sparse Key := [(key1938, -12), (key1939, 12), (key1941, 12), (key1942, -12)]

def row17521 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

def row17522 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

def row17523 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

def row17524 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17525 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17526 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17527 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17528 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17529 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17530 : Integer.Sparse Key := [(key517, -12), (key524, 12), (key549, 12), (key555, -12)]

def row17531 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

def row17532 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

def row17533 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

def row17534 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17535 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17536 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17537 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17538 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17539 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17540 : Integer.Sparse Key := [(key1854, 12), (key1856, -12), (key1887, -12), (key1890, 12)]

def row17541 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

def row17542 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

def row17543 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

def row17544 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17545 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17546 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17547 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17548 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17549 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17550 : Integer.Sparse Key := [(key1866, 12), (key1871, -12), (key1881, -12), (key1889, 12)]

def row17551 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

def row17552 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

def row17553 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

def row17554 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17555 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17556 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17557 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17558 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17559 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17560 : Integer.Sparse Key := [(key1868, -12), (key1871, 12), (key1878, 12), (key1881, -12)]

def row17561 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

def row17562 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

def row17563 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

def row17564 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17565 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17566 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17567 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17568 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17569 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17570 : Integer.Sparse Key := [(key1941, -12), (key1942, 12), (key1950, 12), (key1951, -12)]

def row17571 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

def row17572 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

def row17573 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

def row17574 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17575 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17576 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17577 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17578 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17579 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17580 : Integer.Sparse Key := [(key1863, 12), (key1865, -12), (key1870, -12), (key1872, 12)]

def row17581 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

def row17582 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

def row17583 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

def row17584 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17585 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17586 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17587 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17588 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17589 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17590 : Integer.Sparse Key := [(key536, 12), (key544, -24), (key556, 12)]

def row17591 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

def row17592 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

def row17593 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

def row17594 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17595 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17596 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17597 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17598 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17599 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17600 : Integer.Sparse Key := [(key633, -12), (key635, 12), (key638, 12), (key644, -12)]

def row17601 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

def row17602 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

def row17603 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

def row17604 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17605 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17606 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17607 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17608 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17609 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17610 : Integer.Sparse Key := [(key291, 12), (key294, -24), (key298, 12)]

def row17611 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

def row17612 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

def row17613 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

def row17614 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17615 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17616 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17617 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17618 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17619 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17620 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17621 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17622 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17623 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17624 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17625 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17626 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

def row17627 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

def row17628 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

def row17629 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

def row17630 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

def row17631 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

def row17632 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17633 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17634 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17635 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17636 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17637 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17638 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17639 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17640 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17641 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17642 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17643 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17644 : Integer.Sparse Key := [(key60, 2), (key72, 2), (key125, -4), (key127, 6), (key135, -8), (key704, 2), (key709, -8), (key723, 2), (key863, 6), (key885, -4), (key940, 4)]

def row17645 : Integer.Sparse Key := [(key60, 2), (key72, 2), (key125, -4), (key127, 6), (key135, -8), (key704, 2), (key709, -8), (key723, 2), (key863, 6), (key885, -4), (key940, 4)]

def row17646 : Integer.Sparse Key := [(key72, 4), (key125, -4), (key127, 6), (key135, -8), (key180, 4), (key704, 4), (key709, -8), (key863, 6), (key885, -4)]

def row17647 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

def row17648 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

def row17649 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

def row17650 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17651 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17652 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17653 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17654 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17655 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17656 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17657 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17658 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17659 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17660 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17661 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17662 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

def row17663 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17664 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

def row17665 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

def row17666 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

def row17667 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

def row17668 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17669 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17670 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17671 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17672 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17673 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17674 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17675 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17676 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17677 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17678 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17679 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17680 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

def row17681 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

def row17682 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

def row17683 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

def row17684 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

def row17685 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

def row17686 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17687 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17688 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17689 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17690 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17691 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17692 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17693 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17694 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17695 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17696 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17697 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17698 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

def row17699 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

def row17700 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

def row17701 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

def row17702 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

def row17703 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

def row17704 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17705 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17706 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17707 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17708 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17709 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17710 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17711 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17712 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17713 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17714 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17715 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17716 : Integer.Sparse Key := [(key78, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8), (key956, 4)]

def row17717 : Integer.Sparse Key := [(key78, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8), (key956, 4)]

def row17718 : Integer.Sparse Key := [(key78, 4), (key191, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8)]

def row17719 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

def row17720 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

def row17721 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

def row17722 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17723 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17724 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17725 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17726 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17727 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17728 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17729 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17730 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17731 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17732 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17733 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17734 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

def row17735 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

def row17736 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

def row17737 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

def row17738 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

def row17739 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

def row17740 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17741 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17742 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17743 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17744 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17745 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17746 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17747 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17748 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17749 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17750 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17751 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17752 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

def row17753 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

def row17754 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

def row17755 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

def row17756 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

def row17757 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

def row17758 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17759 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17760 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17761 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17762 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17763 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17764 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17765 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17766 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17767 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17768 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17769 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17770 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

def row17771 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

def row17772 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

def row17773 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

def row17774 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

def row17775 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

def row17776 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17777 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17778 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17779 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17780 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17781 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17782 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17783 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17784 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17785 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17786 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17787 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17788 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

def row17789 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

def row17790 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

def row17791 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17792 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

def row17793 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

def row17794 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17795 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17796 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17797 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17798 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17799 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17800 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17801 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17802 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17803 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17804 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17805 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17806 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

def row17807 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

def row17808 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

def row17809 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

def row17810 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

def row17811 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

def row17812 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17813 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17814 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17815 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17816 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17817 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17818 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17819 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17820 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17821 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17822 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17823 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17824 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

def row17825 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

def row17826 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

def row17827 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

def row17828 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

def row17829 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

def row17830 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17831 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17832 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17833 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17834 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17835 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17836 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17837 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17838 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17839 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17840 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17841 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17842 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

def row17843 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

def row17844 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

def row17845 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

def row17846 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

def row17847 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

def row17848 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17849 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17850 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17851 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17852 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17853 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17854 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17855 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17856 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17857 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17858 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17859 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17860 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

def row17861 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

def row17862 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

def row17863 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

def row17864 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

def row17865 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

def row17866 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17867 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17868 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17869 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17870 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17871 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17872 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17873 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17874 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17875 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17876 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17877 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17878 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

def row17879 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

def row17880 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

def row17881 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

def row17882 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

def row17883 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

def row17884 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17885 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17886 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17887 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17888 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17889 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17890 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17891 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17892 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17893 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17894 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17895 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17896 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

def row17897 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

def row17898 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

def row17899 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

def row17900 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

def row17901 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

def row17902 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17903 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17904 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17905 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17906 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17907 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17908 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17909 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17910 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17911 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17912 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17913 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17914 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

def row17915 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

def row17916 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

def row17917 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

def row17918 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

def row17919 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17920 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17921 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17922 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17923 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17924 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17925 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17926 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17927 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17928 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17929 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17930 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17931 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17932 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

def row17933 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

def row17934 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

def row17935 : Integer.Sparse Key := [(key763, -4), (key765, -2), (key775, -2), (key785, -4), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

def row17936 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, -2), (key773, -2), (key775, -2), (key785, -2), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

def row17937 : Integer.Sparse Key := [(key765, -4), (key767, -4), (key773, -4), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

def row17938 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key792, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -2), (key933, 4)]

def row17939 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key792, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -2), (key933, 4)]

def row17940 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17941 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17942 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17943 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17944 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key810, -4), (key838, -4), (key851, 4)]

def row17945 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key810, -4), (key838, -4), (key851, 4)]

def row17946 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17947 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17948 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17949 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17950 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

def row17951 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

def row17952 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

def row17953 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

def row17954 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

def row17955 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

def row17956 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17957 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17958 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17959 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17960 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17961 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17962 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17963 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17964 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17965 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17966 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17967 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17968 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

def row17969 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

def row17970 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

def row17971 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

def row17972 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

def row17973 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

def row17974 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17975 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17976 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17977 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17978 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17979 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17980 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17981 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17982 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17983 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17984 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17985 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17986 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

def row17987 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

def row17988 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

def row17989 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17990 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17991 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17992 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17993 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17994 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17995 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17996 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17997 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17998 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17999 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18000 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18001 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18002 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18003 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18004 : Integer.Sparse Key := [(key2421, 12), (key2428, -12), (key2429, -12), (key2442, 12)]

def row18005 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18006 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18007 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18008 : Integer.Sparse Key := [(key2421, 12), (key2428, -12), (key2429, -12), (key2442, 12)]

def row18009 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18010 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18011 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18012 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18013 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18014 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18015 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18016 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18017 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18018 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18019 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18020 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18021 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18022 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18023 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18024 : Integer.Sparse Key := [(key1049, -6), (key1052, -6), (key1060, 12), (key1135, 6), (key1140, -6), (key1205, 6), (key1207, -6)]

def row18025 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18026 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18027 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18028 : Integer.Sparse Key := [(key1049, -6), (key1052, -6), (key1060, 12), (key1135, 6), (key1140, -6), (key1205, 6), (key1207, -6)]

def row18029 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

def row18030 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

def row18031 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

def row18032 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

def row18033 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

def row18034 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

def row18035 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18036 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18037 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18038 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18039 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18040 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18041 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18042 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18043 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18044 : Integer.Sparse Key := [(key2415, -6), (key2418, -6), (key2425, 12), (key2488, 6), (key2493, -6), (key2547, 6), (key2549, -6)]

def row18045 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18046 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

def row18047 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18048 : Integer.Sparse Key := [(key2415, -6), (key2418, -6), (key2425, 12), (key2488, 6), (key2493, -6), (key2547, 6), (key2549, -6)]

def row18049 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

def row18050 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

def row18051 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

def row18052 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

def row18053 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

def row18054 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

def row18055 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18056 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18057 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18058 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18059 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18060 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18061 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18062 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18063 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18064 : Integer.Sparse Key := [(key3046, 12), (key3060, -6), (key3064, -6), (key3095, -6), (key3101, -6), (key3123, 6), (key3125, 6)]

def row18065 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18066 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18067 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

def row18068 : Integer.Sparse Key := [(key3046, 12), (key3060, -6), (key3064, -6), (key3095, -6), (key3101, -6), (key3123, 6), (key3125, 6)]

def row18069 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

def row18070 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

def row18071 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

def row18072 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

def row18073 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

def row18074 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

def row18075 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18076 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18077 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18078 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18079 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18080 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18081 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18082 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18083 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18084 : Integer.Sparse Key := [(key1048, -6), (key1051, -6), (key1059, 12), (key1134, 6), (key1139, -6), (key1204, 6), (key1206, -6)]

def row18085 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18086 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18087 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

def row18088 : Integer.Sparse Key := [(key1048, -6), (key1051, -6), (key1059, 12), (key1134, 6), (key1139, -6), (key1204, 6), (key1206, -6)]

def row18089 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

def row18090 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

def row18091 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

def row18092 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

def row18093 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

def row18094 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

def row18095 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18096 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18097 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18098 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18099 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18100 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18101 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18102 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18103 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18104 : Integer.Sparse Key := [(key1056, 12), (key1064, -12), (key1065, -12), (key1079, 12)]

def row18105 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18106 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18107 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

def row18108 : Integer.Sparse Key := [(key1056, 12), (key1064, -12), (key1065, -12), (key1079, 12)]

def row18109 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

def row18110 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

def row18111 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

def row18112 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

def row18113 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

def row18114 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

def row18115 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18116 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18117 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18118 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18119 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18120 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18121 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18122 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18123 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18124 : Integer.Sparse Key := [(key2680, -6), (key2683, -6), (key2690, 12), (key2711, 6), (key2716, -6), (key2741, 6), (key2743, -6)]

def row18125 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18126 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18127 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

def row18128 : Integer.Sparse Key := [(key2680, -6), (key2683, -6), (key2690, 12), (key2711, 6), (key2716, -6), (key2741, 6), (key2743, -6)]

def row18129 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

def row18130 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

def row18131 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

def row18132 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

def row18133 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

def row18134 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

def row18135 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18136 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18137 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18138 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18139 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18140 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18141 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18142 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18143 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18144 : Integer.Sparse Key := [(key3080, 12), (key3085, -12), (key3087, -12), (key3100, 12)]

def row18145 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18146 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18147 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

def row18148 : Integer.Sparse Key := [(key3080, 12), (key3085, -12), (key3087, -12), (key3100, 12)]

def row18149 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

def row18150 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

def row18151 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

def row18152 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

def row18153 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

def row18154 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

def row18155 : Integer.Sparse Key := [(key2414, -2), (key2417, 6), (key2424, -4), (key3033, 4), (key3035, -4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

def row18156 : Integer.Sparse Key := [(key2414, -2), (key2417, 6), (key2424, -4), (key3033, 4), (key3035, -4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

def row18157 : Integer.Sparse Key := [(key2414, -2), (key2417, 6), (key2424, -4), (key3033, 4), (key3035, -4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

def row18158 : Integer.Sparse Key := [(key2414, 6), (key2417, -2), (key2424, -4), (key3033, -4), (key3035, 4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

def row18159 : Integer.Sparse Key := [(key2414, 6), (key2417, -2), (key2424, -4), (key3033, -4), (key3035, 4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

def row18160 : Integer.Sparse Key := [(key2414, 6), (key2417, -2), (key2424, -4), (key3033, -4), (key3035, 4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

def row18161 : Integer.Sparse Key := [(key2414, -2), (key2424, -4), (key2487, -2), (key2492, 2), (key3033, 4), (key3035, 2), (key3128, -2), (key3138, 2)]

def row18162 : Integer.Sparse Key := [(key2414, -2), (key2424, -4), (key2487, -2), (key2492, 2), (key3033, 4), (key3035, 2), (key3128, -2), (key3138, 2)]

def row18163 : Integer.Sparse Key := [(key2414, -2), (key2424, -4), (key2487, -2), (key2492, 2), (key3033, 4), (key3035, 2), (key3128, -2), (key3138, 2)]

def row18164 : Integer.Sparse Key := [(key2414, -2), (key2424, 12), (key2487, 6), (key2492, -6), (key2548, -6), (key3033, -4), (key3035, -6), (key3128, 6)]

def row18165 : Integer.Sparse Key := [(key2414, 6), (key2417, 2), (key2424, -4), (key2492, 2), (key2546, -2), (key2548, 2), (key3033, -4), (key3120, -2)]

def row18166 : Integer.Sparse Key := [(key2414, 6), (key2417, 2), (key2424, -4), (key2492, 2), (key2546, -2), (key2548, 2), (key3033, -4), (key3120, -2)]

def row18167 : Integer.Sparse Key := [(key2414, 6), (key2417, 2), (key2424, -4), (key2492, 2), (key2546, -2), (key2548, 2), (key3033, -4), (key3120, -2)]

def row18168 : Integer.Sparse Key := [(key2414, -2), (key2417, -6), (key2424, 12), (key2487, 6), (key2492, -6), (key2546, 6), (key2548, -6), (key3033, -4)]

def row18169 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

def row18170 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

def row18171 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

def row18172 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

def row18173 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

def row18174 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

def row18175 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18176 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18177 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18178 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18179 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18180 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18181 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18182 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18183 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18184 : Integer.Sparse Key := [(key2101, 12), (key2106, -12), (key2111, -12), (key2139, 12)]

def row18185 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18186 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18187 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

def row18188 : Integer.Sparse Key := [(key2101, 12), (key2106, -12), (key2111, -12), (key2139, 12)]

def row18189 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18190 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18191 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18192 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18193 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18194 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18195 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, 3), (key3050, 2), (key3054, -3), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2)]

def row18196 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, 3), (key3050, 2), (key3054, -3), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2)]

def row18197 : Integer.Sparse Key := [(key2679, -1), (key2689, -2), (key2955, -2), (key3047, 3), (key3050, 2), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3110, 2)]

def row18198 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3106, 2)]

def row18199 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3106, 2)]

def row18200 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2813, 2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3096, -2), (key3106, 2)]

def row18201 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, -2), (key2715, 2), (key3047, 3), (key3050, 2), (key3054, -3), (key3066, -2), (key3072, 2)]

def row18202 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, -2), (key2715, 2), (key3047, 3), (key3050, 2), (key3054, -3), (key3066, -2), (key3072, 2)]

def row18203 : Integer.Sparse Key := [(key2679, -1), (key2689, -2), (key2710, -2), (key2715, 2), (key2955, -2), (key3047, 3), (key3050, 2), (key3054, -2), (key3066, -2), (key3072, 2), (key3110, 2)]

def row18204 : Integer.Sparse Key := [(key2679, -3), (key2689, 12), (key2710, 6), (key2715, -6), (key2742, -6), (key3047, -3), (key3050, -6), (key3066, 6)]

def row18205 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key3061, -2)]

def row18206 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key3061, -2)]

def row18207 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key2813, 2), (key3061, -2), (key3096, -2)]

def row18208 : Integer.Sparse Key := [(key2679, -3), (key2682, -6), (key2689, 12), (key2710, 6), (key2715, -6), (key2740, 6), (key2742, -6), (key3047, -3)]

def row18209 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18210 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18211 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18212 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18213 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18214 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18215 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18216 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18217 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18218 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18219 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18220 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18221 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18222 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18223 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18224 : Integer.Sparse Key := [(key1500, -6), (key1503, -6), (key1507, 12), (key1732, 6), (key1736, -6), (key1874, 6), (key1875, -6)]

def row18225 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18226 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18227 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18228 : Integer.Sparse Key := [(key1500, -6), (key1503, -6), (key1507, 12), (key1732, 6), (key1736, -6), (key1874, 6), (key1875, -6)]

def row18229 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18230 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18231 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18232 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18233 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18234 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18235 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18236 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18237 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18238 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18239 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18240 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18241 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18242 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18243 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18244 : Integer.Sparse Key := [(key2421, 12), (key2428, -6), (key2429, -6), (key2496, -6), (key2508, 6), (key2550, -6), (key2556, 6)]

def row18245 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18246 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18247 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18248 : Integer.Sparse Key := [(key2421, 12), (key2428, -6), (key2429, -6), (key2496, -6), (key2508, 6), (key2550, -6), (key2556, 6)]

def row18249 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18250 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18251 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18252 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18253 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18254 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18255 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18256 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18257 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18258 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18259 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18260 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18261 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18262 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18263 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18264 : Integer.Sparse Key := [(key2690, 12), (key2716, -6), (key2743, -6), (key2819, -6), (key2901, 6), (key2956, -6), (key2980, 6)]

def row18265 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18266 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18267 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18268 : Integer.Sparse Key := [(key2690, 12), (key2716, -6), (key2743, -6), (key2819, -6), (key2901, 6), (key2956, -6), (key2980, 6)]

def row18269 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18270 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18271 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18272 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18273 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18274 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18275 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18276 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18277 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18278 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18279 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18280 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18281 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18282 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18283 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18284 : Integer.Sparse Key := [(key2711, -6), (key2716, 6), (key2741, -6), (key2743, 6), (key2814, 6), (key2819, -6), (key2954, 6), (key2956, -6)]

def row18285 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18286 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18287 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18288 : Integer.Sparse Key := [(key2711, -6), (key2716, 6), (key2741, -6), (key2743, 6), (key2814, 6), (key2819, -6), (key2954, 6), (key2956, -6)]

def row18289 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18290 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18291 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18292 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18293 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18294 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18295 : Integer.Sparse Key := [(key2679, -1), (key2682, 4), (key2689, -1), (key2740, 2), (key2742, -2), (key3047, 1), (key3050, -4), (key3054, 1), (key3061, 2), (key3069, -2), (key3096, -2), (key3103, -2), (key3106, 2), (key3110, 2)]

def row18296 : Integer.Sparse Key := [(key2679, -1), (key2682, 4), (key2689, -1), (key2740, 2), (key2742, -2), (key3047, 1), (key3050, -4), (key3054, 1), (key3061, 2), (key3069, -2), (key3096, -2), (key3103, -2), (key3106, 2), (key3110, 2)]

def row18297 : Integer.Sparse Key := [(key2679, -1), (key2682, 4), (key2740, 2), (key2742, -2), (key2955, 2), (key3047, 1), (key3050, -4), (key3061, 2), (key3069, -2), (key3096, -2), (key3103, -2), (key3106, 2)]

def row18298 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2818, 2), (key3047, -2), (key3066, 2), (key3072, -2), (key3096, -2), (key3103, -2), (key3110, 2)]

def row18299 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2818, 2), (key3047, -2), (key3066, 2), (key3072, -2), (key3096, -2), (key3103, -2), (key3110, 2)]

def row18300 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2813, -2), (key2818, 2), (key3047, -2), (key3066, 2), (key3072, -2), (key3103, -2), (key3110, 2)]

def row18301 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, 2), (key2715, -2), (key2742, -2), (key2813, -2), (key2818, 2), (key3047, 1), (key3054, 1), (key3066, 2), (key3103, -2), (key3110, 2)]

def row18302 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, 2), (key2715, -2), (key2742, -2), (key2813, -2), (key2818, 2), (key3047, 1), (key3054, 1), (key3066, 2), (key3103, -2), (key3110, 2)]

def row18303 : Integer.Sparse Key := [(key2679, -1), (key2710, 2), (key2715, -2), (key2742, -2), (key2813, -2), (key2818, 2), (key2955, 2), (key3047, 1), (key3066, 2), (key3103, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18304 : Integer.Sparse Key := [(key2710, -6), (key2715, 6), (key2742, 6), (key2813, 6), (key2818, -6), (key2955, -6), (key3066, -6), (key3103, 6)]

def row18305 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2740, 2), (key2742, -2), (key2818, 2), (key2953, -2), (key2955, 2), (key3047, -2), (key3096, -2)]

def row18306 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2740, 2), (key2742, -2), (key2818, 2), (key2953, -2), (key2955, 2), (key3047, -2), (key3096, -2)]

def row18307 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2740, 2), (key2742, -2), (key2813, -2), (key2818, 2), (key2953, -2), (key2955, 2), (key3047, -2)]

def row18308 : Integer.Sparse Key := [(key2710, -6), (key2715, 6), (key2740, -6), (key2742, 6), (key2813, 6), (key2818, -6), (key2953, 6), (key2955, -6)]

def row18309 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

def row18310 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

def row18311 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

def row18312 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

def row18313 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

def row18314 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

def row18315 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18316 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18317 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18318 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18319 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18320 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18321 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18322 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18323 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18324 : Integer.Sparse Key := [(key2686, 12), (key2693, -6), (key2694, -6), (key2719, -6), (key2731, 6), (key2744, -6), (key2750, 6)]

def row18325 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18326 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18327 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

def row18328 : Integer.Sparse Key := [(key2686, 12), (key2693, -6), (key2694, -6), (key2719, -6), (key2731, 6), (key2744, -6), (key2750, 6)]

def row18329 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

def row18330 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

def row18331 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

def row18332 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

def row18333 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

def row18334 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

def row18335 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18336 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18337 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18338 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18339 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18340 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18341 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18342 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18343 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18344 : Integer.Sparse Key := [(key2122, 12), (key2162, -12), (key2185, -12), (key2285, 12)]

def row18345 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18346 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18347 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

def row18348 : Integer.Sparse Key := [(key2122, 12), (key2162, -12), (key2185, -12), (key2285, 12)]

def row18349 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

def row18350 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

def row18351 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

def row18352 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

def row18353 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

def row18354 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

def row18355 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18356 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18357 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18358 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18359 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18360 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18361 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18362 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18363 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18364 : Integer.Sparse Key := [(key2102, -6), (key2104, -6), (key2107, 6), (key2110, 6), (key2112, 6), (key2113, 6), (key2140, -12)]

def row18365 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18366 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18367 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

def row18368 : Integer.Sparse Key := [(key2102, -6), (key2104, -6), (key2107, 6), (key2110, 6), (key2112, 6), (key2113, 6), (key2140, -12)]

def row18369 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

def row18370 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

def row18371 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

def row18372 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

def row18373 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

def row18374 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

def row18375 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18376 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18377 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18378 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18379 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18380 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18381 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18382 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18383 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18384 : Integer.Sparse Key := [(key1945, 12), (key1947, -12), (key1948, -12), (key1952, 12)]

def row18385 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18386 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18387 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

def row18388 : Integer.Sparse Key := [(key1945, 12), (key1947, -12), (key1948, -12), (key1952, 12)]

def row18389 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

def row18390 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

def row18391 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

def row18392 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

def row18393 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

def row18394 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

def row18395 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18396 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18397 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18398 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18399 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18400 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18401 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18402 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18403 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18404 : Integer.Sparse Key := [(key2123, 12), (key2163, -12), (key2186, -12), (key2286, 12)]

def row18405 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18406 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18407 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

def row18408 : Integer.Sparse Key := [(key2123, 12), (key2163, -12), (key2186, -12), (key2286, 12)]

def row18409 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

def row18410 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

def row18411 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3090, 4), (key3091, 2), (key3109, -4)]

def row18412 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3090, 4), (key3091, 2), (key3109, -4)]

def row18413 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

def row18414 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

def row18415 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -6), (key3090, 2), (key3091, -2), (key3109, 4)]

def row18416 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -6), (key3090, 2), (key3091, -2), (key3109, 4)]

def row18417 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -6), (key3090, 2), (key3091, -2), (key3109, 4)]

def row18418 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, 6), (key3090, -10), (key3091, -2), (key3109, 4)]

def row18419 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, 6), (key3090, -10), (key3091, -2), (key3109, 4)]

def row18420 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, 6), (key3090, -10), (key3091, -2), (key3109, 4)]

def row18421 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -4), (key3091, -2), (key3109, 4)]

def row18422 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -4), (key3091, -2), (key3109, 4)]

def row18423 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -4), (key3091, -2), (key3109, 4)]

def row18424 : Integer.Sparse Key := [(key3081, -6), (key3082, -6), (key3086, 6), (key3088, 12), (key3091, 6), (key3109, -12)]

def row18425 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3109, 4)]

def row18426 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3109, 4)]

def row18427 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3109, 4)]

def row18428 : Integer.Sparse Key := [(key3081, -6), (key3082, -6), (key3086, 6), (key3088, 6), (key3090, 6), (key3091, 6), (key3109, -12)]

def row18429 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

def row18430 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

def row18431 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18432 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

def row18433 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

def row18434 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

def row18435 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

def row18436 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

def row18437 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

def row18438 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 36), (key2578, 6)]

def row18439 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 36), (key2578, 6)]

def row18440 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

def row18441 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 30), (key2566, 6), (key2578, 6)]

def row18442 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

def row18443 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

def row18444 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 24), (key2566, 12), (key2578, 6)]

def row18445 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

def row18446 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

def row18447 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

def row18448 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19384 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19385 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19386 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19387 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19388 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19389 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19390 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19391 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19392 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19393 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19394 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19395 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19396 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19397 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19398 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19399 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19400 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19401 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19402 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19403 : Integer.Sparse Key := [(key1273, 6), (key1278, 18), (key1696, 18), (key1701, 36), (key1751, 18), (key1933, 18), (key1953, 6)]

def row19404 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19405 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19406 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19407 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19408 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19409 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19410 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19411 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19412 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19413 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19414 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19415 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19416 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19417 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19418 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19419 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19420 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19421 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19422 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19423 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19424 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19425 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19426 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19427 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19428 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19429 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19430 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19431 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19432 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19433 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19434 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19435 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19436 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19437 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19438 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19439 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19440 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19441 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19442 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19443 : Integer.Sparse Key := [(key1358, 6), (key1364, 12), (key1374, 6), (key1484, 6), (key1490, 12), (key1513, 6), (key1710, 12), (key1716, 12), (key1723, 12), (key1741, 12), (key1937, 12), (key1940, 6), (key1949, 6)]

def row19444 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19445 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19446 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19447 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19448 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19449 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19450 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19451 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19452 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19453 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19454 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19455 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19456 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19457 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19458 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19459 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19460 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19461 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19462 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19463 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19464 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19465 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19466 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19467 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19468 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19469 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19470 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19471 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19472 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19473 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19474 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19475 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19476 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19477 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19478 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19479 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19480 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19481 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19482 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19483 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

def row19484 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19485 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19486 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19487 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19488 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19489 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19490 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19491 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19492 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19493 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19494 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19495 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19496 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19497 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19498 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19499 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19500 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19501 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19502 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19503 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

def row19504 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19505 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19506 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19507 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19508 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19509 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19510 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19511 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19512 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19513 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19514 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19515 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19516 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19517 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19518 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19519 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19520 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19521 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19522 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19523 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

def row19524 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19525 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19526 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19527 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19528 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19529 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19530 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19531 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19532 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19533 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19534 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19535 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19536 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19537 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19538 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19539 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19540 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19541 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19542 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19543 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

def row19544 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19545 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19546 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19547 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19548 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19549 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19550 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19551 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19552 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19553 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19554 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19555 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19556 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19557 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19558 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19559 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19560 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19561 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19562 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19563 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

def row19564 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19565 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19566 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19567 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19568 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19569 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19570 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19571 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19572 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19573 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19574 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19575 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19576 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19577 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19578 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19579 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19580 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19581 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19582 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

def row19583 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19584 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19585 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19586 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19587 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19588 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

def row19589 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

def row19590 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

def row19591 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

def row19592 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

def row19593 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 36), (key680, 6)]

def row19594 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 36), (key680, 6)]

def row19595 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

def row19596 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 30), (key670, 6), (key680, 6)]

def row19597 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

def row19598 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

def row19599 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 24), (key670, 12), (key680, 6)]

def row19600 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19601 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19602 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19603 : Integer.Sparse Key := [(key288, 6), (key289, 18), (key513, 18), (key515, 36), (key547, 18), (key670, 18), (key680, 6)]

def row19604 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19605 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19606 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19607 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19608 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19609 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19610 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19611 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19612 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19613 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19614 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19615 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19616 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19617 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19618 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19619 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19620 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19621 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19622 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19623 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19624 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19625 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19626 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19627 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19628 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19629 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19630 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19631 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19632 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19633 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19634 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19635 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19636 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19637 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19638 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19639 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19640 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19641 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19642 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19643 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19644 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19645 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19646 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19647 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19648 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19649 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19650 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19651 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19652 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19653 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19654 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19655 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19656 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19657 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19658 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19659 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19660 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19661 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19662 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19663 : Integer.Sparse Key := [(key1251, 6), (key1259, 12), (key1271, 6), (key1526, 6), (key1534, 12), (key1604, 12), (key1612, 12), (key1640, 12), (key1679, 12), (key1693, 6), (key1894, 6), (key1916, 12), (key1930, 6)]

def row19664 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19665 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19666 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19667 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19668 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19669 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19670 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19671 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19672 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19673 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19674 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19675 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19676 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19677 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19678 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19679 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19680 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19681 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19682 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19683 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19684 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19685 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19686 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19687 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19688 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19689 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19690 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19691 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19692 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19693 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19694 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19695 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19696 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19697 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19698 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19699 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19700 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19701 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19702 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19703 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19704 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19705 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19706 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19707 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19708 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19709 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19710 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19711 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19712 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19713 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19714 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19715 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19716 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19717 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19718 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19719 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19720 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19721 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19722 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19723 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 48), (key456, 24)]

def row19784 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19785 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19786 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19787 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row20096 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20204 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20205 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20206 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20207 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20208 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20209 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20210 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20211 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20212 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20213 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20214 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20215 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20216 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20217 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20218 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20219 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20220 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20221 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20222 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20223 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row20224 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20225 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20226 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20227 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20228 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20229 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20230 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20231 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20232 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20233 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20234 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20235 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20236 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20237 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20238 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20239 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20240 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20241 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20242 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20243 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20244 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20245 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20246 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20247 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20248 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20249 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20250 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20251 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20252 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20253 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20254 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20255 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20256 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20257 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20258 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20259 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20260 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20261 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20262 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20263 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20264 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20265 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20266 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20267 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20268 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20269 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20270 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20271 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20272 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20273 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20274 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20275 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20276 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20277 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20278 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20279 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20280 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20281 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20282 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20283 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20284 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20285 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20286 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20287 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20288 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20289 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20290 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20291 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20292 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20293 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20294 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20295 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20296 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20297 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20298 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20299 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20300 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

end MUB6.Certificate.GramRows

end OAI
end


