-- Prove2me | Definitions.Def_OAIQ106D153
-- name    : OAIQ106D153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:01:55.541428+00:00
-- url     : https://prove2.me/theorems/88f9e074-5c04-4866-9c18-d1c20d44e5b0
-- title:
--   Definitions bundle OAIQ106D153 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1517 declarations of OpenAI's Lean: 1517 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block5.entry1_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry2_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry2_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry3_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry4_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_4`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_5`, `OAI.MUB6.Certificate.GramEntries.Block5.entry6_0`, `OAI.MUB6.Certificate.GramEntries.Block5.entry6_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry6_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry6_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry6_4` and 1477 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramFunctions_Block4`, `MutuallyUnbiased_GramFunctions_Block5`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block128`, `MutuallyUnbiased_GramRows_Block129`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block133`, `MutuallyUnbiased_GramRows_Block134`, `MutuallyUnbiased_GramRows_Block164`, `MutuallyUnbiased_GramRows_Block165`, `MutuallyUnbiased_GramRows_Block166`, `MutuallyUnbiased_GramRows_Block167`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block175`, `MutuallyUnbiased_GramRows_Block176`, `MutuallyUnbiased_GramRows_Block177`, `MutuallyUnbiased_GramRows_Block178`, `MutuallyUnbiased_GramRows_Block182`.
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D199`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

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

def entry1_1 : Integer.Sparse Key := [(key0, 2880), (key83, 11520)]

def entry2_0 : Integer.Sparse Key := [(key2370, 360), (key2376, 720), (key2388, 480), (key2398, 360), (key2404, 720), (key2435, 480), (key2464, 480), (key2470, 576), (key2478, 720), (key2501, 720), (key2568, 360), (key2570, 240), (key2575, 240), (key2583, 360), (key2589, 720), (key2604, 240), (key2762, 360), (key2768, 720), (key2839, 960), (key2845, 864), (key2876, 1080), (key2916, 720), (key2925, 480), (key3005, 240), (key3019, 720), (key3028, 480)]

def entry2_1 : Integer.Sparse Key := [(key991, 2880), (key1026, 2880), (key1104, 5760), (key1230, 2880)]

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

def entry10_4 : Integer.Sparse Key := [(key220, 720), (key225, 2160), (key492, 2160), (key497, 4320), (key551, 2160), (key664, 2160), (key681, 720)]

def entry10_5 : Integer.Sparse Key := [(key1277, 1440), (key1283, 1440), (key1700, 2880), (key1706, 1440), (key1756, 1440), (key1851, 1440), (key1855, 2880), (key1886, 1440)]

def entry10_6 : Integer.Sparse Key := [(key1274, 720), (key1278, 2160), (key1697, 2160), (key1701, 4320), (key1751, 2160), (key1852, 2160), (key1884, 720)]

def entry10_7 : Integer.Sparse Key := [(key1360, 2160), (key1372, 720), (key1486, 2160), (key1511, 720), (key1712, 4320), (key1721, 2160), (key1739, 2160)]

def entry10_10 : Integer.Sparse Key := [(key288, 720), (key289, 2160), (key513, 2160), (key515, 4320), (key547, 2880), (key670, 1440), (key680, 720)]

def entry11_0 : Integer.Sparse Key := [(key1251, 720), (key1259, 1440), (key1271, 720), (key1526, 720), (key1534, 1440), (key1604, 1440), (key1612, 1440), (key1640, 1440), (key1679, 1440), (key1693, 720), (key1894, 720), (key1916, 1440), (key1930, 720)]

def entry11_1 : Integer.Sparse Key := [(key208, 2880), (key377, 2880), (key428, 5760), (key456, 2880)]

def entry11_2 : Integer.Sparse Key := [(key1291, 240), (key1299, 480), (key1311, 480), (key1319, 480), (key1327, 480), (key1352, 480), (key1355, 240), (key1386, 240), (key1394, 480), (key1419, 480), (key1427, 480), (key1445, 480), (key1473, 480), (key1481, 240), (key1541, 480), (key1549, 480), (key1557, 480), (key1568, 480), (key1576, 480), (key1594, 480), (key1617, 480), (key1625, 480), (key1634, 480), (key1682, 480), (key1684, 480), (key1690, 480), (key1897, 480), (key1900, 240), (key1904, 480), (key1912, 240), (key1919, 480), (key1921, 480), (key1927, 480)]

def entry11_3 : Integer.Sparse Key := [(key1253, 2880), (key1528, 2880), (key1606, 5760), (key1636, 2880)]

def entry11_4 : Integer.Sparse Key := [(key18, 360), (key23, 720), (key35, 480), (key43, 360), (key48, 720), (key74, 480), (key100, 480), (key105, 576), (key115, 720), (key137, 720), (key195, 360), (key196, 240), (key200, 240), (key206, 360), (key212, 720), (key218, 240), (key375, 360), (key381, 720), (key426, 960), (key432, 864), (key460, 1080), (key486, 720), (key490, 480), (key654, 240), (key659, 720), (key663, 480)]

def entry11_6 : Integer.Sparse Key := [(key1252, 720), (key1257, 1440), (key1266, 720), (key1527, 720), (key1532, 1440), (key1605, 1440), (key1610, 1440), (key1638, 1440), (key1649, 1440), (key1672, 720), (key1766, 720), (key1807, 1440), (key1830, 720)]

def entry11_7 : Integer.Sparse Key := [(key1293, 720), (key1313, 1440), (key1323, 720), (key1388, 720), (key1421, 1440), (key1441, 720), (key1543, 1440), (key1553, 720), (key1570, 1440), (key1590, 720), (key1619, 1440), (key1621, 1440), (key1630, 1440)]

def entry11_8 : Integer.Sparse Key := [(key626, 2880), (key627, 5760), (key629, 2880), (key640, 2880)]

def entry11_9 : Integer.Sparse Key := [(key1407, 2880), (key1411, 1440), (key1435, 1440), (key1436, 2880), (key1584, 1440), (key1585, 2880), (key1628, 1440)]

def entry11_11 : Integer.Sparse Key := [(key236, 240), (key241, 480), (key248, 480), (key253, 480), (key263, 640), (key277, 320), (key278, 240), (key302, 240), (key307, 480), (key316, 640), (key321, 576), (key331, 720), (key346, 480), (key347, 320), (key385, 320), (key390, 384), (key400, 480), (key406, 480), (key411, 480), (key421, 640), (key435, 480), (key445, 576), (key453, 576), (key487, 384), (key488, 480), (key489, 480), (key655, 240), (key656, 160), (key657, 320), (key658, 240), (key660, 384), (key661, 480), (key662, 480)]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block4

def terms2 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 0, 2], -2⟩,
  ⟨1, ![1, -3, 0, 0, 2, 0], -2⟩,
  ⟨1, ![1, -3, 0, 2, 0, 0], -2⟩,
  ⟨1, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨1, ![1, 0, -3, 0, 0, 2], -2⟩,
  ⟨1, ![1, 0, -3, 0, 2, 0], -2⟩,
  ⟨1, ![1, 0, -3, 2, 0, 0], -2⟩,
  ⟨1, ![1, 0, 0, -3, 0, 2], 2⟩,
  ⟨1, ![1, 0, 0, -3, 2, 0], 2⟩,
  ⟨1, ![1, 0, 0, 0, -3, 2], 2⟩,
  ⟨1, ![1, 0, 0, 0, 2, -3], 2⟩,
  ⟨1, ![1, 0, 0, 2, -3, 0], 2⟩,
  ⟨1, ![1, 0, 0, 2, 0, -3], 2⟩,
  ⟨1, ![1, 0, 2, -3, 0, 0], -2⟩,
  ⟨1, ![1, 0, 2, 0, -3, 0], -2⟩,
  ⟨1, ![1, 0, 2, 0, 0, -3], -2⟩,
  ⟨1, ![1, 2, -3, 0, 0, 0], 6⟩,
  ⟨1, ![1, 2, 0, -3, 0, 0], -2⟩,
  ⟨1, ![1, 2, 0, 0, -3, 0], -2⟩,
  ⟨1, ![1, 2, 0, 0, 0, -3], -2⟩
]

def terms3 : Array TaggedTerm := #[
  ⟨1, ![3, -2, -1, 0, 0, 0], 6⟩,
  ⟨1, ![3, -2, 0, -1, 0, 0], -2⟩,
  ⟨1, ![3, -2, 0, 0, -1, 0], -2⟩,
  ⟨1, ![3, -2, 0, 0, 0, -1], -2⟩,
  ⟨1, ![3, -1, -2, 0, 0, 0], 6⟩,
  ⟨1, ![3, -1, 0, -2, 0, 0], -2⟩,
  ⟨1, ![3, -1, 0, 0, -2, 0], -2⟩,
  ⟨1, ![3, -1, 0, 0, 0, -2], -2⟩,
  ⟨1, ![3, 0, -2, -1, 0, 0], -2⟩,
  ⟨1, ![3, 0, -2, 0, -1, 0], -2⟩,
  ⟨1, ![3, 0, -2, 0, 0, -1], -2⟩,
  ⟨1, ![3, 0, -1, -2, 0, 0], -2⟩,
  ⟨1, ![3, 0, -1, 0, -2, 0], -2⟩,
  ⟨1, ![3, 0, -1, 0, 0, -2], -2⟩,
  ⟨1, ![3, 0, 0, -2, -1, 0], 2⟩,
  ⟨1, ![3, 0, 0, -2, 0, -1], 2⟩,
  ⟨1, ![3, 0, 0, -1, -2, 0], 2⟩,
  ⟨1, ![3, 0, 0, -1, 0, -2], 2⟩,
  ⟨1, ![3, 0, 0, 0, -2, -1], 2⟩,
  ⟨1, ![3, 0, 0, 0, -1, -2], 2⟩
]

def terms4 : Array TaggedTerm := #[
  ⟨0, ![2, -3, 0, 0, 0, 1], -2⟩,
  ⟨0, ![2, -3, 0, 0, 1, 0], -2⟩,
  ⟨0, ![2, -3, 0, 1, 0, 0], -2⟩,
  ⟨0, ![2, -3, 1, 0, 0, 0], 6⟩,
  ⟨0, ![2, 0, -3, 0, 0, 1], -2⟩,
  ⟨0, ![2, 0, -3, 0, 1, 0], -2⟩,
  ⟨0, ![2, 0, -3, 1, 0, 0], -2⟩,
  ⟨0, ![2, 0, 0, -3, 0, 1], 2⟩,
  ⟨0, ![2, 0, 0, -3, 1, 0], 2⟩,
  ⟨0, ![2, 0, 0, 0, -3, 1], 2⟩,
  ⟨0, ![2, 0, 0, 0, 1, -3], 2⟩,
  ⟨0, ![2, 0, 0, 1, -3, 0], 2⟩,
  ⟨0, ![2, 0, 0, 1, 0, -3], 2⟩,
  ⟨0, ![2, 0, 1, -3, 0, 0], -2⟩,
  ⟨0, ![2, 0, 1, 0, -3, 0], -2⟩,
  ⟨0, ![2, 0, 1, 0, 0, -3], -2⟩,
  ⟨0, ![2, 1, -3, 0, 0, 0], 6⟩,
  ⟨0, ![2, 1, 0, -3, 0, 0], -2⟩,
  ⟨0, ![2, 1, 0, 0, -3, 0], -2⟩,
  ⟨0, ![2, 1, 0, 0, 0, -3], -2⟩
]

def terms5 : Array TaggedTerm := #[
  ⟨0, ![1, 0, 0, -3, 1, 1], 4⟩,
  ⟨0, ![1, 0, 0, 1, -3, 1], 4⟩,
  ⟨0, ![1, 0, 0, 1, 1, -3], 4⟩,
  ⟨0, ![1, 0, 1, -3, 0, 1], -2⟩,
  ⟨0, ![1, 0, 1, -3, 1, 0], -2⟩,
  ⟨0, ![1, 0, 1, 0, -3, 1], -2⟩,
  ⟨0, ![1, 0, 1, 0, 1, -3], -2⟩,
  ⟨0, ![1, 0, 1, 1, -3, 0], -2⟩,
  ⟨0, ![1, 0, 1, 1, 0, -3], -2⟩,
  ⟨0, ![1, 1, 0, -3, 0, 1], -2⟩,
  ⟨0, ![1, 1, 0, -3, 1, 0], -2⟩,
  ⟨0, ![1, 1, 0, 0, -3, 1], -2⟩,
  ⟨0, ![1, 1, 0, 0, 1, -3], -2⟩,
  ⟨0, ![1, 1, 0, 1, -3, 0], -2⟩,
  ⟨0, ![1, 1, 0, 1, 0, -3], -2⟩,
  ⟨0, ![1, 1, 1, -3, 0, 0], 4⟩,
  ⟨0, ![1, 1, 1, 0, -3, 0], 4⟩,
  ⟨0, ![1, 1, 1, 0, 0, -3], 4⟩
]

def terms6 : Array TaggedTerm := #[
  ⟨1, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -1⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -1⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], -1⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], 2⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], -1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], -1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], -1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], -1⟩,
  ⟨1, ![1, 0, 0, -2, -1, 2], 2⟩,
  ⟨1, ![1, 0, 0, -2, 2, -1], 2⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 2⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 2⟩,
  ⟨1, ![1, 0, 0, 2, -2, -1], 2⟩,
  ⟨1, ![1, 0, 0, 2, -1, -2], 2⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], -1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], -1⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], -1⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], -1⟩,
  ⟨1, ![1, 0, 2, 0, -2, -1], -1⟩,
  ⟨1, ![1, 0, 2, 0, -1, -2], -1⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], 2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], 2⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], 2⟩,
  ⟨1, ![1, 2, 0, -2, -1, 0], -1⟩,
  ⟨1, ![1, 2, 0, -2, 0, -1], -1⟩,
  ⟨1, ![1, 2, 0, -1, -2, 0], -1⟩,
  ⟨1, ![1, 2, 0, -1, 0, -2], -1⟩,
  ⟨1, ![1, 2, 0, 0, -2, -1], -1⟩,
  ⟨1, ![1, 2, 0, 0, -1, -2], -1⟩
]

def terms7 : Array TaggedTerm := #[
  ⟨1, ![3, -1, -1, -1, 0, 0], 4⟩,
  ⟨1, ![3, -1, -1, 0, -1, 0], 4⟩,
  ⟨1, ![3, -1, -1, 0, 0, -1], 4⟩,
  ⟨1, ![3, -1, 0, -1, -1, 0], -4⟩,
  ⟨1, ![3, -1, 0, -1, 0, -1], -4⟩,
  ⟨1, ![3, -1, 0, 0, -1, -1], -4⟩,
  ⟨1, ![3, 0, -1, -1, -1, 0], -4⟩,
  ⟨1, ![3, 0, -1, -1, 0, -1], -4⟩,
  ⟨1, ![3, 0, -1, 0, -1, -1], -4⟩,
  ⟨1, ![3, 0, 0, -1, -1, -1], 12⟩
]

def terms8 : Array TaggedTerm := #[
  ⟨1, ![2, -3, 0, 0, 0, 1], -2⟩,
  ⟨1, ![2, -3, 0, 0, 1, 0], -2⟩,
  ⟨1, ![2, -3, 0, 1, 0, 0], -2⟩,
  ⟨1, ![2, -3, 1, 0, 0, 0], 6⟩,
  ⟨1, ![2, 0, -3, 0, 0, 1], -2⟩,
  ⟨1, ![2, 0, -3, 0, 1, 0], -2⟩,
  ⟨1, ![2, 0, -3, 1, 0, 0], -2⟩,
  ⟨1, ![2, 0, 0, -3, 0, 1], 2⟩,
  ⟨1, ![2, 0, 0, -3, 1, 0], 2⟩,
  ⟨1, ![2, 0, 0, 0, -3, 1], 2⟩,
  ⟨1, ![2, 0, 0, 0, 1, -3], 2⟩,
  ⟨1, ![2, 0, 0, 1, -3, 0], 2⟩,
  ⟨1, ![2, 0, 0, 1, 0, -3], 2⟩,
  ⟨1, ![2, 0, 1, -3, 0, 0], -2⟩,
  ⟨1, ![2, 0, 1, 0, -3, 0], -2⟩,
  ⟨1, ![2, 0, 1, 0, 0, -3], -2⟩,
  ⟨1, ![2, 1, -3, 0, 0, 0], 6⟩,
  ⟨1, ![2, 1, 0, -3, 0, 0], -2⟩,
  ⟨1, ![2, 1, 0, 0, -3, 0], -2⟩,
  ⟨1, ![2, 1, 0, 0, 0, -3], -2⟩
]

def terms9 : Array TaggedTerm := #[
  ⟨0, ![3, -1, -1, -1, 0, 0], 4⟩,
  ⟨0, ![3, -1, -1, 0, -1, 0], 4⟩,
  ⟨0, ![3, -1, -1, 0, 0, -1], 4⟩,
  ⟨0, ![3, -1, 0, -1, -1, 0], -4⟩,
  ⟨0, ![3, -1, 0, -1, 0, -1], -4⟩,
  ⟨0, ![3, -1, 0, 0, -1, -1], -4⟩,
  ⟨0, ![3, 0, -1, -1, -1, 0], -4⟩,
  ⟨0, ![3, 0, -1, -1, 0, -1], -4⟩,
  ⟨0, ![3, 0, -1, 0, -1, -1], -4⟩,
  ⟨0, ![3, 0, 0, -1, -1, -1], 12⟩
]

end MUB6.Certificate.GramFunctions.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block5

def terms0 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 0, 2], 6⟩,
  ⟨1, ![1, -3, 0, 0, 2, 0], 6⟩,
  ⟨1, ![1, -3, 0, 2, 0, 0], 6⟩,
  ⟨1, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨1, ![1, 0, -3, 0, 0, 2], 6⟩,
  ⟨1, ![1, 0, -3, 0, 2, 0], 6⟩,
  ⟨1, ![1, 0, -3, 2, 0, 0], 6⟩,
  ⟨1, ![1, 0, 0, -3, 0, 2], 6⟩,
  ⟨1, ![1, 0, 0, -3, 2, 0], 6⟩,
  ⟨1, ![1, 0, 0, 0, -3, 2], 6⟩,
  ⟨1, ![1, 0, 0, 0, 2, -3], 6⟩,
  ⟨1, ![1, 0, 0, 2, -3, 0], 6⟩,
  ⟨1, ![1, 0, 0, 2, 0, -3], 6⟩,
  ⟨1, ![1, 0, 2, -3, 0, 0], 6⟩,
  ⟨1, ![1, 0, 2, 0, -3, 0], 6⟩,
  ⟨1, ![1, 0, 2, 0, 0, -3], 6⟩,
  ⟨1, ![1, 2, -3, 0, 0, 0], 6⟩,
  ⟨1, ![1, 2, 0, -3, 0, 0], 6⟩,
  ⟨1, ![1, 2, 0, 0, -3, 0], 6⟩,
  ⟨1, ![1, 2, 0, 0, 0, -3], 6⟩
]

def terms10 : Array TaggedTerm := #[
  ⟨0, ![0, -2, 0, 0, 0, 2], 6⟩,
  ⟨0, ![0, -2, 0, 0, 2, 0], 6⟩,
  ⟨0, ![0, -2, 0, 2, 0, 0], 6⟩,
  ⟨0, ![0, -2, 2, 0, 0, 0], 6⟩,
  ⟨0, ![0, 0, -2, 0, 0, 2], 6⟩,
  ⟨0, ![0, 0, -2, 0, 2, 0], 6⟩,
  ⟨0, ![0, 0, -2, 2, 0, 0], 6⟩,
  ⟨0, ![0, 0, 0, -2, 0, 2], 6⟩,
  ⟨0, ![0, 0, 0, -2, 2, 0], 6⟩,
  ⟨0, ![0, 0, 0, 0, -2, 2], 6⟩,
  ⟨0, ![0, 0, 0, 0, 2, -2], 6⟩,
  ⟨0, ![0, 0, 0, 2, -2, 0], 6⟩,
  ⟨0, ![0, 0, 0, 2, 0, -2], 6⟩,
  ⟨0, ![0, 0, 2, -2, 0, 0], 6⟩,
  ⟨0, ![0, 0, 2, 0, -2, 0], 6⟩,
  ⟨0, ![0, 0, 2, 0, 0, -2], 6⟩,
  ⟨0, ![0, 2, -2, 0, 0, 0], 6⟩,
  ⟨0, ![0, 2, 0, -2, 0, 0], 6⟩,
  ⟨0, ![0, 2, 0, 0, -2, 0], 6⟩,
  ⟨0, ![0, 2, 0, 0, 0, -2], 6⟩
]

def terms11 : Array TaggedTerm := #[
  ⟨0, ![1, -2, -1, 0, 0, 2], 2⟩,
  ⟨0, ![1, -2, -1, 0, 2, 0], 2⟩,
  ⟨0, ![1, -2, -1, 2, 0, 0], 2⟩,
  ⟨0, ![1, -2, 0, -1, 0, 2], 2⟩,
  ⟨0, ![1, -2, 0, -1, 2, 0], 2⟩,
  ⟨0, ![1, -2, 0, 0, -1, 2], 2⟩,
  ⟨0, ![1, -2, 0, 0, 2, -1], 2⟩,
  ⟨0, ![1, -2, 0, 2, -1, 0], 2⟩,
  ⟨0, ![1, -2, 0, 2, 0, -1], 2⟩,
  ⟨0, ![1, -2, 2, -1, 0, 0], 2⟩,
  ⟨0, ![1, -2, 2, 0, -1, 0], 2⟩,
  ⟨0, ![1, -2, 2, 0, 0, -1], 2⟩,
  ⟨0, ![1, -1, -2, 0, 0, 2], 2⟩,
  ⟨0, ![1, -1, -2, 0, 2, 0], 2⟩,
  ⟨0, ![1, -1, -2, 2, 0, 0], 2⟩,
  ⟨0, ![1, -1, 0, -2, 0, 2], 2⟩,
  ⟨0, ![1, -1, 0, -2, 2, 0], 2⟩,
  ⟨0, ![1, -1, 0, 0, -2, 2], 2⟩,
  ⟨0, ![1, -1, 0, 0, 2, -2], 2⟩,
  ⟨0, ![1, -1, 0, 2, -2, 0], 2⟩,
  ⟨0, ![1, -1, 0, 2, 0, -2], 2⟩,
  ⟨0, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨0, ![1, -1, 2, 0, -2, 0], 2⟩,
  ⟨0, ![1, -1, 2, 0, 0, -2], 2⟩,
  ⟨0, ![1, 0, -2, -1, 0, 2], 2⟩,
  ⟨0, ![1, 0, -2, -1, 2, 0], 2⟩,
  ⟨0, ![1, 0, -2, 0, -1, 2], 2⟩,
  ⟨0, ![1, 0, -2, 0, 2, -1], 2⟩,
  ⟨0, ![1, 0, -2, 2, -1, 0], 2⟩,
  ⟨0, ![1, 0, -2, 2, 0, -1], 2⟩,
  ⟨0, ![1, 0, -1, -2, 0, 2], 2⟩,
  ⟨0, ![1, 0, -1, -2, 2, 0], 2⟩,
  ⟨0, ![1, 0, -1, 0, -2, 2], 2⟩,
  ⟨0, ![1, 0, -1, 0, 2, -2], 2⟩,
  ⟨0, ![1, 0, -1, 2, -2, 0], 2⟩,
  ⟨0, ![1, 0, -1, 2, 0, -2], 2⟩,
  ⟨0, ![1, 0, 0, -2, -1, 2], 2⟩,
  ⟨0, ![1, 0, 0, -2, 2, -1], 2⟩,
  ⟨0, ![1, 0, 0, -1, -2, 2], 2⟩,
  ⟨0, ![1, 0, 0, -1, 2, -2], 2⟩,
  ⟨0, ![1, 0, 0, 2, -2, -1], 2⟩,
  ⟨0, ![1, 0, 0, 2, -1, -2], 2⟩,
  ⟨0, ![1, 0, 2, -2, -1, 0], 2⟩,
  ⟨0, ![1, 0, 2, -2, 0, -1], 2⟩,
  ⟨0, ![1, 0, 2, -1, -2, 0], 2⟩,
  ⟨0, ![1, 0, 2, -1, 0, -2], 2⟩,
  ⟨0, ![1, 0, 2, 0, -2, -1], 2⟩,
  ⟨0, ![1, 0, 2, 0, -1, -2], 2⟩,
  ⟨0, ![1, 2, -2, -1, 0, 0], 2⟩,
  ⟨0, ![1, 2, -2, 0, -1, 0], 2⟩,
  ⟨0, ![1, 2, -2, 0, 0, -1], 2⟩,
  ⟨0, ![1, 2, -1, -2, 0, 0], 2⟩,
  ⟨0, ![1, 2, -1, 0, -2, 0], 2⟩,
  ⟨0, ![1, 2, -1, 0, 0, -2], 2⟩,
  ⟨0, ![1, 2, 0, -2, -1, 0], 2⟩,
  ⟨0, ![1, 2, 0, -2, 0, -1], 2⟩,
  ⟨0, ![1, 2, 0, -1, -2, 0], 2⟩,
  ⟨0, ![1, 2, 0, -1, 0, -2], 2⟩,
  ⟨0, ![1, 2, 0, 0, -2, -1], 2⟩,
  ⟨0, ![1, 2, 0, 0, -1, -2], 2⟩
]

end MUB6.Certificate.GramFunctions.Block5

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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

def row20301 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20302 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 4), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20303 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 4), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20304 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20305 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20306 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20307 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20308 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 2), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20309 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 2), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20310 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20311 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20312 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20313 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20314 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

end MUB6.Certificate.GramRows

end OAI
end


