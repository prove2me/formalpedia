-- Prove2me | Definitions.Def_OAIQ106D150
-- name    : OAIQ106D150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:01:54.258526+00:00
-- url     : https://prove2.me/theorems/13cc67e9-8fb2-4e57-87ab-3a4a5550d621
-- title:
--   Definitions bundle OAIQ106D150 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1240 declarations of OpenAI's Lean: 1240 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block4.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_7` and 1200 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block4Data`, `MutuallyUnbiased_GramFunctions_Block3`, `MutuallyUnbiased_GramFunctions_Block4`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block135`, `MutuallyUnbiased_GramRows_Block136`, `MutuallyUnbiased_GramRows_Block137`, `MutuallyUnbiased_GramRows_Block138`, `MutuallyUnbiased_GramRows_Block139`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block155`, `MutuallyUnbiased_GramRows_Block84`, `MutuallyUnbiased_GramRows_Block85`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block87`, `MutuallyUnbiased_GramRows_Block88`, `MutuallyUnbiased_GramRows_Block89`, `MutuallyUnbiased_GramRows_Block90`.
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091` and `OAIQ106D092` of this split.
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

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2362, 144), (key2365, -288), (key2367, 144), (key2457, 144), (key2460, -144), (key2521, -320), (key2525, 240), (key2532, 32), (key2533, 48), (key2562, 144), (key2564, -144)]

def entry1_0 : Integer.Sparse Key := [(key1090, -288), (key1098, 288), (key1180, 288), (key1183, -288)]

def entry1_1 : Integer.Sparse Key := [(key1, 144), (key7, -144), (key84, -144), (key90, 288), (key151, -256), (key193, -32), (key202, 144)]

def entry2_0 : Integer.Sparse Key := [(key2357, -48), (key2361, 48), (key2363, 24), (key2366, -24), (key2452, -216), (key2456, -72), (key2458, 192), (key2461, 96), (key2517, 152), (key2523, -144), (key2528, 136), (key2530, -144), (key2560, -16), (key2579, 16)]

def entry2_1 : Integer.Sparse Key := [(key971, 144), (key979, -144), (key1085, -144), (key1093, 288), (key1164, -144), (key1228, -144), (key1245, 144)]

def entry2_2 : Integer.Sparse Key := [(key2353, 144), (key2359, -144), (key2448, -144), (key2454, 288), (key2515, -256), (key2566, -32), (key2578, 144)]

def entry3_0 : Integer.Sparse Key := [(key2471, 288), (key2479, -288), (key2502, -288), (key2518, 288)]

def entry3_1 : Integer.Sparse Key := [(key995, -144), (key1011, 144), (key1030, -144), (key1067, 144), (key1108, 288), (key1119, -144), (key1146, -144)]

def entry3_2 : Integer.Sparse Key := [(key2372, -144), (key2385, 144), (key2400, -144), (key2432, 144), (key2466, 288), (key2475, -144), (key2498, -144)]

def entry3_3 : Integer.Sparse Key := [(key2606, 144), (key2622, -144), (key2661, 144), (key2696, -160), (key2776, -128), (key2799, -144), (key2849, 288)]

def entry4_0 : Integer.Sparse Key := [(key1090, -288), (key1097, 288), (key1180, 288), (key1182, -288)]

def entry4_1 : Integer.Sparse Key := [(key2, 144), (key6, -144), (key85, -144), (key89, 288), (key150, -144), (key166, -144), (key186, 144)]

def entry4_3 : Integer.Sparse Key := [(key992, -144), (key1010, 144), (key1027, -144), (key1066, 144), (key1105, 288), (key1118, -144), (key1145, -144)]

def entry4_4 : Integer.Sparse Key := [(key1, 144), (key4, -144), (key84, -144), (key87, 288), (key148, -256), (key164, -32), (key184, 144)]

def entry5_0 : Integer.Sparse Key := [(key982, 144), (key986, -288), (key988, 144), (key1096, 144), (key1100, -144), (key1171, -144), (key1175, 144), (key1185, -144), (key1186, 144), (key1222, 144), (key1224, -144)]

def entry5_1 : Integer.Sparse Key := [(key5, -48), (key9, 48), (key11, 24), (key14, -24), (key88, -216), (key92, -72), (key94, 192), (key97, 96), (key153, 152), (key161, -144), (key165, 136), (key167, -144), (key187, -16), (key203, 16)]

def entry5_2 : Integer.Sparse Key := [(key1095, -288), (key1101, 288), (key1166, 288), (key1173, -288)]

def entry5_3 : Integer.Sparse Key := [(key1115, 288), (key1124, -288), (key1151, -288), (key1167, 288)]

def entry5_4 : Integer.Sparse Key := [(key92, -288), (key95, 288), (key153, 288), (key157, -288)]

def entry5_5 : Integer.Sparse Key := [(key10, 144), (key13, -288), (key15, 144), (key93, 144), (key96, -144), (key158, -320), (key163, 240), (key169, 32), (key170, 48), (key189, 144), (key192, -144)]

def entry6_1 : Integer.Sparse Key := [(key1028, 144), (key1036, -144), (key1106, -144), (key1114, 288), (key1123, -144), (key1232, -144), (key1235, 144)]

def entry6_2 : Integer.Sparse Key := [(key2370, 24), (key2376, 12), (key2388, -20), (key2398, 120), (key2404, -72), (key2435, -8), (key2464, -100), (key2470, 144), (key2478, -108), (key2501, -12), (key2568, -36), (key2570, 68), (key2575, 20), (key2583, -24), (key2589, -12), (key2604, 20), (key2762, 24), (key2768, -72), (key2839, -44), (key2845, 144), (key2876, -108), (key2916, -36), (key2925, 76), (key3005, 8), (key3019, 12), (key3028, -20)]

def entry6_3 : Integer.Sparse Key := [(key2780, -144), (key2789, 144), (key2803, -144), (key2824, 144), (key2853, 288), (key2855, -144), (key2865, -144)]

def entry6_5 : Integer.Sparse Key := [(key1003, -144), (key1009, 144), (key1017, 144), (key1022, -144), (key1038, -72), (key1044, 72), (key1073, 72), (key1080, -72), (key1116, -72), (key1125, 144), (key1130, -72), (key1152, -72), (key1159, 144), (key1174, -72), (key1233, 72), (key1236, -72), (key1243, -72), (key1247, 72)]

def entry7_0 : Integer.Sparse Key := [(key2420, 288), (key2427, -576), (key2438, 288)]

def entry7_1 : Integer.Sparse Key := [(key1050, -288), (key1058, 288), (key1136, 288), (key1138, -288)]

def entry7_2 : Integer.Sparse Key := [(key2416, -288), (key2423, 288), (key2489, 288), (key2491, -288)]

def entry7_3 : Integer.Sparse Key := [(key2677, 336), (key2708, -240), (key2811, -224), (key2861, 192), (key3045, -48), (key3059, -48), (key3094, -64), (key3122, 96)]

def entry7_5 : Integer.Sparse Key := [(key1055, 288), (key1063, -576), (key1074, 288)]

def entry7_6 : Integer.Sparse Key := [(key2681, -288), (key2688, 288), (key2712, 288), (key2714, -288)]

def entry7_7 : Integer.Sparse Key := [(key3079, 288), (key3084, -576), (key3099, 288)]

def entry8_0 : Integer.Sparse Key := [(key2456, -288), (key2459, 288), (key2517, 288), (key2520, -288)]

def entry8_1 : Integer.Sparse Key := [(key972, 144), (key977, -144), (key1086, -144), (key1091, 288), (key1162, -144), (key1181, -144), (key1218, 144)]

def entry8_2 : Integer.Sparse Key := [(key2354, 144), (key2358, -144), (key2449, -144), (key2453, 288), (key2514, -144), (key2529, -144), (key2559, 144)]

def entry8_3 : Integer.Sparse Key := [(key2369, -144), (key2384, 144), (key2397, -144), (key2431, 144), (key2463, 288), (key2474, -144), (key2497, -144)]

def entry8_5 : Integer.Sparse Key := [(key1095, -288), (key1099, 288), (key1166, 288), (key1170, -288)]

def entry8_6 : Integer.Sparse Key := [(key2763, 144), (key2767, -144), (key2840, -144), (key2844, 288), (key2875, -144), (key2888, -144), (key2909, 144)]

def entry8_7 : Integer.Sparse Key := [(key2413, -288), (key2422, 288), (key2486, 288), (key2490, -288)]

def entry8_8 : Integer.Sparse Key := [(key2353, 144), (key2356, -144), (key2448, -144), (key2451, 288), (key2513, -256), (key2527, -32), (key2558, 144)]

def entry10_1 : Integer.Sparse Key := [(key1029, 144), (key1034, -144), (key1107, -144), (key1112, 288), (key1121, -144), (key1191, -144), (key1197, 144)]

def entry10_2 : Integer.Sparse Key := [(key2399, 144), (key2403, -144), (key2465, -144), (key2469, 288), (key2477, -144), (key2536, -144), (key2541, 144)]

def entry10_3 : Integer.Sparse Key := [(key2777, -144), (key2788, 144), (key2800, -144), (key2823, 144), (key2850, 288), (key2854, -144), (key2864, -144)]

def entry10_5 : Integer.Sparse Key := [(key1003, -144), (key1007, 144), (key1017, 144), (key1020, -144), (key1038, -72), (key1042, 72), (key1073, 72), (key1077, -72), (key1116, -72), (key1125, 144), (key1128, -72), (key1152, -72), (key1156, 144), (key1172, -72), (key1194, 72), (key1200, -72), (key1213, -72), (key1223, 72)]

def entry10_8 : Integer.Sparse Key := [(key2370, 24), (key2373, 12), (key2386, -20), (key2398, 120), (key2401, -72), (key2433, -8), (key2464, -100), (key2467, 144), (key2476, -108), (key2499, -12), (key2534, -36), (key2540, 68), (key2551, 20), (key2583, -24), (key2586, -12), (key2597, 20), (key2762, 24), (key2765, -72), (key2839, -44), (key2842, 144), (key2874, -108), (key2886, -36), (key2908, 76), (key2928, 8), (key2965, 12), (key2987, -20)]

def entry11_0 : Integer.Sparse Key := [(key1700, -288), (key1706, 288), (key1851, 288), (key1855, -288)]

def entry11_2 : Integer.Sparse Key := [(key1273, 144), (key1278, -144), (key1696, -144), (key1701, 288), (key1751, -144), (key1933, -144), (key1953, 144)]

def entry11_4 : Integer.Sparse Key := [(key221, 144), (key225, -144), (key493, -144), (key497, 288), (key551, -144), (key619, -144), (key645, 144)]

def entry11_5 : Integer.Sparse Key := [(key496, -288), (key502, 288), (key618, 288), (key622, -288)]

def entry11_6 : Integer.Sparse Key := [(key1484, 144), (key1490, -144), (key1710, -144), (key1716, 288), (key1723, -144), (key1937, -144), (key1940, 144)]

def entry11_8 : Integer.Sparse Key := [(key1274, 144), (key1278, -144), (key1697, -144), (key1701, 288), (key1751, -144), (key1852, -144), (key1884, 144)]

def entry11_10 : Integer.Sparse Key := [(key1485, 144), (key1490, -144), (key1711, -144), (key1716, 288), (key1723, -144), (key1861, -144), (key1867, 144)]

def entry11_11 : Integer.Sparse Key := [(key288, 144), (key289, -144), (key513, -144), (key515, 288), (key547, -256), (key670, -32), (key680, 144)]

def entry12_0 : Integer.Sparse Key := [(key2362, 72), (key2365, -144), (key2367, 72), (key2457, 216), (key2460, -216), (key2521, -40), (key2525, 72), (key2532, -104), (key2533, 72), (key2562, -72), (key2564, 72)]

def entry12_1 : Integer.Sparse Key := [(key976, -144), (key984, 144), (key1090, -144), (key1169, 144), (key1180, 288), (key1183, -144), (key1220, -144)]

def entry12_2 : Integer.Sparse Key := [(key2357, -48), (key2361, -96), (key2363, 68), (key2366, 76), (key2452, -132), (key2456, -12), (key2458, 48), (key2461, -48), (key2517, 180), (key2519, 108), (key2523, -24), (key2528, 108), (key2530, -120), (key2560, -72), (key2567, 36), (key2579, -72)]

def entry12_3 : Integer.Sparse Key := [(key2377, 144), (key2389, -144), (key2405, 144), (key2436, -144), (key2479, -144), (key2502, -144), (key2518, 288)]

def entry12_4 : Integer.Sparse Key := [(key976, -144), (key983, 144), (key1090, -144), (key1168, 144), (key1180, 288), (key1182, -144), (key1219, -144)]

def entry12_5 : Integer.Sparse Key := [(key982, 72), (key986, -144), (key988, 72), (key1096, 216), (key1100, -216), (key1171, -216), (key1175, 216), (key1185, 72), (key1186, -72), (key1222, -72), (key1224, 72)]

def entry12_7 : Integer.Sparse Key := [(key2420, 288), (key2427, -288), (key2495, -288), (key2504, 288)]

def entry12_11 : Integer.Sparse Key := [(key1277, -144), (key1283, 144), (key1700, -144), (key1756, 144), (key1851, 288), (key1855, -144), (key1886, -144)]

def entry12_12 : Integer.Sparse Key := [(key2362, 108), (key2365, -72), (key2367, -36), (key2457, 180), (key2460, -36), (key2521, -104), (key2525, -36), (key2532, -256), (key2533, 108), (key2562, -108), (key2564, 252)]

def entry13_1 : Integer.Sparse Key := [(key1001, -144), (key1015, 144), (key1036, -144), (key1071, 144), (key1114, 288), (key1123, -144), (key1150, -144)]

def entry13_2 : Integer.Sparse Key := [(key2370, 24), (key2376, -36), (key2388, 76), (key2398, 24), (key2404, -36), (key2435, 76), (key2464, -24), (key2470, 96), (key2478, -72), (key2501, -72), (key2570, 8), (key2575, 8), (key2583, -24), (key2589, -108), (key2604, 68), (key2762, -24), (key2768, -108), (key2839, 24), (key2845, 192), (key2916, -72), (key2925, -8), (key3005, 68), (key3019, -72), (key3028, -8)]

def entry13_3 : Integer.Sparse Key := [(key2610, 144), (key2626, -144), (key2665, 144), (key2700, -144), (key2780, -144), (key2803, -144), (key2853, 288)]

def entry13_4 : Integer.Sparse Key := [(key1000, -144), (key1014, 144), (key1035, -144), (key1070, 144), (key1113, 288), (key1122, -144), (key1149, -144)]

def entry13_5 : Integer.Sparse Key := [(key1003, -72), (key1009, 72), (key1017, 72), (key1022, -72), (key1038, -72), (key1044, 72), (key1073, 72), (key1080, -72), (key1116, 144), (key1125, -72), (key1130, -72), (key1152, -72), (key1159, -72), (key1174, 144), (key1233, 144), (key1236, -144), (key1243, -144), (key1247, 144)]

def entry13_7 : Integer.Sparse Key := [(key2688, 288), (key2714, -288), (key2817, -288), (key2863, 288)]

def entry13_8 : Integer.Sparse Key := [(key2588, -144), (key2599, 144), (key2767, -144), (key2844, 288), (key2888, -144), (key2930, 144), (key2967, -144)]

def entry14_1 : Integer.Sparse Key := [(key993, 144), (key1001, -144), (key1028, -144), (key1036, 144), (key1123, 144), (key1150, -144), (key1235, -144), (key1242, 144)]

def entry14_3 : Integer.Sparse Key := [(key2626, -144), (key2635, 144), (key2700, -144), (key2721, 144), (key2780, 144), (key2789, -144), (key2803, 144), (key2824, -144)]

def entry14_4 : Integer.Sparse Key := [(key994, 144), (key1000, -144), (key1029, -144), (key1035, 144), (key1122, 144), (key1149, -144), (key1234, -144), (key1241, 144)]

def entry14_5 : Integer.Sparse Key := [(key1003, 72), (key1009, -72), (key1017, -72), (key1022, 72), (key1038, -72), (key1044, 72), (key1073, 72), (key1080, -72), (key1125, -216), (key1130, 216), (key1152, 216), (key1159, -216)]

def entry14_7 : Integer.Sparse Key := [(key2712, -288), (key2714, 288), (key2815, 288), (key2817, -288)]

def entry14_8 : Integer.Sparse Key := [(key2584, 144), (key2588, -144), (key2763, -144), (key2767, 144), (key2888, 144), (key2909, -144), (key2967, -144), (key2988, 144)]

def entry14_11 : Integer.Sparse Key := [(key1358, 144), (key1364, -144), (key1484, -144), (key1490, 144), (key1723, 144), (key1741, -144), (key1940, -144), (key1949, 144)]

def entry15_5 : Integer.Sparse Key := [(key1003, 72), (key1007, -72), (key1017, -72), (key1020, 72), (key1038, -72), (key1042, 72), (key1073, 72), (key1077, -72), (key1125, -216), (key1128, 216), (key1152, 216), (key1156, -216)]

def entry15_7 : Integer.Sparse Key := [(key2709, -288), (key2713, 288), (key2812, 288), (key2816, -288)]

def entry15_11 : Integer.Sparse Key := [(key1359, 144), (key1364, -144), (key1485, -144), (key1490, 144), (key1723, 144), (key1741, -144), (key1867, -144), (key1877, 144)]

def entry16_1 : Integer.Sparse Key := [(key1033, -144), (key1041, 144), (key1111, -144), (key1127, 144), (key1190, 288), (key1193, -144), (key1199, -144)]

def entry16_3 : Integer.Sparse Key := [(key2785, 144), (key2793, -144), (key2808, 144), (key2828, -144), (key2859, -144), (key2869, -144), (key2879, 288)]

def entry16_4 : Integer.Sparse Key := [(key1033, -144), (key1040, 144), (key1111, -144), (key1126, 144), (key1190, 288), (key1192, -144), (key1198, -144)]

def entry16_5 : Integer.Sparse Key := [(key1004, 144), (key1008, -144), (key1021, -144), (key1023, 144), (key1039, 72), (key1043, -72), (key1078, -72), (key1081, 72), (key1117, 72), (key1129, -72), (key1157, -72), (key1176, 72), (key1195, -72), (key1201, -72), (key1202, 144), (key1214, 144), (key1216, -72), (key1225, -72)]

def entry16_7 : Integer.Sparse Key := [(key2685, 288), (key2692, -288), (key2718, -288), (key2727, 288)]

def entry16_11 : Integer.Sparse Key := [(key1489, -144), (key1495, 144), (key1715, -144), (key1727, 144), (key1860, 288), (key1864, -144), (key1869, -144)]

def entry16_16 : Integer.Sparse Key := [(key2617, 72), (key2620, -72), (key2633, 72), (key2643, -84), (key2650, -60), (key2655, -72), (key2656, 144), (key2672, 36), (key2675, -36), (key2707, 56), (key2730, -72), (key2739, -36), (key2749, -80), (key2751, 120), (key2787, 16), (key2797, -36), (key2810, 36), (key2833, -80), (key2899, -36), (key2906, -72), (key2915, 120), (key2945, 8), (key2946, 24), (key2952, 8), (key2962, 72), (key2964, -36), (key2985, 72), (key2994, -60), (key2999, 24), (key3001, -12), (key3004, -36)]

def entry17_0 : Integer.Sparse Key := [(key1989, -144), (key1994, 144), (key1999, 144), (key2003, -144), (key2234, 144), (key2259, 144), (key2268, -144), (key2272, -144), (key2294, -288), (key2324, 144), (key2336, 144)]

def entry17_2 : Integer.Sparse Key := [(key1990, -288), (key2007, 288), (key2235, 288), (key2300, -288)]

def entry17_4 : Integer.Sparse Key := [(key706, -288), (key715, 288), (key860, 288), (key892, -288)]

def entry17_5 : Integer.Sparse Key := [(key705, -144), (key710, 144), (key714, 144), (key718, -144), (key859, 144), (key886, 144), (key891, -144), (key895, -144), (key916, -288), (key948, 144), (key955, 144)]

def entry17_6 : Integer.Sparse Key := [(key2027, 72), (key2033, -72), (key2057, -72), (key2063, 144), (key2069, -72), (key2092, -72), (key2095, 72), (key2146, -72), (key2152, -72), (key2166, -144), (key2194, 144), (key2200, 144), (key2239, 72), (key2246, 72), (key2253, 144), (key2303, -72), (key2305, -72), (key2310, -144)]

def entry17_8 : Integer.Sparse Key := [(key1990, -288), (key2000, 288), (key2235, 288), (key2269, -288)]

def entry17_10 : Integer.Sparse Key := [(key2028, 72), (key2033, -72), (key2058, -72), (key2063, 144), (key2069, -72), (key2079, -72), (key2085, 72), (key2147, -72), (key2152, -72), (key2166, -144), (key2176, 144), (key2187, 144), (key2240, 72), (key2246, 72), (key2253, 144), (key2276, -72), (key2279, -72), (key2287, -144)]

def entry17_11 : Integer.Sparse Key := [(key360, 48), (key362, -72), (key366, 152), (key529, -24), (key531, 96), (key537, -144), (key676, 16), (key731, -48), (key733, -216), (key750, 136), (key865, 24), (key867, 192), (key927, -144), (key938, -16)]

def entry17_12 : Integer.Sparse Key := [(key1989, 72), (key1994, 216), (key1999, -72), (key2003, -216), (key2234, -72), (key2259, 72), (key2268, 72), (key2272, -216), (key2294, -144), (key2324, 216), (key2336, 72)]

def entry17_13 : Integer.Sparse Key := [(key2027, 144), (key2033, 144), (key2057, -144), (key2063, -72), (key2069, -72), (key2092, -72), (key2095, 72), (key2146, -144), (key2152, -72), (key2166, -72), (key2194, -72), (key2200, 72), (key2239, 144), (key2246, 72), (key2253, 72), (key2303, 144), (key2305, -72), (key2310, -72)]

def entry17_17 : Integer.Sparse Key := [(key776, 144), (key778, 144), (key801, -288), (key803, -144), (key811, -320), (key836, 32), (key839, 144), (key871, 144), (key876, 240), (key931, 48), (key934, -144)]

def entry19_0 : Integer.Sparse Key := [(key1854, 288), (key1856, -576), (key1858, 288)]

def entry19_2 : Integer.Sparse Key := [(key1853, -288), (key1857, 288), (key1885, 288), (key1888, -288)]

def entry19_4 : Integer.Sparse Key := [(key665, -288), (key666, 288), (key682, 288), (key683, -288)]

def entry19_5 : Integer.Sparse Key := [(key621, 288), (key623, -576), (key625, 288)]

def entry19_6 : Integer.Sparse Key := [(key1862, -288), (key1866, 288), (key1868, 288), (key1871, -288)]

def entry19_8 : Integer.Sparse Key := [(key1934, -288), (key1935, 288), (key1954, 288), (key1955, -288)]

def entry19_10 : Integer.Sparse Key := [(key1938, -288), (key1939, 288), (key1941, 288), (key1942, -288)]

def entry19_11 : Integer.Sparse Key := [(key517, -288), (key524, 288), (key549, 288), (key555, -288)]

def entry19_12 : Integer.Sparse Key := [(key1854, 288), (key1856, -288), (key1887, -288), (key1890, 288)]

def entry19_13 : Integer.Sparse Key := [(key1866, 288), (key1871, -288), (key1881, -288), (key1889, 288)]

def entry19_14 : Integer.Sparse Key := [(key1868, -288), (key1871, 288), (key1878, 288), (key1881, -288)]

def entry19_15 : Integer.Sparse Key := [(key1941, -288), (key1942, 288), (key1950, 288), (key1951, -288)]

def entry19_19 : Integer.Sparse Key := [(key291, 288), (key294, -576), (key298, 288)]

def entry20_0 : Integer.Sparse Key := [(key1992, -144), (key1995, 144), (key2002, 144), (key2004, -144), (key2237, 144), (key2260, 144), (key2271, -144), (key2273, -144), (key2295, -288), (key2325, 144), (key2337, 144)]

def entry20_5 : Integer.Sparse Key := [(key78, 48), (key191, 16), (key708, -144), (key711, 144), (key717, 96), (key719, -144), (key862, 144), (key887, 144), (key894, -144), (key896, -144), (key917, -288), (key949, 144), (key956, 128)]

def entry20_6 : Integer.Sparse Key := [(key2031, 72), (key2036, -72), (key2061, -72), (key2066, 144), (key2071, -72), (key2093, -72), (key2096, 72), (key2150, -72), (key2155, -72), (key2168, -144), (key2195, 144), (key2201, 144), (key2243, 72), (key2248, 72), (key2255, 144), (key2304, -72), (key2306, -72), (key2311, -144)]

def entry20_10 : Integer.Sparse Key := [(key2031, 72), (key2034, -72), (key2061, -72), (key2064, 144), (key2070, -72), (key2080, -72), (key2086, 72), (key2150, -72), (key2153, -72), (key2167, -144), (key2177, 144), (key2188, 144), (key2243, 72), (key2247, 72), (key2254, 144), (key2277, -72), (key2280, -72), (key2288, -144)]

def entry20_12 : Integer.Sparse Key := [(key1992, 72), (key1995, 216), (key2002, -72), (key2004, -216), (key2237, -72), (key2260, 72), (key2271, 72), (key2273, -216), (key2295, -144), (key2325, 216), (key2337, 72)]

def entry20_13 : Integer.Sparse Key := [(key2031, 144), (key2036, 144), (key2061, -144), (key2066, -72), (key2071, -72), (key2093, -72), (key2096, 72), (key2150, -144), (key2155, -72), (key2168, -72), (key2195, -72), (key2201, 72), (key2243, 144), (key2248, 72), (key2255, 72), (key2304, 144), (key2306, -72), (key2311, -72)]

def entry20_14 : Integer.Sparse Key := [(key2066, -216), (key2071, -72), (key2093, 216), (key2096, 72), (key2155, 216), (key2168, 72), (key2195, -216), (key2201, -72), (key2248, 72), (key2255, -72), (key2306, -72), (key2311, 72)]

def entry20_15 : Integer.Sparse Key := [(key2064, -216), (key2070, -72), (key2080, 216), (key2086, 72), (key2153, 216), (key2167, 72), (key2177, -216), (key2188, -72), (key2247, 72), (key2254, -72), (key2280, -72), (key2288, 72)]

def entry20_16 : Integer.Sparse Key := [(key2035, -72), (key2038, 72), (key2065, -72), (key2073, 72), (key2081, 144), (key2083, -72), (key2088, -72), (key2154, 144), (key2170, 144), (key2178, -72), (key2180, -72), (key2190, -144), (key2278, -72), (key2282, -72), (key2290, -144), (key2329, 72), (key2331, 72), (key2334, 144)]

def entry20_20 : Integer.Sparse Key := [(key781, 144), (key784, 144), (key806, -288), (key809, -144), (key814, -320), (key822, 32), (key827, 144), (key875, 144), (key879, 240), (key906, 48), (key910, -144)]

def entry21_0 : Integer.Sparse Key := [(key2421, -288), (key2428, 288), (key2429, 288), (key2442, -288)]

def entry21_1 : Integer.Sparse Key := [(key1049, 144), (key1052, 144), (key1060, -288), (key1135, -144), (key1140, 144), (key1205, -144), (key1207, 144)]

def entry21_2 : Integer.Sparse Key := [(key2415, 144), (key2418, 144), (key2425, -288), (key2488, -144), (key2493, 144), (key2547, -144), (key2549, 144)]

def entry21_3 : Integer.Sparse Key := [(key3046, -288), (key3060, 144), (key3064, 144), (key3095, 144), (key3101, 144), (key3123, -144), (key3125, -144)]

def entry21_4 : Integer.Sparse Key := [(key1048, 144), (key1051, 144), (key1059, -288), (key1134, -144), (key1139, 144), (key1204, -144), (key1206, 144)]

def entry21_5 : Integer.Sparse Key := [(key1056, -288), (key1064, 288), (key1065, 288), (key1079, -288)]

def entry21_6 : Integer.Sparse Key := [(key2680, 144), (key2683, 144), (key2690, -288), (key2711, -144), (key2716, 144), (key2741, -144), (key2743, 144)]

def entry21_7 : Integer.Sparse Key := [(key3080, -288), (key3085, 288), (key3087, 288), (key3100, -288)]

def entry21_8 : Integer.Sparse Key := [(key2414, 96), (key2417, 96), (key2424, -288), (key2487, -84), (key2492, 96), (key2546, -48), (key2548, 84), (key3033, 48), (key3035, 48), (key3120, -60), (key3128, -96), (key3131, 48), (key3138, 60)]

def entry21_10 : Integer.Sparse Key := [(key2679, 48), (key2682, 36), (key2689, -196), (key2710, -84), (key2715, 96), (key2740, -48), (key2742, 84), (key2813, 8), (key2818, -12), (key2955, -8), (key3047, 96), (key3050, 108), (key3054, -92), (key3061, -60), (key3066, -96), (key3069, 48), (key3072, 60), (key3096, -8), (key3106, 12), (key3110, 8)]

def entry21_12 : Integer.Sparse Key := [(key2421, -288), (key2428, 144), (key2429, 144), (key2496, 144), (key2508, -144), (key2550, 144), (key2556, -144)]

def entry21_13 : Integer.Sparse Key := [(key2690, -288), (key2716, 144), (key2743, 144), (key2819, 144), (key2901, -144), (key2956, 144), (key2980, -144)]

def entry21_14 : Integer.Sparse Key := [(key2711, 144), (key2716, -144), (key2741, 144), (key2743, -144), (key2814, -144), (key2819, 144), (key2954, -144), (key2956, 144)]

def entry21_15 : Integer.Sparse Key := [(key2679, 24), (key2682, 36), (key2689, -32), (key2710, 120), (key2715, -120), (key2740, 72), (key2742, -120), (key2813, -92), (key2818, 108), (key2953, -48), (key2955, 92), (key3047, -24), (key3050, -36), (key3054, 32), (key3061, 24), (key3066, 72), (key3069, -24), (key3072, -24), (key3096, -52), (key3103, -96), (key3106, 36), (key3110, 52)]

def entry21_16 : Integer.Sparse Key := [(key2686, -288), (key2693, 144), (key2694, 144), (key2719, 144), (key2731, -144), (key2744, 144), (key2750, -144)]

def entry21_21 : Integer.Sparse Key := [(key3081, 144), (key3082, 144), (key3086, -144), (key3088, -160), (key3090, -128), (key3091, -144), (key3109, 288)]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block3

def terms6 : Array TaggedTerm := #[
  ⟨1, ![3, -3, 0, 0, 0, 0], -24⟩,
  ⟨1, ![3, 0, -3, 0, 0, 0], 6⟩,
  ⟨1, ![3, 0, 0, -3, 0, 0], 6⟩,
  ⟨1, ![3, 0, 0, 0, -3, 0], 6⟩,
  ⟨1, ![3, 0, 0, 0, 0, -3], 6⟩
]

def terms7 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 0, 2], -2⟩,
  ⟨1, ![1, -2, -1, 0, 2, 0], -2⟩,
  ⟨1, ![1, -2, -1, 2, 0, 0], -2⟩,
  ⟨1, ![1, -2, 0, -1, 0, 2], -2⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], -2⟩,
  ⟨1, ![1, -2, 0, 0, -1, 2], -2⟩,
  ⟨1, ![1, -2, 0, 0, 2, -1], -2⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], -2⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], -2⟩,
  ⟨1, ![1, -2, 2, -1, 0, 0], -2⟩,
  ⟨1, ![1, -2, 2, 0, -1, 0], -2⟩,
  ⟨1, ![1, -2, 2, 0, 0, -1], -2⟩,
  ⟨1, ![1, -1, -2, 0, 0, 2], 2⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 2⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], 2⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], 2⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], 2⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], 2⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], 2⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], 2⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], 2⟩
]

def terms8 : Array TaggedTerm := #[
  ⟨0, ![1, -1, -2, 0, 0, 2], -2⟩,
  ⟨0, ![1, -1, -2, 0, 2, 0], -2⟩,
  ⟨0, ![1, -1, -2, 2, 0, 0], -2⟩,
  ⟨0, ![1, -1, 0, -2, 0, 2], -2⟩,
  ⟨0, ![1, -1, 0, -2, 2, 0], -2⟩,
  ⟨0, ![1, -1, 0, 0, -2, 2], -2⟩,
  ⟨0, ![1, -1, 0, 0, 2, -2], -2⟩,
  ⟨0, ![1, -1, 0, 2, -2, 0], -2⟩,
  ⟨0, ![1, -1, 0, 2, 0, -2], -2⟩,
  ⟨0, ![1, -1, 2, -2, 0, 0], -2⟩,
  ⟨0, ![1, -1, 2, 0, -2, 0], -2⟩,
  ⟨0, ![1, -1, 2, 0, 0, -2], -2⟩,
  ⟨0, ![1, 0, -2, -1, 0, 2], 1⟩,
  ⟨0, ![1, 0, -2, -1, 2, 0], 1⟩,
  ⟨0, ![1, 0, -2, 0, -1, 2], 1⟩,
  ⟨0, ![1, 0, -2, 0, 2, -1], 1⟩,
  ⟨0, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨0, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨0, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨0, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨0, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨0, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨0, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨0, ![1, 0, -1, 2, 0, -2], 1⟩,
  ⟨0, ![1, 0, 0, -2, -1, 2], 1⟩,
  ⟨0, ![1, 0, 0, -2, 2, -1], 1⟩,
  ⟨0, ![1, 0, 0, -1, -2, 2], 1⟩,
  ⟨0, ![1, 0, 0, -1, 2, -2], 1⟩,
  ⟨0, ![1, 0, 0, 2, -2, -1], 1⟩,
  ⟨0, ![1, 0, 0, 2, -1, -2], 1⟩,
  ⟨0, ![1, 0, 2, -2, -1, 0], 1⟩,
  ⟨0, ![1, 0, 2, -2, 0, -1], 1⟩,
  ⟨0, ![1, 0, 2, -1, -2, 0], 1⟩,
  ⟨0, ![1, 0, 2, -1, 0, -2], 1⟩,
  ⟨0, ![1, 0, 2, 0, -2, -1], 1⟩,
  ⟨0, ![1, 0, 2, 0, -1, -2], 1⟩
]

def terms9 : Array TaggedTerm := #[
  ⟨1, ![1, 0, -2, -1, 0, 2], 1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], 1⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], 1⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], 1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], 1⟩,
  ⟨1, ![1, 0, 0, -2, -1, 2], 1⟩,
  ⟨1, ![1, 0, 0, -2, 2, -1], 1⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 1⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 1⟩,
  ⟨1, ![1, 0, 0, 2, -2, -1], 1⟩,
  ⟨1, ![1, 0, 0, 2, -1, -2], 1⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], 1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], 1⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], 1⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], 1⟩,
  ⟨1, ![1, 0, 2, 0, -2, -1], 1⟩,
  ⟨1, ![1, 0, 2, 0, -1, -2], 1⟩,
  ⟨1, ![1, 2, -2, -1, 0, 0], -2⟩,
  ⟨1, ![1, 2, -2, 0, -1, 0], -2⟩,
  ⟨1, ![1, 2, -2, 0, 0, -1], -2⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], -2⟩,
  ⟨1, ![1, 2, 0, -2, -1, 0], -2⟩,
  ⟨1, ![1, 2, 0, -2, 0, -1], -2⟩,
  ⟨1, ![1, 2, 0, -1, -2, 0], -2⟩,
  ⟨1, ![1, 2, 0, -1, 0, -2], -2⟩,
  ⟨1, ![1, 2, 0, 0, -2, -1], -2⟩,
  ⟨1, ![1, 2, 0, 0, -1, -2], -2⟩
]

end MUB6.Certificate.GramFunctions.Block3

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

def terms0 : Array TaggedTerm := #[
  ⟨1, ![1, 0, 0, -3, 1, 1], 4⟩,
  ⟨1, ![1, 0, 0, 1, -3, 1], 4⟩,
  ⟨1, ![1, 0, 0, 1, 1, -3], 4⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], -2⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], -2⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], -2⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], -2⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], -2⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], -2⟩,
  ⟨1, ![1, 1, 0, -3, 0, 1], -2⟩,
  ⟨1, ![1, 1, 0, -3, 1, 0], -2⟩,
  ⟨1, ![1, 1, 0, 0, -3, 1], -2⟩,
  ⟨1, ![1, 1, 0, 0, 1, -3], -2⟩,
  ⟨1, ![1, 1, 0, 1, -3, 0], -2⟩,
  ⟨1, ![1, 1, 0, 1, 0, -3], -2⟩,
  ⟨1, ![1, 1, 1, -3, 0, 0], 4⟩,
  ⟨1, ![1, 1, 1, 0, -3, 0], 4⟩,
  ⟨1, ![1, 1, 1, 0, 0, -3], 4⟩
]

def terms10 : Array TaggedTerm := #[
  ⟨1, ![2, -1, 0, -2, 0, 1], -1⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], -1⟩,
  ⟨1, ![2, -1, 0, 0, -2, 1], -1⟩,
  ⟨1, ![2, -1, 0, 0, 1, -2], -1⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], -1⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], -1⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], 2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], 2⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], 2⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], -1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], -1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], -1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], -1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], -1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], -1⟩,
  ⟨1, ![2, 0, 0, -2, -1, 1], 2⟩,
  ⟨1, ![2, 0, 0, -2, 1, -1], 2⟩,
  ⟨1, ![2, 0, 0, -1, -2, 1], 2⟩,
  ⟨1, ![2, 0, 0, -1, 1, -2], 2⟩,
  ⟨1, ![2, 0, 0, 1, -2, -1], 2⟩,
  ⟨1, ![2, 0, 0, 1, -1, -2], 2⟩,
  ⟨1, ![2, 0, 1, -2, -1, 0], -1⟩,
  ⟨1, ![2, 0, 1, -2, 0, -1], -1⟩,
  ⟨1, ![2, 0, 1, -1, -2, 0], -1⟩,
  ⟨1, ![2, 0, 1, -1, 0, -2], -1⟩,
  ⟨1, ![2, 0, 1, 0, -2, -1], -1⟩,
  ⟨1, ![2, 0, 1, 0, -1, -2], -1⟩,
  ⟨1, ![2, 1, -1, -2, 0, 0], 2⟩,
  ⟨1, ![2, 1, -1, 0, -2, 0], 2⟩,
  ⟨1, ![2, 1, -1, 0, 0, -2], 2⟩,
  ⟨1, ![2, 1, 0, -2, -1, 0], -1⟩,
  ⟨1, ![2, 1, 0, -2, 0, -1], -1⟩,
  ⟨1, ![2, 1, 0, -1, -2, 0], -1⟩,
  ⟨1, ![2, 1, 0, -1, 0, -2], -1⟩,
  ⟨1, ![2, 1, 0, 0, -2, -1], -1⟩,
  ⟨1, ![2, 1, 0, 0, -1, -2], -1⟩
]

def terms11 : Array TaggedTerm := #[
  ⟨0, ![0, -2, 0, 0, 0, 2], -2⟩,
  ⟨0, ![0, -2, 0, 0, 2, 0], -2⟩,
  ⟨0, ![0, -2, 0, 2, 0, 0], -2⟩,
  ⟨0, ![0, -2, 2, 0, 0, 0], 6⟩,
  ⟨0, ![0, 0, -2, 0, 0, 2], -2⟩,
  ⟨0, ![0, 0, -2, 0, 2, 0], -2⟩,
  ⟨0, ![0, 0, -2, 2, 0, 0], -2⟩,
  ⟨0, ![0, 0, 0, -2, 0, 2], 2⟩,
  ⟨0, ![0, 0, 0, -2, 2, 0], 2⟩,
  ⟨0, ![0, 0, 0, 0, -2, 2], 2⟩,
  ⟨0, ![0, 0, 0, 0, 2, -2], 2⟩,
  ⟨0, ![0, 0, 0, 2, -2, 0], 2⟩,
  ⟨0, ![0, 0, 0, 2, 0, -2], 2⟩,
  ⟨0, ![0, 0, 2, -2, 0, 0], -2⟩,
  ⟨0, ![0, 0, 2, 0, -2, 0], -2⟩,
  ⟨0, ![0, 0, 2, 0, 0, -2], -2⟩,
  ⟨0, ![0, 2, -2, 0, 0, 0], 6⟩,
  ⟨0, ![0, 2, 0, -2, 0, 0], -2⟩,
  ⟨0, ![0, 2, 0, 0, -2, 0], -2⟩,
  ⟨0, ![0, 2, 0, 0, 0, -2], -2⟩
]

def terms12 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 1, 1], 2⟩,
  ⟨1, ![1, -3, 0, 1, 0, 1], 2⟩,
  ⟨1, ![1, -3, 0, 1, 1, 0], 2⟩,
  ⟨1, ![1, -3, 1, 0, 0, 1], -2⟩,
  ⟨1, ![1, -3, 1, 0, 1, 0], -2⟩,
  ⟨1, ![1, -3, 1, 1, 0, 0], -2⟩,
  ⟨1, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 0, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 1, 0], 2⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], -1⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], -1⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], -1⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], -1⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], -1⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], -1⟩,
  ⟨1, ![1, 1, -3, 0, 0, 1], -2⟩,
  ⟨1, ![1, 1, -3, 0, 1, 0], -2⟩,
  ⟨1, ![1, 1, -3, 1, 0, 0], -2⟩,
  ⟨1, ![1, 1, 0, -3, 0, 1], -1⟩,
  ⟨1, ![1, 1, 0, -3, 1, 0], -1⟩,
  ⟨1, ![1, 1, 0, 0, -3, 1], -1⟩,
  ⟨1, ![1, 1, 0, 0, 1, -3], -1⟩,
  ⟨1, ![1, 1, 0, 1, -3, 0], -1⟩,
  ⟨1, ![1, 1, 0, 1, 0, -3], -1⟩,
  ⟨1, ![1, 1, 1, -3, 0, 0], 4⟩,
  ⟨1, ![1, 1, 1, 0, -3, 0], 4⟩,
  ⟨1, ![1, 1, 1, 0, 0, -3], 4⟩
]

end MUB6.Certificate.GramFunctions.Block4

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

def row13187 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

def row13188 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

def row13189 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

def row13190 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13191 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13192 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13193 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13194 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13195 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13196 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13197 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13198 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13199 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13200 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13201 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row13202 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

def row13203 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

def row13204 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14241 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14242 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14243 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14244 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14245 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14246 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14247 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14248 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14249 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14250 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14251 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14252 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14253 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14254 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14255 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1112, -4), (key1121, 4), (key1197, -2), (key1210, 2)]

def row14256 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14257 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14258 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14259 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14260 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14261 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -4), (key1112, 12), (key1121, -4), (key1148, -4), (key1191, -4), (key1197, 2), (key1210, 2)]

def row14262 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14263 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14264 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14265 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14266 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14267 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14268 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14269 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14270 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, -4), (key1148, 4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row14271 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14272 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14273 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14274 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14275 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14276 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, -2), (key1069, 2), (key1107, 4), (key1112, -4), (key1191, 4), (key1197, -2), (key1210, -2)]

def row14277 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14278 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14279 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14280 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14281 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14282 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14283 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14284 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14285 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14286 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14287 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14288 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14289 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14290 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14291 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2469, -4), (key2477, 4), (key2541, -2), (key2552, 2)]

def row14292 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14293 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14294 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14295 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14296 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14297 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -4), (key2469, 12), (key2477, -4), (key2500, -4), (key2536, -4), (key2541, 2), (key2552, 2)]

def row14298 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14299 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14300 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14301 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14302 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14303 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14304 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14305 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14306 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, -4), (key2500, 4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row14307 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14308 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14309 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14310 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14311 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14312 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, -2), (key2434, 2), (key2465, 4), (key2469, -4), (key2536, 4), (key2541, -2), (key2552, -2)]

def row14313 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14314 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14315 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14316 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14317 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14318 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14319 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14320 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14321 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14322 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14323 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14324 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14325 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14326 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14327 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, -2), (key2720, 2), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, -4)]

def row14328 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14329 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14330 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14331 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14332 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14333 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, -4), (key2823, 2), (key2850, 12), (key2854, -4), (key2864, -4)]

def row14334 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14335 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14336 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14337 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14338 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14339 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14340 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14341 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14342 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, -4), (key2788, 6), (key2800, -4), (key2823, 6), (key2850, 4), (key2854, -4), (key2864, -4)]

def row14343 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14344 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14345 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14346 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14347 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14348 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, 2), (key2720, -2), (key2788, -2), (key2823, -2), (key2850, -4), (key2854, 4), (key2864, 4)]

def row14385 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14386 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14387 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14388 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14389 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14390 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14391 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14392 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14393 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14394 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14395 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14396 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14397 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14398 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14399 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1116, -2), (key1125, -2), (key1128, 4), (key1152, 4), (key1156, -2), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row14400 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14401 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14402 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14403 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14404 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14405 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1194, 4), (key1200, -4), (key1213, -4), (key1223, 4)]

def row14406 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14407 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14408 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14409 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14410 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14411 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14412 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14413 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14414 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1116, -4), (key1125, 8), (key1128, -4), (key1152, -4), (key1156, 8), (key1172, -4)]

def row14415 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14416 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14417 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14418 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14419 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14420 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, 4), (key1125, -2), (key1128, -2), (key1152, -2), (key1156, -2), (key1172, 4)]

def row14457 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14458 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14459 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14460 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14461 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14462 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14463 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14464 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14465 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14466 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14467 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14468 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14469 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14470 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14471 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

def row14472 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14473 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14474 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14475 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14476 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14477 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

def row14478 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14479 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14480 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14481 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14482 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14483 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14484 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14485 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14486 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

def row14487 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14488 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14489 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14490 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14491 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14492 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

def row14493 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14494 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14495 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14496 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14497 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14498 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

def row14499 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

def row14500 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

def row14501 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

def row14502 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14503 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14504 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14505 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14506 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14507 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

def row14508 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2928, 2), (key2987, 2)]

def row14509 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2928, 2), (key2987, 2)]

def row14510 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, -4), (key2597, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2987, 2)]

def row14511 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, -4), (key2597, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2987, 2)]

def row14512 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4)]

def row14513 : Integer.Sparse Key := [(key2386, 2), (key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2583, 2), (key2586, -4), (key2765, -4), (key2842, 6), (key2874, -4)]

def row14514 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14515 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14516 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14517 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

def row14518 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 4), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2842, -2), (key2874, 6)]

def row14519 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 4), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2842, -2), (key2874, 6)]

def row14520 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

def row14521 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

def row14522 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

def row14523 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2), (key2839, -2)]

def row14524 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2), (key2839, -2)]

def row14525 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2), (key2839, -2)]

def row14526 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2), (key2839, -2)]

def row14527 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 4), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2)]

def row14528 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 4), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14601 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14602 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14603 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14604 : Integer.Sparse Key := [(key1700, -12), (key1706, 12), (key1851, 12), (key1855, -12)]

def row14605 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14606 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14607 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14608 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14609 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14610 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14611 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14612 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14613 : Integer.Sparse Key := [(key1700, -4), (key1706, 4), (key1851, 4), (key1855, -4)]

def row14614 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14615 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14616 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14617 : Integer.Sparse Key := [(key1700, -12), (key1706, 12), (key1851, 12), (key1855, -12)]

def row14618 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14619 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14620 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row14641 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14642 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14643 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14644 : Integer.Sparse Key := [(key1273, 6), (key1278, -6), (key1696, -6), (key1701, 12), (key1751, -6), (key1933, -6), (key1953, 6)]

def row14645 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14646 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14647 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14648 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14649 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14650 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14651 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14652 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14653 : Integer.Sparse Key := [(key1273, 2), (key1278, -2), (key1696, -2), (key1701, 4), (key1751, -2), (key1933, -2), (key1953, 2)]

def row14654 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14655 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14656 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14657 : Integer.Sparse Key := [(key1273, 6), (key1278, -6), (key1696, -6), (key1701, 12), (key1751, -6), (key1933, -6), (key1953, 6)]

def row14658 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14659 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14660 : Integer.Sparse Key := [(key1273, -2), (key1278, 2), (key1696, 2), (key1701, -4), (key1751, 2), (key1933, 2), (key1953, -2)]

def row14681 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14682 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14683 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14684 : Integer.Sparse Key := [(key221, 6), (key225, -6), (key493, -6), (key497, 12), (key551, -6), (key619, -6), (key645, 6)]

def row14685 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14686 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14687 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14688 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14689 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14690 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14691 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14692 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14693 : Integer.Sparse Key := [(key221, 2), (key225, -2), (key493, -2), (key497, 4), (key551, -2), (key619, -2), (key645, 2)]

def row14694 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14695 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14696 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14697 : Integer.Sparse Key := [(key221, 6), (key225, -6), (key493, -6), (key497, 12), (key551, -6), (key619, -6), (key645, 6)]

def row14698 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14699 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14700 : Integer.Sparse Key := [(key221, -2), (key225, 2), (key493, 2), (key497, -4), (key551, 2), (key619, 2), (key645, -2)]

def row14701 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14702 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14703 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14704 : Integer.Sparse Key := [(key496, -12), (key502, 12), (key618, 12), (key622, -12)]

def row14705 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14706 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14707 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14708 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14709 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14710 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14711 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14712 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14713 : Integer.Sparse Key := [(key496, -4), (key502, 4), (key618, 4), (key622, -4)]

def row14714 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14715 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14716 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14717 : Integer.Sparse Key := [(key496, -12), (key502, 12), (key618, 12), (key622, -12)]

def row14718 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14719 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14720 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

def row14721 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14722 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14723 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14724 : Integer.Sparse Key := [(key1484, 6), (key1490, -6), (key1710, -6), (key1716, 12), (key1723, -6), (key1937, -6), (key1940, 6)]

def row14725 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14726 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14727 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14728 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14729 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14730 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14731 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14732 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14733 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

def row14734 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14735 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14736 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14737 : Integer.Sparse Key := [(key1484, 6), (key1490, -6), (key1710, -6), (key1716, 12), (key1723, -6), (key1937, -6), (key1940, 6)]

def row14738 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14739 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14740 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

def row14761 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14762 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14763 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14764 : Integer.Sparse Key := [(key1274, 6), (key1278, -6), (key1697, -6), (key1701, 12), (key1751, -6), (key1852, -6), (key1884, 6)]

def row14765 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14766 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14767 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14768 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14769 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14770 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14771 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14772 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14773 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

def row14774 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14775 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14776 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14777 : Integer.Sparse Key := [(key1274, 6), (key1278, -6), (key1697, -6), (key1701, 12), (key1751, -6), (key1852, -6), (key1884, 6)]

def row14778 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14779 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14780 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

def row14801 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14802 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14803 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14804 : Integer.Sparse Key := [(key1485, 6), (key1490, -6), (key1711, -6), (key1716, 12), (key1723, -6), (key1861, -6), (key1867, 6)]

def row14805 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14806 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14807 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14808 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14809 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14810 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14811 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14812 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14813 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

def row14814 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14815 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14816 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14817 : Integer.Sparse Key := [(key1485, 6), (key1490, -6), (key1711, -6), (key1716, 12), (key1723, -6), (key1861, -6), (key1867, 6)]

def row14818 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14819 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14820 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

def row14821 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14822 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14823 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14824 : Integer.Sparse Key := [(key288, 6), (key289, -6), (key513, -6), (key515, 12), (key547, -6), (key670, -6), (key680, 6)]

def row14825 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14826 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14827 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14828 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14829 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14830 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -4), (key680, 2)]

def row14831 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -4), (key680, 2)]

def row14832 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14833 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

def row14834 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14835 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14836 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

def row14837 : Integer.Sparse Key := [(key288, 6), (key289, -6), (key513, -6), (key515, 12), (key547, -6), (key670, -6), (key680, 6)]

def row14838 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14839 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

def row14840 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14853 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14854 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14855 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14856 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14857 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14858 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14859 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14860 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14861 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1098, -4), (key1169, 4), (key1180, 4), (key1220, -4)]

def row14862 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14863 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14864 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14865 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14866 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14867 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14868 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14869 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14870 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1098, 4), (key1169, -4), (key1180, -4), (key1220, 4)]

def row14871 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14872 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14873 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14874 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14875 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14876 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row14877 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

def row14878 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

def row14879 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, -8), (key1098, 4), (key1169, 4), (key1180, 12), (key1183, -8), (key1220, -4)]

def row14880 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

def row14881 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

def row14882 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2461, -4), (key2517, 4), (key2567, 4), (key2579, -4)]

def row14883 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

def row14884 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

def row14885 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2461, 4), (key2517, -4), (key2567, -4), (key2579, 4)]

def row14886 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

def row14887 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

def row14888 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2452, -4), (key2456, 4), (key2458, -2), (key2461, -2), (key2517, 4), (key2519, 6), (key2567, -2), (key2579, -4)]

def row14889 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14890 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14891 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14892 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14893 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14894 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2363, 2), (key2366, -2), (key2452, 6), (key2456, -2), (key2458, -2), (key2461, -2), (key2517, -2), (key2523, 4), (key2528, -2)]

def row14895 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

def row14896 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

def row14897 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2452, 4), (key2456, -4), (key2458, 4), (key2517, -2), (key2519, -4), (key2528, -2), (key2560, 4)]

def row14898 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14899 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14900 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14901 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14902 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14903 : Integer.Sparse Key := [(key2357, 2), (key2361, -2), (key2456, 4), (key2458, -4), (key2517, -2), (key2528, -2), (key2530, 4)]

def row14904 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

def row14905 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

def row14906 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, 4), (key2452, -4), (key2456, -4), (key2458, 4), (key2517, 6), (key2519, 4), (key2528, 6), (key2530, -8), (key2560, -4)]

def row14907 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14908 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14909 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14910 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14911 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14912 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14913 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14914 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14915 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, -4), (key2518, 4)]

def row14916 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14917 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14918 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14919 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14920 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14921 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14922 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14923 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14924 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, -4), (key2436, 4), (key2471, 4), (key2518, -4)]

def row14925 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14926 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14927 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14928 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14929 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14930 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

def row14931 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

def row14932 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

def row14933 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, 4), (key2436, -4), (key2471, 4), (key2479, -8), (key2502, -8), (key2518, 12)]

def row14934 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14935 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14936 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14937 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14938 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14939 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14940 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14941 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14942 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1097, -4), (key1168, 4), (key1180, 4), (key1219, -4)]

def row14943 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14944 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14945 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14946 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14947 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14948 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14949 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14950 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14951 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1097, 4), (key1168, -4), (key1180, -4), (key1219, 4)]

def row14952 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14953 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14954 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14955 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14956 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14957 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

def row14958 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

def row14959 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

def row14960 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, -8), (key1097, 4), (key1168, 4), (key1180, 12), (key1182, -8), (key1219, -4)]

def row14961 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14962 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15123 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15124 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15125 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15126 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15127 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15128 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15129 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15130 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15131 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

def row15132 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15133 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15134 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15135 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15136 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15137 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15138 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15139 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15140 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

def row15141 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15142 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15143 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15144 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15145 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15146 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

def row15147 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

def row15148 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

def row15149 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

def row15159 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15160 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15161 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2525, -1), (key2532, 2), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15162 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2525, -1), (key2532, 2), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15163 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15164 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row15168 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15169 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15170 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 2), (key2525, 1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15171 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 2), (key2525, 1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15172 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15173 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

def row15174 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

def row15175 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

def row15176 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

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

def row16836 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7706 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7707 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7708 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7709 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7710 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7711 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7712 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7713 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7714 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7715 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7716 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7717 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7718 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7719 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7720 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7721 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7722 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7723 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7724 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7725 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7726 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7727 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7728 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7729 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7730 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7731 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7732 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7733 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7734 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7735 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7736 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7737 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7738 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7739 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7740 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7741 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7742 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3005, 2), (key3028, 2)]

def row7743 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3005, 2), (key3028, 2)]

def row7744 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3028, 2)]

def row7745 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3028, 2)]

def row7746 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2)]

def row7747 : Integer.Sparse Key := [(key2388, 2), (key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2583, 2), (key2589, 2), (key2768, 2), (key2876, 2)]

def row7748 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2), (key2839, 2)]

def row7749 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2), (key2839, 2)]

def row7750 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2), (key2839, 2)]

def row7751 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2), (key2839, 2)]

def row7752 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2)]

def row7753 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2)]

def row7791 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7792 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7793 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7794 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7795 : Integer.Sparse Key := [(key968, -24), (key1082, 24)]

def row7796 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7797 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7798 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7799 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7800 : Integer.Sparse Key := [(key973, -24), (key1087, 24)]

def row7801 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7802 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7803 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7804 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7805 : Integer.Sparse Key := [(key2396, -24), (key2462, 24)]

def row7806 : Integer.Sparse Key := [(key2368, 6), (key2396, 6), (key2462, 12), (key2581, -6), (key2837, -18)]

def row7807 : Integer.Sparse Key := [(key2368, 4), (key2396, 4), (key2462, 4), (key2581, -4), (key2760, 2), (key2837, -10)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7808 : Integer.Sparse Key := [(key2368, 2), (key2396, 2), (key2581, -2), (key2760, 4), (key2837, -6)]

def row7809 : Integer.Sparse Key := [(key2760, 6), (key2837, -6)]

def row7810 : Integer.Sparse Key := [(key2355, -24), (key2450, 24)]

def row7811 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7812 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7813 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7814 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7815 : Integer.Sparse Key := [(key2764, -24), (key2841, 24)]

def row7816 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7817 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7818 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7819 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7820 : Integer.Sparse Key := [(key2351, -24), (key2446, 24)]

def row7821 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7822 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7823 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7824 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7837 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7838 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7839 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7840 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7841 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7842 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7843 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7844 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7845 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7846 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7847 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7848 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7849 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7850 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7851 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7852 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7853 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7854 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7855 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7856 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7857 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7858 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7859 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7860 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7861 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7862 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7863 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7864 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7865 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7866 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7867 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7868 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7869 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7870 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7871 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7872 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7873 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7874 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7875 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7876 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7877 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7878 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7879 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7880 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7881 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7882 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7883 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7884 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7897 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7898 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7899 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7900 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7901 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7902 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7903 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7904 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7905 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7906 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7907 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7908 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7909 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7910 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7911 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7912 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7913 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7914 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7915 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7916 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7917 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7918 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7919 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7920 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7981 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7982 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7983 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7984 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7985 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7986 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7987 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7988 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7989 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7990 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7991 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7992 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7993 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7994 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7995 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7996 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7997 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7998 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7999 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8000 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8001 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8002 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8003 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8004 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8005 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8006 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8007 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8008 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8009 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8010 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8011 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8012 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8013 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8014 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8015 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8016 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8017 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8018 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8019 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8020 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8021 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8022 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8023 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8024 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8025 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8026 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8027 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8028 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8029 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8030 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8031 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8032 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8033 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8034 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8035 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8036 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8037 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8038 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8039 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8040 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8041 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key212, 2), (key375, 2), (key381, 2), (key460, 2), (key490, 2), (key654, 2), (key663, 2)]

def row8042 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key212, 2), (key375, 2), (key381, 2), (key460, 2), (key490, 2), (key654, 2), (key663, 2)]

def row8043 : Integer.Sparse Key := [(key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key206, 2), (key212, 2), (key218, 2), (key381, 2), (key460, 2), (key490, 2), (key663, 2)]

def row8044 : Integer.Sparse Key := [(key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key206, 2), (key212, 2), (key218, 2), (key381, 2), (key460, 2), (key490, 2), (key663, 2)]

def row8045 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key196, 2), (key200, 2), (key212, 2), (key375, 2), (key381, 2), (key460, 2)]

def row8046 : Integer.Sparse Key := [(key35, 2), (key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key196, 2), (key200, 2), (key206, 2), (key212, 2), (key381, 2), (key460, 2)]

def row8047 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2), (key426, 2)]

def row8048 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2), (key426, 2)]

def row8049 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2), (key426, 2)]

def row8050 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2), (key426, 2)]

def row8051 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2)]

def row8052 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2)]

def row8053 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8054 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8055 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8056 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8057 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8058 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8059 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8060 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8061 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8062 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8063 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8064 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

def row8065 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8066 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8067 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8068 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8069 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8070 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8071 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8072 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8073 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8074 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8075 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8076 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8077 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8078 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8079 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8080 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8081 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8082 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8083 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8084 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8085 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8086 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8087 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8088 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

def row8089 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8090 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8091 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8092 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8093 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8094 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8095 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8096 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8097 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8098 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8099 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8100 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

def row8101 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8102 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8103 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8104 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8105 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8106 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8107 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8108 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8109 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8110 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8111 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8112 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8113 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8114 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8115 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8116 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8117 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8118 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8119 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8120 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8121 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8122 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8123 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8124 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

def row8125 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8126 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8127 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8128 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8129 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8130 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8131 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8132 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8133 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8134 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8135 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8136 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

def row8137 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8138 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8139 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8140 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8141 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8142 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8143 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8144 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8145 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8146 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8147 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8148 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8149 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8150 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8151 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8152 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8153 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8154 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8155 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8156 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8157 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8158 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8159 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8160 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

def row8161 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8162 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8163 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8164 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8165 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8166 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8167 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8168 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8169 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8170 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8171 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8172 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

def row8173 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8174 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8175 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8176 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8177 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8178 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8179 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8180 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8181 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8182 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8183 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8184 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8185 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8186 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8187 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8188 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8189 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8190 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8191 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8192 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8193 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8194 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8195 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8196 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

def row8209 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8210 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8211 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8212 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8213 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8214 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8215 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8216 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8217 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8218 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8219 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8220 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8221 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8222 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8223 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8224 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8225 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8226 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8227 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8228 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8229 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8230 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8231 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8232 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

def row8233 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8234 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8235 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8236 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8237 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8238 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -8), (key435, 2), (key445, 2), (key453, 2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8239 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -8), (key435, 2), (key445, 2), (key453, 2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8240 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8241 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8242 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8243 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8244 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row8245 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8246 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8247 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8248 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8249 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8250 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8251 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8252 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8253 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8254 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8255 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8256 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8257 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8258 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8259 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 2), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8260 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 2), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8261 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8262 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8263 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8264 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8265 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8266 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8267 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8268 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

def row8281 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8282 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8283 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8284 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8285 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8286 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8287 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8288 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8289 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8290 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8291 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8292 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

def row8293 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8294 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8295 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8296 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8297 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8298 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8299 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8300 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8301 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8302 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8303 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8304 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

def row8305 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8306 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8307 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8308 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8309 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8310 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8311 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8312 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8313 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8314 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8315 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8316 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

def row8317 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8318 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8319 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8320 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8321 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8322 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8323 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8324 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8325 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8326 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8327 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8328 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8341 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8342 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8343 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8344 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8345 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8346 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8347 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8348 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8349 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8350 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8351 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8352 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8353 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8354 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8355 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8356 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8357 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8358 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8359 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8360 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8361 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8362 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8363 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8364 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, -18), (key2873, 6)]

def row8365 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8366 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8367 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8368 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8369 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8370 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8371 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8372 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8373 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8374 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8375 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8376 : Integer.Sparse Key := [(key2585, 6), (key2764, 6), (key2841, 12), (key2873, -24)]

def row8413 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8414 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8415 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8416 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8417 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8418 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8419 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8420 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8421 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8422 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8423 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8424 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8425 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8426 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8427 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8428 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8429 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8430 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8431 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8432 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8433 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8434 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8435 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8436 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, -1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1625, -2), (key1634, -2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row8437 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8438 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8439 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8440 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8441 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8442 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8443 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8444 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8445 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8446 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

def row8447 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8448 : Integer.Sparse Key := [(key1299, 2), (key1319, 2), (key1327, 2), (key1352, -4), (key1355, -2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1682, -4), (key1684, -4), (key1690, -4)]

end MUB6.Certificate.GramRows

end OAI
end


