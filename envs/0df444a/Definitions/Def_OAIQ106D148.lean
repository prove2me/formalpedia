-- Prove2me | Definitions.Def_OAIQ106D148
-- name    : OAIQ106D148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:53:31.820553+00:00
-- url     : https://prove2.me/theorems/25aa5275-3cd3-4c89-bc2f-5b6ba51799b4
-- title:
--   Definitions bundle OAIQ106D148 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1546 declarations of OpenAI's Lean: 1546 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry12_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry14_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry14_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry14_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry15_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry15_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry16_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry16_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry16_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry17_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry21_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entry21_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entry22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry22_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entry22_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entry23_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry23_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entry23_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entry23_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entry23_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry25_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry25_14`, `OAI.MUB6.Certificate.GramEntries.Block3.entry25_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entry25_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry25_25`, `OAI.MUB6.Certificate.GramEntries.Block3.entry4_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry5_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry7_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry7_3` and 1506 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block3Data`, `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramFunctions_Block3`, `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block101`, `MutuallyUnbiased_GramRows_Block102`, `MutuallyUnbiased_GramRows_Block103`, `MutuallyUnbiased_GramRows_Block104`, `MutuallyUnbiased_GramRows_Block105`, `MutuallyUnbiased_GramRows_Block106`, `MutuallyUnbiased_GramRows_Block107`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block111`, `MutuallyUnbiased_GramRows_Block112`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block78`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_GramRows_Block82`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block91`, `MutuallyUnbiased_GramRows_Block92`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_GramRows_Block94`, `MutuallyUnbiased_GramRows_Block95`, `MutuallyUnbiased_GramRows_Block96`, `MutuallyUnbiased_GramRows_Block97`, `MutuallyUnbiased_GramRows_Block98`, `MutuallyUnbiased_GramRows_Block99`.
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090` and `OAIQ106D091` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D198` and `OAIQ106D199`.
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
import Definitions.Def_OAIQ106D088
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization

def entry4_0 : Integer.Sparse Key := [(key2361, 48), (key2363, -64), (key2366, 16), (key2452, -336), (key2456, 48), (key2458, -240), (key2517, 64), (key2519, -204), (key2523, 48), (key2528, 176), (key2530, 240), (key2560, 160), (key2567, 12), (key2579, 32)]

def entry5_4 : Integer.Sparse Key := [(key2370, 24), (key2376, 24), (key2388, 32), (key2398, 168), (key2404, 312), (key2435, 176), (key2464, -128), (key2470, -144), (key2478, -120), (key2501, -120), (key2568, 12), (key2570, 16), (key2575, 16), (key2583, -24), (key2589, -72), (key2604, 16), (key2762, 24), (key2768, 24), (key2839, -64), (key2845, -96), (key2876, -60), (key2916, 24), (key2925, 32), (key3005, 16), (key3019, -72), (key3028, -16)]

def entry7_2 : Integer.Sparse Key := [(key993, 192), (key1001, 384), (key1015, 144), (key1028, -192), (key1036, -384), (key1071, -144), (key1123, -96), (key1150, 96), (key1235, -48), (key1242, 48)]

def entry7_3 : Integer.Sparse Key := [(key2610, -144), (key2626, 96), (key2635, 48), (key2665, 144), (key2700, 384), (key2721, 192), (key2780, -96), (key2789, -48), (key2803, -384), (key2824, -192)]

def entry8_2 : Integer.Sparse Key := [(key18, 24), (key23, 24), (key35, 32), (key43, 168), (key48, 312), (key74, 176), (key100, -128), (key105, -144), (key115, -120), (key137, -120), (key195, 12), (key196, 16), (key200, 16), (key206, -24), (key212, -72), (key218, 16), (key375, 24), (key381, 24), (key426, -64), (key432, -96), (key460, -60), (key486, 24), (key490, 32), (key654, 16), (key659, -72), (key663, -16)]

def entry8_3 : Integer.Sparse Key := [(key1293, 192), (key1313, -192), (key1388, 48), (key1421, -48), (key1543, -96), (key1553, 48), (key1570, 336), (key1590, 192), (key1619, -240), (key1621, -48), (key1630, -192)]

def entry8_5 : Integer.Sparse Key := [(key1291, 72), (key1299, 120), (key1311, -72), (key1319, -96), (key1327, -24), (key1352, -24), (key1355, 24), (key1386, 24), (key1394, 24), (key1419, -24), (key1427, -48), (key1445, -24), (key1473, 24), (key1481, 24), (key1541, -24), (key1549, -48), (key1557, 24), (key1568, 120), (key1576, 96), (key1594, 120), (key1617, -96), (key1625, -48), (key1634, -96), (key1682, -48), (key1684, 24), (key1690, -24), (key1897, -24), (key1900, 24), (key1904, 120), (key1912, 72), (key1919, -96), (key1921, -24), (key1927, -72)]

def entry8_7 : Integer.Sparse Key := [(key1291, -48), (key1299, -96), (key1311, 48), (key1319, 48), (key1352, 48), (key1386, 48), (key1394, 96), (key1419, -48), (key1427, -48), (key1473, -48), (key1541, 144), (key1549, 144), (key1557, 96), (key1568, -144), (key1576, -144), (key1594, -96), (key1625, -48), (key1634, 48), (key1684, -48), (key1690, 48), (key1897, 144), (key1900, 48), (key1904, -144), (key1912, -48), (key1921, -48), (key1927, 48)]

def entry8_8 : Integer.Sparse Key := [(key236, 72), (key241, 120), (key248, -72), (key253, -96), (key263, -64), (key277, 16), (key278, 24), (key302, 24), (key307, 24), (key316, -64), (key321, -96), (key331, -60), (key346, 24), (key347, 32), (key385, 16), (key400, 24), (key406, 120), (key411, 96), (key421, 160), (key435, -96), (key445, -96), (key453, -96), (key488, 24), (key489, 24), (key655, 12), (key656, 16), (key657, 80), (key658, 72), (key660, -96), (key661, -72), (key662, -72)]

def entry9_2 : Integer.Sparse Key := [(key993, 48), (key1001, -48), (key1028, 48), (key1036, -48), (key1106, -96), (key1114, -240), (key1123, -192), (key1150, -192), (key1232, 336), (key1235, 192), (key1242, 192)]

def entry9_3 : Integer.Sparse Key := [(key2626, -192), (key2635, 192), (key2700, -48), (key2721, 48), (key2780, -192), (key2789, 192), (key2803, -48), (key2824, 48), (key2853, -240), (key2855, 336), (key2865, -96)]

def entry9_4 : Integer.Sparse Key := [(key2370, 24), (key2376, -72), (key2388, -16), (key2398, 24), (key2404, -72), (key2435, -16), (key2464, -128), (key2470, -240), (key2478, -216), (key2501, -216), (key2568, 300), (key2570, 160), (key2575, 160), (key2583, 24), (key2589, 24), (key2604, 16), (key2762, 24), (key2768, 24), (key2839, 32), (key2876, 36), (key2916, 24), (key2925, 32), (key3005, 16), (key3019, 24), (key3028, 32)]

def entry9_8 : Integer.Sparse Key := [(key1291, 24), (key1299, -24), (key1311, -24), (key1319, -96), (key1327, -72), (key1352, 120), (key1355, 72), (key1386, 24), (key1394, -24), (key1419, -24), (key1427, -96), (key1445, -72), (key1473, 120), (key1481, 72), (key1541, 24), (key1549, -48), (key1557, -24), (key1568, 24), (key1576, -48), (key1594, -24), (key1617, -48), (key1625, -96), (key1634, -96), (key1682, 96), (key1684, 120), (key1690, 120), (key1897, 24), (key1900, 24), (key1904, 24), (key1912, 24), (key1919, -48), (key1921, -24), (key1927, -24)]

def entry12_0 : Integer.Sparse Key := [(key2361, 144), (key2366, -144), (key2452, 288), (key2456, 288), (key2458, 144), (key2461, -144), (key2517, 144), (key2519, 144), (key2523, -288), (key2528, -144), (key2530, -288), (key2560, -144)]

def entry12_5 : Integer.Sparse Key := [(key2398, -144), (key2404, -288), (key2435, -144), (key2464, 144), (key2470, 144), (key2478, 144), (key2501, 144), (key2589, -144), (key2604, 144), (key2768, -144), (key2845, -144), (key2876, -144), (key2916, 288), (key2925, 144)]

def entry12_9 : Integer.Sparse Key := [(key2370, 72), (key2398, 72), (key2464, 240), (key2470, 144), (key2478, 144), (key2501, 144), (key2568, -288), (key2570, -144), (key2575, -144), (key2583, 72), (key2589, -144), (key2762, 72), (key2768, -144), (key2839, 192), (key2845, -144), (key2876, -144)]

def entry13_7 : Integer.Sparse Key := [(key2077, 192), (key2079, 384), (key2085, 144), (key2174, -192), (key2176, -384), (key2187, -144), (key2279, -96), (key2287, 96), (key2343, -48), (key2347, 48)]

def entry13_9 : Integer.Sparse Key := [(key2077, 48), (key2079, -48), (key2174, 48), (key2176, -48), (key2274, -96), (key2276, -240), (key2279, -192), (key2287, -192), (key2341, 336), (key2343, 192), (key2347, 192)]

def entry14_7 : Integer.Sparse Key := [(key993, -144), (key1001, -288), (key1015, -288), (key1028, 144), (key1036, 288), (key1071, 288), (key1123, -288), (key1150, 288), (key1235, -144), (key1242, 144)]

def entry14_8 : Integer.Sparse Key := [(key43, -144), (key48, -288), (key74, -144), (key100, 144), (key105, 144), (key115, 144), (key137, 144), (key212, -144), (key218, 144), (key381, -144), (key432, -144), (key460, -144), (key486, 288), (key490, 144)]

def entry14_9 : Integer.Sparse Key := [(key993, 144), (key1001, -144), (key1028, 144), (key1036, -144), (key1106, 432), (key1123, 144), (key1150, 144), (key1232, -432), (key1235, -144), (key1242, -144)]

def entry15_7 : Integer.Sparse Key := [(key2584, 192), (key2588, 384), (key2599, 144), (key2763, -192), (key2767, -384), (key2888, -96), (key2909, -48), (key2930, -144), (key2967, 96), (key2988, 48)]

def entry15_9 : Integer.Sparse Key := [(key2584, 48), (key2588, -48), (key2763, 48), (key2767, -48), (key2840, -96), (key2844, -240), (key2875, 336), (key2888, -192), (key2909, 192), (key2967, -192), (key2988, 192)]

def entry16_7 : Integer.Sparse Key := [(key2610, 288), (key2626, 288), (key2635, 144), (key2665, -288), (key2700, -288), (key2721, -144), (key2780, -288), (key2789, -144), (key2803, 288), (key2824, 144)]

def entry16_8 : Integer.Sparse Key := [(key1293, -144), (key1313, 144), (key1388, 144), (key1421, -144), (key1543, 432), (key1553, 144), (key1570, -432), (key1590, -144), (key1621, -144), (key1630, 144)]

def entry16_9 : Integer.Sparse Key := [(key2626, 144), (key2635, -144), (key2700, -144), (key2721, 144), (key2780, 144), (key2789, -144), (key2803, -144), (key2824, 144), (key2855, -432), (key2865, 432)]

def entry17_8 : Integer.Sparse Key := [(key1296, 144), (key1303, 48), (key1316, -144), (key1330, -48), (key1340, -48), (key1346, 48), (key1391, 48), (key1424, -96), (key1448, -48), (key1455, 48), (key1467, 48), (key1546, -48), (key1573, 96), (key1597, 48), (key1655, -48), (key1668, -48), (key1775, -48), (key1781, 48), (key1788, 144), (key1791, 96), (key1799, 144), (key1813, -144), (key1818, -96), (key1826, -144), (key1840, -48), (key1842, 48)]

def entry18_0 : Integer.Sparse Key := [(key982, 96), (key988, -96), (key1096, 144), (key1100, -96), (key1171, 96), (key1175, -144), (key1185, 96), (key1186, -144), (key1222, 144), (key1224, -96)]

def entry18_5 : Integer.Sparse Key := [(key1003, -96), (key1009, -96), (key1017, 96), (key1022, 96), (key1044, -48), (key1073, 48), (key1116, -144), (key1125, 144), (key1130, 48), (key1152, -48), (key1159, -144), (key1174, 144), (key1233, -96), (key1236, 96), (key1243, -96), (key1247, 96)]

def entry18_7 : Integer.Sparse Key := [(key1003, 96), (key1009, 48), (key1017, -48), (key1022, -96), (key1038, -96), (key1044, -48), (key1073, 48), (key1080, 96), (key1125, -192), (key1130, -192), (key1152, 192), (key1159, 192), (key1236, -192), (key1243, 192)]

def entry18_8 : Integer.Sparse Key := [(key25, 24), (key37, 32), (key40, 24), (key50, 24), (key76, 32), (key81, 24), (key117, 24), (key139, 24), (key162, 24), (key197, 12), (key201, 12), (key204, 16), (key210, -120), (key213, -96), (key215, 64), (key217, 72), (key379, -24), (key382, -48), (key430, -144), (key461, -96), (key464, 120), (key466, 48), (key483, 84), (key565, 16), (key567, -24), (key590, -72), (key592, -144), (key609, -108), (key612, 120), (key615, 80)]

def entry18_9 : Integer.Sparse Key := [(key1003, 96), (key1009, -96), (key1017, 96), (key1022, -96), (key1038, 96), (key1044, -96), (key1073, 96), (key1080, -96), (key1116, 48), (key1125, 144), (key1130, -144), (key1152, 144), (key1159, -144), (key1174, -48), (key1233, -48), (key1247, 48)]

def entry18_17 : Integer.Sparse Key := [(key1008, -192), (key1021, 192), (key1039, 48), (key1043, -96), (key1078, 96), (key1081, -48), (key1117, -48), (key1129, 96), (key1157, -96), (key1176, 48), (key1195, -192), (key1201, 192), (key1216, -192), (key1225, 192)]

def entry21_11 : Integer.Sparse Key := [(key2370, 72), (key2398, 72), (key2464, 240), (key2467, 144), (key2476, 144), (key2499, 144), (key2534, -288), (key2540, -144), (key2551, -144), (key2583, 72), (key2586, -144), (key2762, 72), (key2765, -144), (key2839, 192), (key2842, -144), (key2874, -144)]

def entry21_15 : Integer.Sparse Key := [(key2370, 24), (key2373, -72), (key2386, -16), (key2398, 24), (key2401, -72), (key2433, -16), (key2464, -128), (key2467, -240), (key2476, -216), (key2499, -216), (key2534, 300), (key2540, 160), (key2551, 160), (key2583, 24), (key2586, 24), (key2597, 16), (key2762, 24), (key2765, 24), (key2839, 32), (key2874, 36), (key2886, 24), (key2908, 32), (key2928, 16), (key2965, 24), (key2987, 32)]

def entry21_18 : Integer.Sparse Key := [(key1003, 96), (key1007, -96), (key1017, 96), (key1020, -96), (key1038, 96), (key1042, -96), (key1073, 96), (key1077, -96), (key1116, 48), (key1125, 144), (key1128, -144), (key1152, 144), (key1156, -144), (key1172, -48), (key1194, -48), (key1223, 48)]

def entry22_11 : Integer.Sparse Key := [(key2398, -144), (key2401, -288), (key2433, -144), (key2464, 144), (key2467, 144), (key2476, 144), (key2499, 144), (key2586, -144), (key2597, 144), (key2765, -144), (key2842, -144), (key2874, -144), (key2886, 288), (key2908, 144)]

def entry22_15 : Integer.Sparse Key := [(key2370, 24), (key2373, 24), (key2386, 32), (key2398, 168), (key2401, 312), (key2433, 176), (key2464, -128), (key2467, -144), (key2476, -120), (key2499, -120), (key2534, 12), (key2540, 16), (key2551, 16), (key2583, -24), (key2586, -72), (key2597, 16), (key2762, 24), (key2765, 24), (key2839, -64), (key2842, -96), (key2874, -60), (key2886, 24), (key2908, 32), (key2928, 16), (key2965, -72), (key2987, -16)]

def entry22_18 : Integer.Sparse Key := [(key1003, -96), (key1007, -96), (key1017, 96), (key1020, 96), (key1042, -48), (key1073, 48), (key1116, -144), (key1125, 144), (key1128, 48), (key1152, -48), (key1156, -144), (key1172, 144), (key1194, -96), (key1200, 96), (key1213, -96), (key1223, 96)]

def entry23_4 : Integer.Sparse Key := [(key2357, 192), (key2361, 192), (key2363, 224), (key2366, 112), (key2452, -240), (key2456, -144), (key2458, -144), (key2461, -96), (key2517, -32), (key2519, -108), (key2523, -144), (key2528, 32), (key2530, 48), (key2560, 64), (key2567, 12), (key2579, 32)]

def entry23_10 : Integer.Sparse Key := [(key1254, -96), (key1263, 96), (key1529, 336), (key1607, -240), (key1646, -96), (key1763, 384), (key1804, -384)]

def entry23_12 : Integer.Sparse Key := [(key2357, -144), (key2361, -144), (key2363, -192), (key2366, -240), (key2452, 288), (key2458, 144), (key2461, -144), (key2519, 144), (key2523, -288), (key2567, 288), (key2579, 288)]

def entry23_18 : Integer.Sparse Key := [(key982, 48), (key988, -48), (key1096, -48), (key1100, -288), (key1171, 288), (key1175, 48), (key1185, -192), (key1186, -192), (key1222, 192), (key1224, 192)]

def entry23_23 : Integer.Sparse Key := [(key2362, 144), (key2365, 480), (key2367, 96), (key2457, -144), (key2460, -384), (key2521, -256), (key2525, -192), (key2532, 64), (key2562, 96), (key2564, 96)]

def entry25_2 : Integer.Sparse Key := [(key1049, 144), (key1052, -144), (key1135, -144), (key1140, -576), (key1205, 144), (key1207, 576)]

def entry25_11 : Integer.Sparse Key := [(key2414, 144), (key2487, 180), (key2492, 432), (key2546, -144), (key2548, -432), (key3033, 288), (key3035, -432), (key3120, 108), (key3128, -144)]

def entry25_14 : Integer.Sparse Key := [(key1049, 432), (key1052, -432), (key1135, 288), (key1140, 432), (key1205, -288), (key1207, -432)]

def entry25_15 : Integer.Sparse Key := [(key2414, 48), (key2417, -144), (key2424, -144), (key2487, -144), (key2492, -576), (key2546, 144), (key2548, 468), (key3033, 96), (key3039, 144), (key3138, 108)]

def entry25_25 : Integer.Sparse Key := [(key3081, 288), (key3082, -288), (key3086, 432), (key3088, -864), (key3091, 432)]

end MUB6.Certificate.GramEntries.Block3

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

def entry1_0 : Integer.Sparse Key := [(key970, 2880), (key1084, 8640), (key1226, 2880)]

end MUB6.Certificate.GramEntries.Block5

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

def terms0 : Array TaggedTerm := #[
  ⟨1, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 0, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 1, 0], 2⟩,
  ⟨1, ![1, 0, 0, -3, 1, 1], 2⟩,
  ⟨1, ![1, 0, 0, 1, -3, 1], 2⟩,
  ⟨1, ![1, 0, 0, 1, 1, -3], 2⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], 2⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], 2⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], 2⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], 2⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], 2⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], 2⟩,
  ⟨1, ![1, 1, -3, 0, 0, 1], -2⟩,
  ⟨1, ![1, 1, -3, 0, 1, 0], -2⟩,
  ⟨1, ![1, 1, -3, 1, 0, 0], -2⟩,
  ⟨1, ![1, 1, 0, -3, 0, 1], -2⟩,
  ⟨1, ![1, 1, 0, -3, 1, 0], -2⟩,
  ⟨1, ![1, 1, 0, 0, -3, 1], -2⟩,
  ⟨1, ![1, 1, 0, 0, 1, -3], -2⟩,
  ⟨1, ![1, 1, 0, 1, -3, 0], -2⟩,
  ⟨1, ![1, 1, 0, 1, 0, -3], -2⟩,
  ⟨1, ![1, 1, 1, -3, 0, 0], -2⟩,
  ⟨1, ![1, 1, 1, 0, -3, 0], -2⟩,
  ⟨1, ![1, 1, 1, 0, 0, -3], -2⟩
]

def terms1 : Array TaggedTerm := #[
  ⟨0, ![3, -3, 0, 0, 0, 0], -24⟩,
  ⟨0, ![3, 0, -3, 0, 0, 0], 6⟩,
  ⟨0, ![3, 0, 0, -3, 0, 0], 6⟩,
  ⟨0, ![3, 0, 0, 0, -3, 0], 6⟩,
  ⟨0, ![3, 0, 0, 0, 0, -3], 6⟩
]

def terms10 : Array TaggedTerm := #[
  ⟨0, ![3, -1, -2, 0, 0, 0], -6⟩,
  ⟨0, ![3, -1, 0, -2, 0, 0], -6⟩,
  ⟨0, ![3, -1, 0, 0, -2, 0], -6⟩,
  ⟨0, ![3, -1, 0, 0, 0, -2], -6⟩,
  ⟨0, ![3, 0, -2, -1, 0, 0], 2⟩,
  ⟨0, ![3, 0, -2, 0, -1, 0], 2⟩,
  ⟨0, ![3, 0, -2, 0, 0, -1], 2⟩,
  ⟨0, ![3, 0, -1, -2, 0, 0], 2⟩,
  ⟨0, ![3, 0, -1, 0, -2, 0], 2⟩,
  ⟨0, ![3, 0, -1, 0, 0, -2], 2⟩,
  ⟨0, ![3, 0, 0, -2, -1, 0], 2⟩,
  ⟨0, ![3, 0, 0, -2, 0, -1], 2⟩,
  ⟨0, ![3, 0, 0, -1, -2, 0], 2⟩,
  ⟨0, ![3, 0, 0, -1, 0, -2], 2⟩,
  ⟨0, ![3, 0, 0, 0, -2, -1], 2⟩,
  ⟨0, ![3, 0, 0, 0, -1, -2], 2⟩
]

def terms11 : Array TaggedTerm := #[
  ⟨1, ![2, -3, 0, 0, 0, 1], 6⟩,
  ⟨1, ![2, -3, 0, 0, 1, 0], 6⟩,
  ⟨1, ![2, -3, 0, 1, 0, 0], 6⟩,
  ⟨1, ![2, -3, 1, 0, 0, 0], 6⟩,
  ⟨1, ![2, 1, -3, 0, 0, 0], -6⟩,
  ⟨1, ![2, 1, 0, -3, 0, 0], -6⟩,
  ⟨1, ![2, 1, 0, 0, -3, 0], -6⟩,
  ⟨1, ![2, 1, 0, 0, 0, -3], -6⟩
]

def terms12 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 0, 2], 6⟩,
  ⟨1, ![1, -3, 0, 0, 2, 0], 6⟩,
  ⟨1, ![1, -3, 0, 2, 0, 0], 6⟩,
  ⟨1, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨1, ![1, 2, -3, 0, 0, 0], -6⟩,
  ⟨1, ![1, 2, 0, -3, 0, 0], -6⟩,
  ⟨1, ![1, 2, 0, 0, -3, 0], -6⟩,
  ⟨1, ![1, 2, 0, 0, 0, -3], -6⟩
]

def terms13 : Array TaggedTerm := #[
  ⟨0, ![-1, -1, 0, 0, 0, 2], -6⟩,
  ⟨0, ![-1, -1, 0, 0, 2, 0], -6⟩,
  ⟨0, ![-1, -1, 0, 2, 0, 0], -6⟩,
  ⟨0, ![-1, -1, 2, 0, 0, 0], -6⟩,
  ⟨0, ![-1, 0, -1, 0, 0, 2], 2⟩,
  ⟨0, ![-1, 0, -1, 0, 2, 0], 2⟩,
  ⟨0, ![-1, 0, -1, 2, 0, 0], 2⟩,
  ⟨0, ![-1, 0, 0, -1, 0, 2], 2⟩,
  ⟨0, ![-1, 0, 0, -1, 2, 0], 2⟩,
  ⟨0, ![-1, 0, 0, 0, -1, 2], 2⟩,
  ⟨0, ![-1, 0, 0, 0, 2, -1], 2⟩,
  ⟨0, ![-1, 0, 0, 2, -1, 0], 2⟩,
  ⟨0, ![-1, 0, 0, 2, 0, -1], 2⟩,
  ⟨0, ![-1, 0, 2, -1, 0, 0], 2⟩,
  ⟨0, ![-1, 0, 2, 0, -1, 0], 2⟩,
  ⟨0, ![-1, 0, 2, 0, 0, -1], 2⟩
]

def terms14 : Array TaggedTerm := #[
  ⟨0, ![1, -3, 0, 0, 0, 2], 6⟩,
  ⟨0, ![1, -3, 0, 0, 2, 0], 6⟩,
  ⟨0, ![1, -3, 0, 2, 0, 0], 6⟩,
  ⟨0, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨0, ![1, 2, -3, 0, 0, 0], -6⟩,
  ⟨0, ![1, 2, 0, -3, 0, 0], -6⟩,
  ⟨0, ![1, 2, 0, 0, -3, 0], -6⟩,
  ⟨0, ![1, 2, 0, 0, 0, -3], -6⟩
]

def terms15 : Array TaggedTerm := #[
  ⟨1, ![2, -3, 0, 0, 0, 1], -6⟩,
  ⟨1, ![2, -3, 0, 0, 1, 0], -6⟩,
  ⟨1, ![2, -3, 0, 1, 0, 0], -6⟩,
  ⟨1, ![2, -3, 1, 0, 0, 0], -6⟩,
  ⟨1, ![2, 0, -3, 0, 0, 1], 2⟩,
  ⟨1, ![2, 0, -3, 0, 1, 0], 2⟩,
  ⟨1, ![2, 0, -3, 1, 0, 0], 2⟩,
  ⟨1, ![2, 0, 0, -3, 0, 1], 2⟩,
  ⟨1, ![2, 0, 0, -3, 1, 0], 2⟩,
  ⟨1, ![2, 0, 0, 0, -3, 1], 2⟩,
  ⟨1, ![2, 0, 0, 0, 1, -3], 2⟩,
  ⟨1, ![2, 0, 0, 1, -3, 0], 2⟩,
  ⟨1, ![2, 0, 0, 1, 0, -3], 2⟩,
  ⟨1, ![2, 0, 1, -3, 0, 0], 2⟩,
  ⟨1, ![2, 0, 1, 0, -3, 0], 2⟩,
  ⟨1, ![2, 0, 1, 0, 0, -3], 2⟩
]

def terms16 : Array TaggedTerm := #[
  ⟨1, ![3, -2, -1, 0, 0, 0], -6⟩,
  ⟨1, ![3, -2, 0, -1, 0, 0], -6⟩,
  ⟨1, ![3, -2, 0, 0, -1, 0], -6⟩,
  ⟨1, ![3, -2, 0, 0, 0, -1], -6⟩,
  ⟨1, ![3, -1, -2, 0, 0, 0], 6⟩,
  ⟨1, ![3, -1, 0, -2, 0, 0], 6⟩,
  ⟨1, ![3, -1, 0, 0, -2, 0], 6⟩,
  ⟨1, ![3, -1, 0, 0, 0, -2], 6⟩
]

def terms17 : Array TaggedTerm := #[
  ⟨1, ![1, -1, -2, 0, 1, 1], -2⟩,
  ⟨1, ![1, -1, -2, 1, 0, 1], -2⟩,
  ⟨1, ![1, -1, -2, 1, 1, 0], -2⟩,
  ⟨1, ![1, -1, 0, -2, 1, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, -2, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, 1, -2], -2⟩,
  ⟨1, ![1, -1, 1, -2, 0, 1], -2⟩,
  ⟨1, ![1, -1, 1, -2, 1, 0], -2⟩,
  ⟨1, ![1, -1, 1, 0, -2, 1], -2⟩,
  ⟨1, ![1, -1, 1, 0, 1, -2], -2⟩,
  ⟨1, ![1, -1, 1, 1, -2, 0], -2⟩,
  ⟨1, ![1, -1, 1, 1, 0, -2], -2⟩,
  ⟨1, ![1, 0, -2, -1, 1, 1], 2⟩,
  ⟨1, ![1, 0, -2, 1, -1, 1], 2⟩,
  ⟨1, ![1, 0, -2, 1, 1, -1], 2⟩,
  ⟨1, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, -2, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, 1, -2], 2⟩,
  ⟨1, ![1, 0, 1, -2, -1, 1], 2⟩,
  ⟨1, ![1, 0, 1, -2, 1, -1], 2⟩,
  ⟨1, ![1, 0, 1, -1, -2, 1], 2⟩,
  ⟨1, ![1, 0, 1, -1, 1, -2], 2⟩,
  ⟨1, ![1, 0, 1, 1, -2, -1], 2⟩,
  ⟨1, ![1, 0, 1, 1, -1, -2], 2⟩
]

def terms18 : Array TaggedTerm := #[
  ⟨0, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨0, ![1, 0, -3, 1, 0, 1], 2⟩,
  ⟨0, ![1, 0, -3, 1, 1, 0], 2⟩,
  ⟨0, ![1, 0, 0, -3, 1, 1], 2⟩,
  ⟨0, ![1, 0, 0, 1, -3, 1], 2⟩,
  ⟨0, ![1, 0, 0, 1, 1, -3], 2⟩,
  ⟨0, ![1, 0, 1, -3, 0, 1], 2⟩,
  ⟨0, ![1, 0, 1, -3, 1, 0], 2⟩,
  ⟨0, ![1, 0, 1, 0, -3, 1], 2⟩,
  ⟨0, ![1, 0, 1, 0, 1, -3], 2⟩,
  ⟨0, ![1, 0, 1, 1, -3, 0], 2⟩,
  ⟨0, ![1, 0, 1, 1, 0, -3], 2⟩,
  ⟨0, ![1, 1, -3, 0, 0, 1], -2⟩,
  ⟨0, ![1, 1, -3, 0, 1, 0], -2⟩,
  ⟨0, ![1, 1, -3, 1, 0, 0], -2⟩,
  ⟨0, ![1, 1, 0, -3, 0, 1], -2⟩,
  ⟨0, ![1, 1, 0, -3, 1, 0], -2⟩,
  ⟨0, ![1, 1, 0, 0, -3, 1], -2⟩,
  ⟨0, ![1, 1, 0, 0, 1, -3], -2⟩,
  ⟨0, ![1, 1, 0, 1, -3, 0], -2⟩,
  ⟨0, ![1, 1, 0, 1, 0, -3], -2⟩,
  ⟨0, ![1, 1, 1, -3, 0, 0], -2⟩,
  ⟨0, ![1, 1, 1, 0, -3, 0], -2⟩,
  ⟨0, ![1, 1, 1, 0, 0, -3], -2⟩
]

def terms19 : Array TaggedTerm := #[
  ⟨1, ![3, -1, -1, -1, 0, 0], -4⟩,
  ⟨1, ![3, -1, -1, 0, -1, 0], -4⟩,
  ⟨1, ![3, -1, -1, 0, 0, -1], -4⟩,
  ⟨1, ![3, -1, 0, -1, -1, 0], -4⟩,
  ⟨1, ![3, -1, 0, -1, 0, -1], -4⟩,
  ⟨1, ![3, -1, 0, 0, -1, -1], -4⟩,
  ⟨1, ![3, 0, -1, -1, -1, 0], 6⟩,
  ⟨1, ![3, 0, -1, -1, 0, -1], 6⟩,
  ⟨1, ![3, 0, -1, 0, -1, -1], 6⟩,
  ⟨1, ![3, 0, 0, -1, -1, -1], 6⟩
]

def terms20 : Array TaggedTerm := #[
  ⟨0, ![-2, 0, 0, 0, 0, 2], 6⟩,
  ⟨0, ![-2, 0, 0, 0, 2, 0], 6⟩,
  ⟨0, ![-2, 0, 0, 2, 0, 0], 6⟩,
  ⟨0, ![-2, 0, 2, 0, 0, 0], 6⟩,
  ⟨0, ![-2, 2, 0, 0, 0, 0], -24⟩
]

def terms21 : Array TaggedTerm := #[
  ⟨1, ![2, 0, -2, -1, 0, 1], 1⟩,
  ⟨1, ![2, 0, -2, -1, 1, 0], 1⟩,
  ⟨1, ![2, 0, -2, 0, -1, 1], 1⟩,
  ⟨1, ![2, 0, -2, 0, 1, -1], 1⟩,
  ⟨1, ![2, 0, -2, 1, -1, 0], 1⟩,
  ⟨1, ![2, 0, -2, 1, 0, -1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], 1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], 1⟩,
  ⟨1, ![2, 0, 0, -2, -1, 1], 1⟩,
  ⟨1, ![2, 0, 0, -2, 1, -1], 1⟩,
  ⟨1, ![2, 0, 0, -1, -2, 1], 1⟩,
  ⟨1, ![2, 0, 0, -1, 1, -2], 1⟩,
  ⟨1, ![2, 0, 0, 1, -2, -1], 1⟩,
  ⟨1, ![2, 0, 0, 1, -1, -2], 1⟩,
  ⟨1, ![2, 0, 1, -2, -1, 0], 1⟩,
  ⟨1, ![2, 0, 1, -2, 0, -1], 1⟩,
  ⟨1, ![2, 0, 1, -1, -2, 0], 1⟩,
  ⟨1, ![2, 0, 1, -1, 0, -2], 1⟩,
  ⟨1, ![2, 0, 1, 0, -2, -1], 1⟩,
  ⟨1, ![2, 0, 1, 0, -1, -2], 1⟩,
  ⟨1, ![2, 1, -2, -1, 0, 0], -2⟩,
  ⟨1, ![2, 1, -2, 0, -1, 0], -2⟩,
  ⟨1, ![2, 1, -2, 0, 0, -1], -2⟩,
  ⟨1, ![2, 1, -1, -2, 0, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, -2, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, 0, -2], -2⟩,
  ⟨1, ![2, 1, 0, -2, -1, 0], -2⟩,
  ⟨1, ![2, 1, 0, -2, 0, -1], -2⟩,
  ⟨1, ![2, 1, 0, -1, -2, 0], -2⟩,
  ⟨1, ![2, 1, 0, -1, 0, -2], -2⟩,
  ⟨1, ![2, 1, 0, 0, -2, -1], -2⟩,
  ⟨1, ![2, 1, 0, 0, -1, -2], -2⟩
]

end MUB6.Certificate.GramFunctions.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9741 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9742 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9743 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9744 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9745 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9746 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9747 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9748 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9749 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9750 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9751 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9752 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

def row9753 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9754 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9755 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9756 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9757 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9758 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9759 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9760 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9761 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9762 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9763 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9764 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

def row9816 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9817 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9818 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9819 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9820 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9821 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9822 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9823 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9824 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9825 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9826 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9827 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9828 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9829 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9830 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9831 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9832 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9833 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9834 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9835 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

def row9836 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9933 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9934 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9935 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9936 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9937 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9938 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9939 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9940 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9941 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9942 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9943 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9944 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9945 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9946 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9947 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9948 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9949 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9950 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9951 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9952 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9953 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9954 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9955 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9956 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9957 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9958 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9959 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9960 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9961 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9962 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9963 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9964 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9965 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9966 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9967 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9968 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9969 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9970 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9971 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9972 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9973 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9974 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9975 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9976 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9977 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9978 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9979 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9980 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9981 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

def row9982 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

def row9983 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9984 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 4), (key156, -4), (key161, 4), (key203, 4)]

def row9985 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 2), (key156, -4), (key161, 4), (key165, 2), (key187, 4)]

def row9986 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 2), (key156, -4), (key161, 4), (key165, 2), (key187, 4)]

def row9987 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9988 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9989 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9990 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9991 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9992 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9993 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9994 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9995 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9996 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9997 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9998 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9999 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10000 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10001 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10002 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10003 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10004 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10005 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10006 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10007 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10008 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10009 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10010 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10011 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10012 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10013 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10014 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10015 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10016 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10017 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10018 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10019 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10020 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10021 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10022 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10023 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10024 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10025 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10026 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10027 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10028 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10029 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10030 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10031 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10032 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10033 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10034 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10035 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10036 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10037 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10038 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10039 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10040 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10041 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10042 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10043 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10044 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10045 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10046 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10047 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10048 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10049 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10050 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10051 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10052 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10053 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10054 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10055 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10056 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10057 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10058 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10059 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10060 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10061 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10062 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10063 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10064 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10065 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10066 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10067 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10068 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10069 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10070 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10071 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10072 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10073 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10074 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10075 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10076 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10077 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10078 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10079 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10080 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10081 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10082 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10083 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10084 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10085 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10086 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10087 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10088 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10089 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10090 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10091 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10092 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10093 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10094 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10095 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10096 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10097 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10098 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10099 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10100 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10101 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10102 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10103 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10104 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10105 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10106 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10107 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10108 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10109 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10110 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10111 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10112 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10113 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10114 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10115 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10116 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10117 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10118 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10119 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10120 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10121 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10122 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10123 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10124 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10125 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

def row10126 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

def row10127 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

def row10128 : Integer.Sparse Key := [(key37, 2), (key40, 2), (key76, 2), (key81, 2), (key162, 2), (key204, 2), (key210, -2), (key213, -2), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key590, -2), (key592, -4), (key609, -2)]

def row10129 : Integer.Sparse Key := [(key37, 1), (key40, 2), (key76, 1), (key81, 2), (key162, 2), (key210, -2), (key213, -2), (key215, 1), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key565, 1), (key590, -2), (key592, -4), (key609, -2), (key615, 2)]

def row10130 : Integer.Sparse Key := [(key37, 1), (key40, 2), (key76, 1), (key81, 2), (key162, 2), (key210, -2), (key213, -2), (key215, 1), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key565, 1), (key590, -2), (key592, -4), (key609, -2), (key615, 2)]

def row10131 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10132 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10133 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10134 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10135 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10136 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10137 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10138 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10139 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10140 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10141 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10142 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10143 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10144 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10145 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10146 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10147 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10148 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10149 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10150 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10151 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10152 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10153 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10154 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10155 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10156 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10157 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10158 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10159 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10160 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10161 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10162 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10163 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10164 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10165 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10166 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10167 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10168 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10169 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10170 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10171 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10172 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10173 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10174 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10175 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10176 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10177 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10178 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10179 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10180 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10181 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10182 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10183 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10184 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10185 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10186 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10187 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10188 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10189 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10190 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10191 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10192 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10193 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10194 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10195 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10196 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10197 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10198 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10199 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10200 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10201 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10202 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10203 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10204 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10205 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10206 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10207 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10208 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10209 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10210 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10211 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10212 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10213 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10214 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10215 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10216 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10217 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10218 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10219 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10220 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10221 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10222 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10223 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10224 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10225 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10226 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10227 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10228 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10229 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10230 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10231 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10232 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10233 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10234 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10235 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10236 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10237 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10238 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10239 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10240 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10241 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10242 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10243 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10244 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10245 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10246 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10247 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10248 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10249 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10250 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10251 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10252 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10253 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10254 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10255 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10256 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10257 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10258 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10259 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10260 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10261 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10262 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10263 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10264 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10265 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10266 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10267 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10268 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10269 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10270 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10271 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10272 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10273 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10274 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10275 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10276 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10277 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10278 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10279 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10280 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10281 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10282 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10283 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10284 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10285 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10286 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10287 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10288 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10289 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10290 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10291 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10292 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10293 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10294 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10295 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10296 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10297 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10298 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10299 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10300 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10301 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10302 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10303 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10304 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10305 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10306 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10307 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10308 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10309 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10310 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10311 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10312 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10313 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10314 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10315 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10316 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10317 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10318 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10319 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10320 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10321 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10322 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10323 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10324 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10325 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10326 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10327 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10328 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10329 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10330 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10331 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10332 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10333 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10334 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10335 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10336 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10337 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10338 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10339 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10340 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10341 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10342 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10343 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10344 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10345 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10346 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10347 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10348 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10349 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10350 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10351 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10352 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10353 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10354 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10355 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10356 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10357 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10358 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10359 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10360 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10361 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10362 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10363 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10364 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10365 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10366 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10367 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10368 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

def row10369 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

def row10370 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

def row10371 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10372 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10373 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 2), (key163, -4), (key169, 2), (key170, -2), (key189, 4)]

def row10374 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 2), (key163, -4), (key169, 2), (key170, -2), (key189, 4)]

def row10375 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10376 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10377 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10378 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10379 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10380 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10381 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10382 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -4), (key163, 4), (key170, 2), (key189, -2), (key192, 4)]

def row10383 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -4), (key163, 4), (key170, 2), (key189, -2), (key192, 4)]

def row10384 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10385 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10386 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10387 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10388 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10389 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10390 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10391 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10392 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10393 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10394 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10395 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10396 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10397 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10398 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10399 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10400 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10401 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10402 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10403 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10404 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10405 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10406 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10407 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10408 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10409 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10410 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10411 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10412 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10413 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10414 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10415 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10416 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10417 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10418 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10419 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

def row10420 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

def row10421 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

def row10422 : Integer.Sparse Key := [(key2677, -6), (key2811, -6), (key3045, -2), (key3059, 8), (key3094, 2), (key3122, 4)]

def row10423 : Integer.Sparse Key := [(key2677, -6), (key2811, -6), (key3045, -2), (key3059, 8), (key3094, 2), (key3122, 4)]

def row10424 : Integer.Sparse Key := [(key2677, -6), (key2811, -12), (key3045, -2), (key3059, 8), (key3094, 8), (key3122, 4)]

def row10425 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 6)]

def row10426 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 6)]

def row10427 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2811, 2), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 4)]

def row10428 : Integer.Sparse Key := [(key2677, 6), (key2708, -12), (key2811, 6), (key2861, -6), (key3045, 6)]

def row10429 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10430 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10431 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10432 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10433 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10434 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10435 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10436 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10437 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10438 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10439 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10440 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10441 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10442 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10443 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10444 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10445 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10446 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10447 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10448 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10449 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10450 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10451 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10452 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10453 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10454 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10455 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

def row10456 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

def row10457 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

def row10458 : Integer.Sparse Key := [(key2412, 6), (key2485, -18), (key3031, 12)]

def row10459 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10460 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10461 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10462 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10463 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10464 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10465 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10466 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10467 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10468 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10469 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10470 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10471 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10472 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10473 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10474 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10475 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10476 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10477 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10478 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10479 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10480 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10481 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10482 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10483 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10484 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10485 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10486 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10487 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10488 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10489 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10490 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10491 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10492 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10493 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10494 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10495 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10496 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

def row10497 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

def row10498 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

def row10500 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10501 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10502 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10503 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10504 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10505 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10506 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10507 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10508 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10509 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10510 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10511 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10512 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10513 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10514 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10515 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10516 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10517 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10518 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10519 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10520 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10521 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10522 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10523 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10524 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10525 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10526 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10527 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10528 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10529 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10530 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10531 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10532 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10533 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10534 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10535 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10536 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10537 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10538 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10539 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10540 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10541 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10542 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10543 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10544 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10545 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10546 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10547 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10548 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10549 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

def row10550 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

def row10551 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

def row10552 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 6), (key3045, 6), (key3094, 6)]

def row10553 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 6), (key3045, 6), (key3094, 6)]

def row10554 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 12), (key3045, 6)]

def row10555 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10556 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10557 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10558 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10559 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10560 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10561 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10562 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10563 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10564 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10565 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10566 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10567 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10568 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10569 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10570 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10571 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10572 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10573 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10574 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10575 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10576 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10577 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10578 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10579 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10580 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10581 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10582 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10583 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10584 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10585 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10586 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10587 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10588 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10589 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10590 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10591 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10592 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10593 : Integer.Sparse Key := [(key1851, -24), (key1855, 24)]

def row10594 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10595 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10596 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10597 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10598 : Integer.Sparse Key := [(key685, 24), (key692, -24)]

def row10599 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10600 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10601 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10602 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10603 : Integer.Sparse Key := [(key619, 24), (key645, -24)]

def row10604 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10605 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10606 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10607 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10608 : Integer.Sparse Key := [(key1958, 24), (key1960, -24)]

def row10609 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10610 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10611 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10612 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10613 : Integer.Sparse Key := [(key1852, 24), (key1884, -24)]

def row10614 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10615 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10616 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10617 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10618 : Integer.Sparse Key := [(key1861, 24), (key1867, -24)]

def row10619 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10620 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10621 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10622 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10623 : Integer.Sparse Key := [(key1957, 24), (key1969, -24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10624 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10625 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10626 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10627 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10628 : Integer.Sparse Key := [(key1867, 24), (key1877, -24)]

def row10629 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10630 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10631 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10632 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10633 : Integer.Sparse Key := [(key627, 24), (key629, -24)]

def row10634 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10635 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10636 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10637 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10638 : Integer.Sparse Key := [(key1859, -24), (key1861, 24)]

def row10639 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10640 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10641 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10642 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10643 : Integer.Sparse Key := [(key686, 24), (key687, -24)]

def row10644 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10645 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10646 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10647 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10648 : Integer.Sparse Key := [(key1932, -24), (key1953, 24)]

def row10649 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10650 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10651 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10652 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10653 : Integer.Sparse Key := [(key1850, -24), (key1884, 24)]

def row10654 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10655 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10656 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10657 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10658 : Integer.Sparse Key := [(key362, 24), (key366, -24)]

def row10659 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10660 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10661 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10662 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10663 : Integer.Sparse Key := [(key617, -24), (key645, 24)]

def row10664 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10665 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10666 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10667 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10668 : Integer.Sparse Key := [(key1933, 24), (key1953, -24)]

def row10669 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10670 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10671 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10672 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10673 : Integer.Sparse Key := [(key1960, 24), (key1966, -24)]

def row10674 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10675 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10676 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10677 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10678 : Integer.Sparse Key := [(key1864, 24), (key1869, -24)]

def row10679 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10680 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10681 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10682 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10683 : Integer.Sparse Key := [(key618, -24), (key622, 24)]

def row10684 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10685 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10686 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10687 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10688 : Integer.Sparse Key := [(key1962, 24), (key1964, -24)]

def row10689 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10690 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10691 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10692 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10693 : Integer.Sparse Key := [(key288, -24), (key289, 24)]

def row10730 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10731 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10732 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10733 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10734 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10735 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10736 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10737 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10738 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10739 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10740 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10741 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10742 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10743 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10744 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10745 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10746 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10747 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10748 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10749 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10750 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10751 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10752 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10753 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10754 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10755 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10756 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10757 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10758 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10759 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10760 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10761 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10762 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10763 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10764 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10765 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10766 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10767 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10768 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10769 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10770 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10771 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10772 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10773 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10774 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10775 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10776 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10777 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10778 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10779 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10780 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10781 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10782 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10783 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10784 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10785 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10786 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10787 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10788 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10789 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10790 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10791 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10792 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10793 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10794 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10795 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10796 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10797 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10798 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10799 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10800 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10801 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10802 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10803 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10804 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10805 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10806 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10807 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11054 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11055 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11056 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11057 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11058 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11059 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11060 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11061 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11062 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11063 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11064 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11065 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11066 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11067 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11068 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11069 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11070 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11071 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11072 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11073 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11074 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11075 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11076 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11077 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11078 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11079 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11080 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11081 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11082 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11083 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11084 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11085 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11086 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11087 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11088 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11089 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11090 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11091 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11092 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11093 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11094 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11095 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11096 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11097 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11098 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11099 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11100 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11101 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11102 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11103 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11104 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11105 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11106 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11107 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11108 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11109 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11110 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11111 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11112 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11113 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11162 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11163 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11164 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11165 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11166 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11167 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11168 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11169 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11170 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11171 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11172 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11173 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11174 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11175 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11176 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11177 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11178 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11179 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11180 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11181 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11182 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11183 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11184 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11185 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11186 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11187 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11188 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11189 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11190 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11191 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11192 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11193 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11194 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11195 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11196 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11197 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11234 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11235 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11236 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11237 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11238 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11239 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11240 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11241 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11242 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11243 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11244 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11245 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11246 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2928, 2), (key2987, 2)]

def row11247 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2928, 2), (key2987, 2)]

def row11248 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2987, 2)]

def row11249 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2987, 2)]

def row11250 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2)]

def row11251 : Integer.Sparse Key := [(key2386, 2), (key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2583, 2), (key2586, 2), (key2765, 2), (key2874, 2)]

def row11252 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2), (key2839, 2)]

def row11253 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2), (key2839, 2)]

def row11254 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2), (key2839, 2)]

def row11255 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2), (key2839, 2)]

def row11256 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2)]

def row11257 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2)]

def row11258 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11259 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11260 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11261 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11262 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11263 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11264 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11265 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11266 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11267 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11268 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11269 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11342 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11343 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11344 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11345 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11346 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11347 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11348 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11349 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11350 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11351 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11352 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11353 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11354 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11355 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11356 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11357 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11358 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11359 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11360 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11361 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11362 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11363 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11364 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11365 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11366 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11367 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11368 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11369 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11370 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11371 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11372 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11373 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11374 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11375 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11376 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11377 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11378 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11379 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11380 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11381 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11382 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11383 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11384 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11385 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11386 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11387 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11388 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11389 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11390 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11391 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11392 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11393 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11394 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11395 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11396 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11397 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11398 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11399 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11400 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11401 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11402 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11403 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11404 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11405 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11406 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11407 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11408 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11409 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11410 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11411 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11412 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11413 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11414 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11415 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11416 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11417 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11418 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11419 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11420 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11421 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11422 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11423 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11424 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11425 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11426 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11427 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11428 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11429 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11430 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11431 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11432 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11433 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11434 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11435 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11436 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11437 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11438 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11439 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11440 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11441 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11442 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11443 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11444 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11445 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11446 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11447 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11448 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11449 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6993 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key822, -4), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6994 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key822, -4), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6995 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6996 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6997 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6998 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6999 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row7000 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7001 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7002 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7003 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7004 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 6), (key822, -4), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7005 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 6), (key822, -4), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7006 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 2), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7007 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 2), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7008 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -4), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7009 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 3), (key822, -1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7010 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 3), (key822, -1), (key827, -1), (key875, 1), (key879, -3), (key906, 1), (key910, 1)]

def row7011 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -6), (key822, 2), (key827, 2), (key875, -2), (key879, 6), (key906, -2), (key910, -2)]

def row7012 : Integer.Sparse Key := [(key781, 4), (key784, -4), (key806, -8), (key809, 4), (key814, 4), (key822, 4), (key827, -4), (key875, 4), (key879, -4), (key906, -4), (key910, 4)]

def row7013 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7014 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7015 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7016 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row7017 : Integer.Sparse Key := [(key781, 4), (key784, -4), (key806, -8), (key809, 4), (key814, 4), (key822, 4), (key827, -4), (key875, 4), (key879, -4), (key906, -4), (key910, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7372 : Integer.Sparse Key := [(key1088, 24), (key1178, -24)]

def row7373 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7374 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7375 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7376 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7377 : Integer.Sparse Key := [(key0, -24), (key83, 24)]

def row7378 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7379 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7380 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7381 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7494 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

def row7495 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

def row7496 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

def row7497 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

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

def row8485 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8486 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8487 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8488 : Integer.Sparse Key := [(key1254, 6), (key1263, -6), (key1607, 6), (key1646, -12), (key1804, 12), (key1835, -6)]

def row8489 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8490 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8491 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8492 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8493 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8494 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8495 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8496 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8497 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8498 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8499 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8500 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, -2), (key1607, -4), (key1763, 2), (key1835, 4)]

def row8501 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8502 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8503 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8504 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 18)]

def row8505 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

def row8506 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

def row8507 : Integer.Sparse Key := [(key16, 6), (key98, -24), (key374, 6), (key425, 12)]

def row8508 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

def row8509 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

def row8510 : Integer.Sparse Key := [(key41, 6), (key98, -24), (key205, 6), (key425, 12)]

def row8511 : Integer.Sparse Key := [(key16, 6), (key98, -18), (key374, 6), (key425, 6)]

def row8512 : Integer.Sparse Key := [(key16, 6), (key98, -18), (key374, 6), (key425, 6)]

def row8513 : Integer.Sparse Key := [(key41, 6), (key98, -18), (key205, 6), (key425, 6)]

def row8514 : Integer.Sparse Key := [(key41, 6), (key98, -18), (key205, 6), (key425, 6)]

def row8515 : Integer.Sparse Key := [(key16, 6), (key98, -12), (key374, 6)]

def row8516 : Integer.Sparse Key := [(key41, 6), (key98, -12), (key205, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8597 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8598 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8599 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8600 : Integer.Sparse Key := [(key1289, 6), (key1384, -6), (key1539, -12), (key1566, 12), (key1895, -6), (key1902, 6)]

def row8601 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8602 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8603 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8604 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8605 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8606 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8607 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8608 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8609 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8610 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8611 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8612 : Integer.Sparse Key := [(key1309, 4), (key1350, 2), (key1417, -4), (key1471, -2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row8613 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8614 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8615 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8616 : Integer.Sparse Key := [(key238, -6), (key250, 6), (key387, 6), (key408, -12), (key417, -6), (key437, 6), (key449, 6)]

def row8617 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8618 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8619 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8620 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8621 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8622 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8623 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8624 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8625 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8626 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8627 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8628 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, 2), (key318, -2), (key387, 2), (key396, 2), (key408, 2), (key417, 2), (key437, -4), (key441, -2), (key449, -2)]

def row8629 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8630 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8631 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8632 : Integer.Sparse Key := [(key1309, 6), (key1350, -6), (key1417, 6), (key1471, -6), (key1615, 6), (key1680, -12), (key1917, 6)]

def row8633 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8634 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8635 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8636 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8637 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8638 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8639 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8640 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8641 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8642 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8643 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8644 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, -2), (key1566, -2), (key1615, -4), (key1680, 2), (key1895, 2), (key1902, 2), (key1917, 2)]

def row8645 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8646 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8647 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8648 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key314, 6), (key404, -18), (key433, 12)]

def row8649 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8650 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8651 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8652 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

def row8653 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

def row8654 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, 2), (key404, 4), (key433, -8)]

def row8655 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8656 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8657 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key383, 2), (key404, 4), (key433, -8)]

def row8658 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key383, 2), (key404, 4), (key433, -8)]

def row8659 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

def row8660 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, 2), (key314, -2), (key383, 4), (key404, 4), (key433, -8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8717 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8718 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8719 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8720 : Integer.Sparse Key := [(key2584, -6), (key2588, -12), (key2599, -6), (key2763, 6), (key2767, 12), (key2930, 6)]

def row8721 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8722 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8723 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8724 : Integer.Sparse Key := [(key2599, 6), (key2888, 12), (key2909, 6), (key2930, -6), (key2967, -12), (key2988, -6)]

def row8733 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8734 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8735 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8736 : Integer.Sparse Key := [(key2840, 6), (key2844, 6), (key2875, -12), (key2888, 6), (key2909, -6), (key2967, 6), (key2988, -6)]

def row8737 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8738 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8739 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8740 : Integer.Sparse Key := [(key2584, -6), (key2588, 6), (key2763, -6), (key2767, 6), (key2840, -12), (key2844, 6), (key2875, 6)]

def row8757 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8758 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8759 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8760 : Integer.Sparse Key := [(key2361, -6), (key2366, 6), (key2456, -12), (key2461, 6), (key2517, -6), (key2523, 12)]

def row8777 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8778 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8779 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8780 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6)]

def row8781 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8782 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8783 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8784 : Integer.Sparse Key := [(key2589, 6), (key2604, -6), (key2768, 6), (key2845, 6), (key2876, 6), (key2916, -12), (key2925, -6)]

def row8809 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8810 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8811 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8812 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2568, -12), (key2570, -6), (key2575, -6)]

def row8813 : Integer.Sparse Key := [(key2370, -6), (key2398, -6), (key2464, -12), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def row8814 : Integer.Sparse Key := [(key2370, -4), (key2398, -4), (key2464, -4), (key2583, -2), (key2589, 6), (key2762, -2), (key2768, 6), (key2839, -8), (key2845, 6), (key2876, 6)]

def row8815 : Integer.Sparse Key := [(key2370, -2), (key2398, -2), (key2583, -4), (key2589, 6), (key2762, -4), (key2768, 6), (key2839, -12), (key2845, 6), (key2876, 6)]

def row8816 : Integer.Sparse Key := [(key2583, -6), (key2589, 6), (key2762, -6), (key2768, 6), (key2839, -12), (key2845, 6), (key2876, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8953 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8954 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8955 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8956 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

def row8957 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8958 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8959 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8960 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8961 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8962 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8963 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8964 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8965 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8966 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8967 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8968 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

def row8989 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8990 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8991 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8992 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8993 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8994 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8995 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8996 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8997 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8998 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row8999 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

def row9000 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9113 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9114 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9115 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9116 : Integer.Sparse Key := [(key1015, 6), (key1071, -6), (key1123, 12), (key1150, -12), (key1235, 6), (key1242, -6)]

def row9117 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9118 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9119 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9120 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key100, 6), (key105, 6), (key115, 6), (key137, 6)]

def row9121 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9122 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9123 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9124 : Integer.Sparse Key := [(key212, 6), (key218, -6), (key381, 6), (key432, 6), (key460, 6), (key486, -12), (key490, -6)]

def row9125 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

def row9126 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

def row9127 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

def row9128 : Integer.Sparse Key := [(key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6), (key1232, -12), (key1235, -6), (key1242, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9257 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9258 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9259 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9260 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9261 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9262 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9263 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9264 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9265 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9266 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9267 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9268 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

def row9281 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9282 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9283 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9284 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9285 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9286 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9287 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9288 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9289 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9290 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9291 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row9292 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9421 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9422 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9423 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9424 : Integer.Sparse Key := [(key2610, -6), (key2626, -12), (key2635, -6), (key2665, 6), (key2780, 12), (key2789, 6)]

def row9425 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9426 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9427 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9428 : Integer.Sparse Key := [(key2610, 6), (key2665, -6), (key2700, -12), (key2721, -6), (key2803, 12), (key2824, 6)]

def row9429 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9430 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9431 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9432 : Integer.Sparse Key := [(key1388, -6), (key1421, 6), (key1543, -12), (key1553, -6), (key1570, 6), (key1619, 6), (key1621, 6)]

def row9433 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9434 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9435 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9436 : Integer.Sparse Key := [(key1293, -6), (key1313, 6), (key1543, 6), (key1570, -12), (key1590, -6), (key1619, 6), (key1630, 6)]

def row9437 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9438 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9439 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9440 : Integer.Sparse Key := [(key2700, 6), (key2721, -6), (key2803, 6), (key2824, -6), (key2853, 6), (key2855, 6), (key2865, -12)]

def row9441 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

def row9442 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

def row9443 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

def row9444 : Integer.Sparse Key := [(key2626, 6), (key2635, -6), (key2780, 6), (key2789, -6), (key2853, 6), (key2855, -12), (key2865, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9549 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9550 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9551 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9552 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9553 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9554 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9555 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9556 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9557 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9558 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9559 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9560 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

def row9561 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9562 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9563 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9564 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9565 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9566 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9567 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9568 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9569 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9570 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9571 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9572 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

def row9573 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9574 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9575 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9576 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9577 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9578 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9579 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9580 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9581 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9582 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9583 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9584 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

def row9585 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9586 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9587 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9588 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9589 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9590 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9591 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9592 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9593 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9594 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9595 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

def row9596 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9645 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9646 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9647 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9648 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9649 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9650 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9651 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9652 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9653 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9654 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9655 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9656 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

def row9657 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9658 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9659 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9660 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9661 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9662 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9663 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9664 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9665 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9666 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9667 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9668 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

def row9693 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9694 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9695 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9696 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9697 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9698 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9699 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9700 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9701 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9702 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9703 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9704 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

def row9705 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9706 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9707 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9708 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9709 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9710 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9711 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9712 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9713 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9714 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9715 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

def row9716 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

end MUB6.Certificate.GramRows

end OAI
end


