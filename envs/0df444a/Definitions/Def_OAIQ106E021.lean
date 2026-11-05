-- Prove2me | Definitions.Def_OAIQ106E021
-- name    : OAIQ106E021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:54:04.85332+00:00
-- url     : https://prove2.me/theorems/b90aeefb-1605-4890-9603-fbebf440fab3
-- title:
--   Definitions bundle OAIQ106E021 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1833 declarations of OpenAI's Lean: 1833 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block2.entries`, `OAI.MUB6.Certificate.GramEntries.Block2.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block2.entry1_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry1_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry2_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry2_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry2_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_6` and 1793 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block2Data`, `MutuallyUnbiased_GramRows_Block34`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block64`, `MutuallyUnbiased_GramRows_Block65`, `MutuallyUnbiased_GramRows_Block66`, `MutuallyUnbiased_GramRows_Block67`, `MutuallyUnbiased_GramRows_Block68`, `MutuallyUnbiased_GramRows_Block69`, `MutuallyUnbiased_GramRows_Block70`, `MutuallyUnbiased_GramRows_Block71`, `MutuallyUnbiased_GramRows_Block72`, `MutuallyUnbiased_GramRows_Block73`, `MutuallyUnbiased_GramRows_Block78`, `MutuallyUnbiased_GramRows_Block79`, `MutuallyUnbiased_GramRows_Block80`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_Moments_GramNormalization`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E022`, `OAIQ106E023`, `OAIQ106E024`, `OAIQ106E026` and `OAIQ106E151`.
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

def Key.rightCharge (K : Key) : Charge := fun i => (K.rows.getD i.val (0, 0)).2

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2608, 64), (key2614, -64), (key2624, -64), (key2630, 96), (key2638, -52), (key2657, -12), (key2659, 32), (key2663, -64), (key2669, 64), (key2698, 84), (key2704, -144), (key2724, 60), (key2752, 56), (key2757, -60), (key2778, 44), (key2784, -48), (key2792, 8), (key2801, -64), (key2807, 96), (key2827, -52), (key2919, -32), (key2922, 32), (key3007, 4), (key3009, -4), (key3011, -12), (key3016, 32), (key3022, 32), (key3025, -32)]

def entry1_0 : Integer.Sparse Key := [(key1291, 64), (key1299, -64), (key1311, -64), (key1319, 96), (key1327, -32), (key1352, -32), (key1355, 32), (key1386, -64), (key1394, 64), (key1419, 64), (key1427, -96), (key1445, 32), (key1473, 32), (key1481, -32), (key1541, 64), (key1549, -96), (key1557, 32), (key1568, -64), (key1576, 96), (key1594, -32), (key1684, -32), (key1690, 32), (key1897, 32), (key1900, -32), (key1904, -32), (key1912, 32), (key1921, 32), (key1927, -32)]

def entry1_1 : Integer.Sparse Key := [(key236, 64), (key241, -64), (key248, -64), (key253, 96), (key263, -52), (key277, -12), (key278, 32), (key302, -64), (key307, 64), (key316, 84), (key321, -144), (key331, 60), (key346, 56), (key347, -60), (key385, 44), (key390, -48), (key400, 8), (key406, -64), (key411, 96), (key421, -52), (key488, -32), (key489, 32), (key655, 4), (key656, -4), (key657, -12), (key658, 32), (key661, 32), (key662, -32)]

def entry2_0 : Integer.Sparse Key := [(key2609, 64), (key2613, -64), (key2625, -64), (key2629, 96), (key2637, -32), (key2647, -32), (key2652, 32), (key2664, -64), (key2668, 64), (key2699, 64), (key2703, -96), (key2723, 32), (key2736, 32), (key2746, -32), (key2779, 64), (key2783, -96), (key2791, 32), (key2802, -64), (key2806, 96), (key2826, -32), (key2896, -32), (key2903, 32), (key2937, 32), (key2942, -32), (key2949, -32), (key2959, 32), (key2975, 32), (key2982, -32)]

def entry2_1 : Integer.Sparse Key := [(key1292, 64), (key1297, -64), (key1312, -64), (key1317, 96), (key1325, -32), (key1338, -32), (key1344, 32), (key1387, -64), (key1392, 64), (key1420, 64), (key1425, -96), (key1443, 32), (key1456, 32), (key1465, -32), (key1542, 64), (key1547, -96), (key1555, 32), (key1569, -64), (key1574, 96), (key1592, -32), (key1658, -32), (key1666, 32), (key1773, 32), (key1779, -32), (key1789, -32), (key1797, 32), (key1816, 32), (key1824, -32)]

def entry2_2 : Integer.Sparse Key := [(key2608, 64), (key2611, -64), (key2624, -64), (key2627, 96), (key2636, -52), (key2645, -12), (key2651, 32), (key2663, -64), (key2666, 64), (key2698, 84), (key2701, -144), (key2722, 60), (key2734, 56), (key2745, -60), (key2778, 44), (key2781, -48), (key2790, 8), (key2801, -64), (key2804, 96), (key2825, -52), (key2895, -32), (key2902, 32), (key2935, 4), (key2941, -4), (key2947, -12), (key2958, 32), (key2974, 32), (key2981, -32)]

def entry3_0 : Integer.Sparse Key := [(key1003, 96), (key1009, -96), (key1017, -96), (key1022, 96), (key1038, -96), (key1044, 96), (key1073, 96), (key1080, -96), (key1125, 96), (key1130, -96), (key1152, -96), (key1159, 96)]

def entry3_1 : Integer.Sparse Key := [(key25, 48), (key27, -48), (key37, -64), (key40, 60), (key50, -48), (key52, 48), (key76, 64), (key81, -60), (key117, 36), (key120, -48), (key139, -36), (key144, 48), (key197, 6), (key201, -6), (key210, 48), (key213, -48), (key215, -32), (key217, 36), (key379, -48), (key382, 48), (key464, 60), (key466, -48), (key483, -6), (key565, 32), (key567, -36), (key590, -60), (key592, 48), (key609, 6)]

def entry3_2 : Integer.Sparse Key := [(key1003, 96), (key1007, -96), (key1017, -96), (key1020, 96), (key1038, -96), (key1042, 96), (key1073, 96), (key1077, -96), (key1125, 96), (key1128, -96), (key1152, -96), (key1156, 96)]

def entry3_3 : Integer.Sparse Key := [(key10, 96), (key13, -192), (key15, 96), (key93, -96), (key96, 96), (key158, 124), (key163, -144), (key169, 68), (key170, -48), (key189, -96), (key192, 96)]

def entry4_0 : Integer.Sparse Key := [(key2378, 48), (key2383, -48), (key2390, -64), (key2394, 60), (key2406, -48), (key2411, 48), (key2437, 64), (key2443, -60), (key2480, 36), (key2484, -48), (key2503, -36), (key2509, 48), (key2571, 6), (key2576, -6), (key2587, 48), (key2593, -48), (key2598, -32), (key2600, 36), (key2766, -48), (key2772, 48), (key2887, 60), (key2889, -48), (key2910, -6), (key2929, 32), (key2931, -36), (key2966, -60), (key2968, 48), (key2989, 6)]

def entry4_1 : Integer.Sparse Key := [(key1256, 96), (key1261, -96), (key1265, -96), (key1268, 96), (key1531, -96), (key1536, 96), (key1648, 96), (key1651, -96), (key1765, 96), (key1768, -96), (key1806, -96), (key1809, 96)]

def entry4_2 : Integer.Sparse Key := [(key2378, 96), (key2381, -96), (key2390, -96), (key2392, 96), (key2406, -96), (key2409, 96), (key2437, 96), (key2440, -96), (key2480, 96), (key2482, -96), (key2503, -96), (key2506, 96)]

def entry4_3 : Integer.Sparse Key := [(key982, 96), (key986, -192), (key988, 96), (key1096, -96), (key1100, 96), (key1171, 96), (key1175, -96), (key1185, 96), (key1186, -96), (key1222, -96), (key1224, 96)]

def entry4_4 : Integer.Sparse Key := [(key2362, 96), (key2365, -192), (key2367, 96), (key2457, -96), (key2460, 96), (key2521, 124), (key2525, -144), (key2532, 68), (key2533, -48), (key2562, -96), (key2564, 96)]

def entry5_0 : Integer.Sparse Key := [(key2612, -20), (key2616, -12), (key2618, 22), (key2621, 10), (key2628, 32), (key2640, 6), (key2641, -32), (key2644, -24), (key2646, -6), (key2648, -8), (key2653, 22), (key2660, 10), (key2667, 32), (key2673, -32), (key2702, 64), (key2726, -6), (key2728, -64), (key2732, 24), (key2735, -84), (key2737, 32), (key2747, 58), (key2758, -12), (key2782, -32), (key2794, -12), (key2795, 32), (key2805, -52), (key2809, -12), (key2829, 52), (key2831, 58), (key2835, -12), (key2860, 24), (key2870, -24), (key2893, 72), (key2897, -32), (key2904, -40), (key2936, 6), (key2938, 8), (key2943, -20), (key2948, 44), (key2950, -20), (key2960, -44), (key2972, -72), (key2976, 32), (key2983, 40), (key3010, 6), (key3012, 6), (key3017, -20), (key3023, -24), (key3026, 24)]

def entry5_1 : Integer.Sparse Key := [(key1296, -32), (key1303, 32), (key1316, 32), (key1330, -32), (key1340, -32), (key1346, 32), (key1391, 32), (key1398, -32), (key1424, 64), (key1448, -64), (key1455, -96), (key1458, 32), (key1467, 64), (key1546, -32), (key1560, 32), (key1573, -64), (key1597, 64), (key1655, 96), (key1660, -32), (key1668, -64), (key1775, 32), (key1781, -32), (key1788, 96), (key1791, -32), (key1799, -64), (key1813, -96), (key1818, 32), (key1826, 64)]

def entry5_2 : Integer.Sparse Key := [(key2616, -32), (key2619, 32), (key2632, 32), (key2642, -32), (key2649, -32), (key2654, 32), (key2671, 32), (key2674, -32), (key2706, -32), (key2729, 32), (key2738, 32), (key2748, -32), (key2786, 64), (key2794, -96), (key2796, 32), (key2809, -64), (key2829, 96), (key2832, -32), (key2860, 96), (key2870, -96), (key2898, -32), (key2905, 32), (key2939, -64), (key2944, 64), (key2951, 64), (key2961, -64), (key2977, -64), (key2984, 64)]

def entry5_3 : Integer.Sparse Key := [(key1039, 96), (key1043, -96), (key1078, -96), (key1081, 96), (key1117, -96), (key1129, 96), (key1157, 96), (key1176, -96), (key1195, 96), (key1201, -96), (key1216, -96), (key1225, 96)]

def entry5_4 : Integer.Sparse Key := [(key2379, 12), (key2382, -12), (key2393, -8), (key2407, 72), (key2410, -72), (key2441, -78), (key2445, 72), (key2473, -58), (key2483, 72), (key2507, 60), (key2526, -72), (key2539, 42), (key2544, -50), (key2555, -8), (key2557, -24), (key2565, 48), (key2592, -12), (key2595, 12), (key2602, 8), (key2771, 24), (key2774, -24), (key2848, -38), (key2882, 54), (key2891, 24), (key2912, -46), (key2933, -18), (key2934, 24), (key2970, 36), (key2991, 8), (key2993, -72), (key2996, -24), (key3003, 48)]

def entry5_5 : Integer.Sparse Key := [(key2617, 64), (key2620, -64), (key2633, -64), (key2643, 84), (key2650, 44), (key2655, -64), (key2672, 32), (key2675, -32), (key2707, -60), (key2730, 60), (key2739, 32), (key2749, -36), (key2787, -4), (key2797, 32), (key2810, 32), (key2833, -36), (key2899, -32), (key2906, 8), (key2940, 4), (key2945, -28), (key2952, -28), (key2962, -64), (key2964, 96), (key2978, 56), (key2985, 64), (key2994, -144), (key3001, -48), (key3004, 96)]

def entry6_0 : Integer.Sparse Key := [(key1292, 64), (key1298, -64), (key1312, -64), (key1318, 96), (key1326, -32), (key1351, -32), (key1354, 32), (key1387, -64), (key1393, 64), (key1420, 64), (key1426, -96), (key1444, 32), (key1472, 32), (key1480, -32), (key1542, 64), (key1548, -96), (key1556, 32), (key1569, -64), (key1575, 96), (key1593, -32), (key1683, -32), (key1689, 32), (key1896, 32), (key1899, -32), (key1903, -32), (key1911, 32), (key1920, 32), (key1926, -32)]

def entry6_1 : Integer.Sparse Key := [(key237, 64), (key240, -64), (key249, -64), (key252, 96), (key262, -32), (key268, -32), (key273, 32), (key303, -64), (key306, 64), (key317, 64), (key320, -96), (key330, 32), (key336, 32), (key342, -32), (key386, 64), (key389, -96), (key399, 32), (key407, -64), (key410, 96), (key420, -32), (key471, -32), (key477, 32), (key569, 32), (key574, -32), (key579, -32), (key585, 32), (key597, 32), (key603, -32)]

def entry6_2 : Integer.Sparse Key := [(key1291, 64), (key1295, -64), (key1311, -64), (key1315, 96), (key1324, -32), (key1336, -32), (key1343, 32), (key1386, -64), (key1390, 64), (key1419, 64), (key1423, -96), (key1442, 32), (key1454, 32), (key1464, -32), (key1541, 64), (key1545, -96), (key1554, 32), (key1568, -64), (key1572, 96), (key1591, -32), (key1657, -32), (key1665, 32), (key1771, 32), (key1778, -32), (key1787, -32), (key1796, 32), (key1815, 32), (key1823, -32)]

def entry6_3 : Integer.Sparse Key := [(key25, 96), (key26, -96), (key37, -96), (key39, 96), (key50, -96), (key51, 96), (key76, 96), (key79, -96), (key117, 96), (key119, -96), (key139, -96), (key142, 96)]

def entry6_4 : Integer.Sparse Key := [(key1256, 96), (key1260, -96), (key1265, -96), (key1267, 96), (key1531, -96), (key1535, 96), (key1648, 96), (key1650, -96), (key1765, 96), (key1767, -96), (key1806, -96), (key1808, 96)]

def entry6_5 : Integer.Sparse Key := [(key1296, -32), (key1302, 32), (key1316, 32), (key1329, -32), (key1339, -32), (key1345, 32), (key1391, 32), (key1397, -32), (key1424, 64), (key1447, -64), (key1455, -96), (key1457, 32), (key1466, 64), (key1546, -32), (key1559, 32), (key1573, -64), (key1596, 64), (key1655, 96), (key1659, -32), (key1667, -64), (key1774, 32), (key1780, -32), (key1788, 96), (key1790, -32), (key1798, -64), (key1813, -96), (key1817, 32), (key1825, 64)]

def entry6_6 : Integer.Sparse Key := [(key236, 64), (key239, -64), (key248, -64), (key251, 96), (key260, -52), (key267, -12), (key271, 32), (key302, -64), (key305, 64), (key316, 84), (key319, -144), (key328, 60), (key335, 56), (key340, -60), (key385, 44), (key388, -48), (key397, 8), (key406, -64), (key409, 96), (key418, -52), (key469, -32), (key475, 32), (key568, 4), (key572, -4), (key578, -12), (key583, 32), (key595, 32), (key601, -32)]

def entry7_0 : Integer.Sparse Key := [(key2608, 32), (key2614, -32), (key2624, -32), (key2638, 44), (key2657, 20), (key2659, -32), (key2663, -32), (key2669, 32), (key2698, 44), (key2704, -120), (key2724, 60), (key2752, 64), (key2757, -56), (key2778, 20), (key2784, 24), (key2792, -32), (key2801, -32), (key2807, 96), (key2827, -96), (key2858, -24), (key2868, 24), (key2918, -72), (key2919, 32), (key2922, 40), (key3007, -28), (key3009, 24), (key3011, -32), (key3016, 64), (key3021, 72), (key3022, -8), (key3025, -64)]

def entry7_1 : Integer.Sparse Key := [(key1291, 32), (key1299, -32), (key1311, -32), (key1327, 32), (key1352, 32), (key1355, -32), (key1386, -32), (key1394, 32), (key1419, 32), (key1427, -96), (key1445, 64), (key1473, 64), (key1481, -64), (key1541, 32), (key1557, -32), (key1568, -32), (key1576, 96), (key1594, -64), (key1682, -96), (key1684, 32), (key1690, 64), (key1897, -32), (key1900, 32), (key1904, -64), (key1912, 64), (key1919, 96), (key1921, -32), (key1927, -64)]

def entry7_2 : Integer.Sparse Key := [(key2609, 32), (key2613, -32), (key2625, -32), (key2637, 32), (key2647, 32), (key2652, -32), (key2664, -32), (key2668, 32), (key2699, 32), (key2723, -32), (key2736, -32), (key2746, 32), (key2779, 32), (key2783, -96), (key2791, 64), (key2802, -32), (key2806, 96), (key2826, -64), (key2857, -96), (key2867, 96), (key2896, 32), (key2903, -32), (key2937, 64), (key2942, -64), (key2949, -64), (key2959, 64), (key2975, 64), (key2982, -64)]

def entry7_3 : Integer.Sparse Key := [(key1038, -96), (key1044, 96), (key1073, 96), (key1080, -96), (key1116, 96), (key1130, -96), (key1152, -96), (key1174, 96), (key1233, -96), (key1236, 96), (key1243, 96), (key1247, -96)]

def entry7_4 : Integer.Sparse Key := [(key2378, -36), (key2383, 24), (key2390, 26), (key2394, -12), (key2406, -84), (key2411, 72), (key2437, 90), (key2443, -72), (key2472, 96), (key2480, -24), (key2484, -72), (key2503, -60), (key2509, -24), (key2524, 84), (key2569, -48), (key2571, 54), (key2576, 48), (key2580, -58), (key2587, 36), (key2593, -24), (key2598, -26), (key2600, 12), (key2766, -12), (key2772, 24), (key2880, -48), (key2887, 24), (key2889, -24), (key2910, 42), (key2929, 6), (key2931, -24), (key2966, -36), (key2968, 24), (key2989, 48), (key2995, 12), (key3002, -38)]

def entry7_5 : Integer.Sparse Key := [(key2612, -16), (key2616, -48), (key2618, 30), (key2621, 34), (key2628, 16), (key2632, 48), (key2640, -2), (key2641, -40), (key2644, -48), (key2646, 2), (key2648, -16), (key2653, 30), (key2658, -24), (key2660, 34), (key2667, 4), (key2671, -36), (key2673, 8), (key2676, 24), (key2702, 32), (key2706, 48), (key2726, -6), (key2728, -32), (key2732, -24), (key2735, -24), (key2737, -8), (key2747, 26), (key2753, -24), (key2758, 24), (key2782, -16), (key2794, 24), (key2795, -8), (key2798, -24), (key2805, -20), (key2809, -12), (key2829, 74), (key2831, 26), (key2835, -36), (key2860, -24), (key2870, -48), (key2885, 72), (key2893, 24), (key2897, 8), (key2904, -8), (key2920, 24), (key2923, 24), (key2927, -60), (key2936, 6), (key2938, -8), (key2943, 8), (key2948, 22), (key2950, -28), (key2960, -22), (key2972, -48), (key2976, 40), (key2983, 32), (key2997, 24), (key2998, -36), (key3000, -12), (key3010, 6), (key3012, 6), (key3017, -10), (key3023, -24), (key3030, 12)]

def entry7_6 : Integer.Sparse Key := [(key1292, 32), (key1298, -32), (key1312, -32), (key1326, 32), (key1351, 32), (key1354, -32), (key1387, -32), (key1393, 32), (key1420, 32), (key1426, -96), (key1444, 64), (key1472, 64), (key1480, -64), (key1542, 32), (key1556, -32), (key1569, -32), (key1575, 96), (key1593, -64), (key1681, -96), (key1683, 32), (key1689, 64), (key1896, -32), (key1899, 32), (key1903, -64), (key1911, 64), (key1918, 96), (key1920, -32), (key1926, -64)]

def entry7_7 : Integer.Sparse Key := [(key2608, 64), (key2614, -64), (key2624, -64), (key2638, 88), (key2657, 40), (key2659, -64), (key2663, 32), (key2669, -32), (key2698, -36), (key2704, -48), (key2724, 72), (key2752, 56), (key2757, -60), (key2778, -28), (key2784, 48), (key2792, 8), (key2801, -64), (key2807, 96), (key2827, -52), (key2851, 96), (key2858, -96), (key2868, -48), (key2918, -96), (key2919, 64), (key2922, 56), (key3007, -8), (key3009, -4), (key3011, -12), (key3016, 32), (key3021, 48), (key3022, 8), (key3025, -32)]

def entry8_0 : Integer.Sparse Key := [(key2612, 20), (key2616, 12), (key2618, -22), (key2621, -10), (key2628, 52), (key2632, 12), (key2640, -52), (key2641, -58), (key2644, 12), (key2646, -44), (key2648, 20), (key2653, 44), (key2658, -6), (key2660, 20), (key2667, -8), (key2671, -24), (key2673, 8), (key2676, 24), (key2702, 32), (key2706, -24), (key2726, 66), (key2728, -32), (key2732, -24), (key2735, -12), (key2737, -8), (key2747, 26), (key2753, 24), (key2758, -36), (key2782, -40), (key2794, 12), (key2795, 40), (key2798, -24), (key2805, -32), (key2829, -6), (key2831, 32), (key2835, 24), (key2860, 24), (key2870, -24), (key2893, 72), (key2897, -40), (key2904, -32), (key2920, -24), (key2923, 24), (key2936, 30), (key2938, -8), (key2943, -28), (key2948, 6), (key2950, 8), (key2960, -22), (key2972, -72), (key2976, 40), (key2983, 32), (key3010, 6), (key3017, -10)]

def entry8_1 : Integer.Sparse Key := [(key1296, 32), (key1303, -32), (key1316, 64), (key1330, -64), (key1337, -96), (key1340, 32), (key1346, 64), (key1391, -32), (key1398, 32), (key1424, 32), (key1448, -32), (key1458, -32), (key1467, 32), (key1546, -64), (key1560, 64), (key1573, -32), (key1597, 32), (key1655, 96), (key1660, -64), (key1668, -32), (key1772, 96), (key1775, -32), (key1781, -64), (key1791, 32), (key1799, -32), (key1813, -96), (key1818, 64), (key1826, 32)]

def entry8_2 : Integer.Sparse Key := [(key2616, 32), (key2619, -32), (key2632, 64), (key2640, -96), (key2642, 32), (key2649, -64), (key2654, 64), (key2671, -32), (key2674, 32), (key2706, -64), (key2726, 96), (key2729, -32), (key2738, 64), (key2748, -64), (key2786, 32), (key2796, -32), (key2809, -32), (key2832, 32), (key2860, 96), (key2870, -96), (key2898, -64), (key2905, 64), (key2939, -32), (key2944, 32), (key2951, 32), (key2961, -32), (key2977, -32), (key2984, 32)]

def entry8_3 : Integer.Sparse Key := [(key1004, 96), (key1008, -96), (key1021, -96), (key1023, 96), (key1117, -96), (key1129, 96), (key1157, 96), (key1176, -96), (key1195, 96), (key1202, -96), (key1214, -96), (key1225, 96)]

def entry8_4 : Integer.Sparse Key := [(key2379, 72), (key2382, -72), (key2393, -78), (key2395, 72), (key2407, 12), (key2410, -12), (key2441, -8), (key2473, -58), (key2483, 60), (key2507, 72), (key2526, -72), (key2539, 42), (key2544, -8), (key2545, -24), (key2555, -50), (key2565, 48), (key2592, 24), (key2595, -24), (key2602, -18), (key2603, 24), (key2771, -12), (key2774, 12), (key2848, -38), (key2882, 54), (key2891, 36), (key2912, 8), (key2914, -72), (key2933, 8), (key2970, 24), (key2991, -46), (key2996, -24), (key3003, 48)]

def entry8_5 : Integer.Sparse Key := [(key2617, 32), (key2620, -32), (key2633, -32), (key2643, 44), (key2650, 20), (key2655, -32), (key2672, 64), (key2675, -64), (key2707, -4), (key2730, 12), (key2739, -8), (key2749, -80), (key2751, 72), (key2787, -28), (key2797, 40), (key2810, -32), (key2833, 44), (key2899, 32), (key2906, 16), (key2915, -72), (key2940, 20), (key2945, -48), (key2946, 24), (key2952, 20), (key2962, -32), (key2978, 16), (key2985, 32), (key2994, -72), (key2999, -24), (key3001, -24), (key3004, 96)]

def entry8_6 : Integer.Sparse Key := [(key1296, 32), (key1302, -32), (key1316, 64), (key1329, -64), (key1337, -96), (key1339, 32), (key1345, 64), (key1391, -32), (key1397, 32), (key1424, 32), (key1447, -32), (key1457, -32), (key1466, 32), (key1546, -64), (key1559, 64), (key1573, -32), (key1596, 32), (key1655, 96), (key1659, -64), (key1667, -32), (key1772, 96), (key1774, -32), (key1780, -64), (key1790, 32), (key1798, -32), (key1813, -96), (key1817, 64), (key1825, 32)]

def entry8_7 : Integer.Sparse Key := [(key2612, 4), (key2616, -36), (key2618, 8), (key2621, 24), (key2628, 32), (key2640, 22), (key2641, -32), (key2644, -24), (key2646, -22), (key2648, -8), (key2653, 22), (key2660, 10), (key2667, -4), (key2671, -60), (key2673, 16), (key2676, 48), (key2702, 16), (key2706, -24), (key2726, 90), (key2728, -40), (key2732, -48), (key2737, -16), (key2747, 34), (key2753, 24), (key2758, -24), (key2782, -8), (key2786, 48), (key2795, 8), (key2798, -48), (key2805, -16), (key2809, 48), (key2829, -8), (key2831, -8), (key2835, -24), (key2860, -24), (key2870, -48), (key2885, 72), (key2893, 24), (key2897, -8), (key2904, 8), (key2920, -24), (key2927, 12), (key2936, 6), (key2938, -16), (key2943, -8), (key2948, 8), (key2950, -8), (key2960, 8), (key2972, -48), (key2976, 32), (key2983, 40), (key2997, 24), (key2998, -12), (key3000, -36), (key3008, -24), (key3010, 30), (key3012, -24), (key3017, 24), (key3023, 24), (key3026, 24), (key3030, -60)]

def entry8_8 : Integer.Sparse Key := [(key2617, 64), (key2620, -64), (key2633, 32), (key2643, -36), (key2650, -28), (key2655, -64), (key2656, 96), (key2672, 32), (key2675, -32), (key2707, -8), (key2730, 24), (key2739, 8), (key2749, -40), (key2787, -56), (key2797, 56), (key2810, -64), (key2833, 84), (key2899, 64), (key2906, 56), (key2915, -144), (key2940, 40), (key2945, -24), (key2952, 44), (key2962, -64), (key2978, 8), (key2985, -32), (key2999, -48), (key3004, 96)]

def entry9_0 : Integer.Sparse Key := [(key2066, -96), (key2071, 96), (key2093, 96), (key2096, -96), (key2155, 96), (key2168, -96), (key2195, -96), (key2201, 96), (key2248, -96), (key2255, 96), (key2306, 96), (key2311, -96)]

def entry9_1 : Integer.Sparse Key := [(key312, -12), (key313, 12), (key324, 12), (key325, -120), (key329, 102), (key339, 84), (key341, -90), (key414, 8), (key415, 96), (key419, -102), (key474, -72), (key476, 72), (key582, -58), (key584, 72), (key600, 72), (key602, -72), (key725, 12), (key727, -12), (key728, -12), (key730, 24), (key736, 12), (key748, -6), (key752, -6), (key794, -8), (key815, -38), (key832, 6), (key841, 24), (key870, -24), (key880, 24), (key929, 24), (key936, -24)]

def entry9_2 : Integer.Sparse Key := [(key2064, -96), (key2070, 96), (key2080, 96), (key2086, -96), (key2153, 96), (key2167, -96), (key2177, -96), (key2188, 96), (key2247, -96), (key2254, 96), (key2280, 96), (key2288, -96)]

def entry9_3 : Integer.Sparse Key := [(key66, -70), (key67, 96), (key78, 84), (key80, -84), (key131, 60), (key141, -58), (key143, -96), (key160, 84), (key178, -48), (key183, 102), (key191, -58), (key708, -26), (key717, 12), (key719, -12), (key862, 36), (key887, -48), (key894, -38), (key917, 90), (key949, 12), (key956, -38)]

def entry9_4 : Integer.Sparse Key := [(key1992, -96), (key1995, 96), (key2002, 96), (key2004, -96), (key2237, 96), (key2260, -96), (key2271, -96), (key2273, -96), (key2295, 192), (key2325, 96), (key2337, -96)]

def entry9_5 : Integer.Sparse Key := [(key2035, -96), (key2038, 96), (key2065, 96), (key2073, -96), (key2083, -96), (key2088, 96), (key2178, 96), (key2180, -96), (key2278, -96), (key2282, 96), (key2329, 96), (key2331, -96)]

def entry9_6 : Integer.Sparse Key := [(key729, -96), (key735, 96), (key739, 96), (key744, -96), (key795, 96), (key813, -96), (key819, -96), (key826, 96), (key869, -96), (key878, 96), (key903, 96), (key909, -96)]

def entry9_7 : Integer.Sparse Key := [(key2031, 96), (key2036, -96), (key2061, -96), (key2071, 96), (key2093, 96), (key2096, -96), (key2150, -96), (key2155, 96), (key2243, 96), (key2248, -96), (key2304, -96), (key2306, 96)]

def entry9_8 : Integer.Sparse Key := [(key2035, -96), (key2038, 96), (key2081, 96), (key2083, -96), (key2154, 96), (key2170, -96), (key2180, -96), (key2190, 96), (key2278, -96), (key2290, 96), (key2329, 96), (key2334, -96)]

def entry9_9 : Integer.Sparse Key := [(key781, 96), (key784, -96), (key806, -192), (key809, 96), (key814, 124), (key822, 68), (key827, -96), (key875, 96), (key879, -144), (key906, -48), (key910, 96)]

def entry10_0 : Integer.Sparse Key := [(key2080, 96), (key2084, -96), (key2086, -96), (key2089, 96), (key2177, -96), (key2181, 96), (key2188, 96), (key2191, -96), (key2280, 96), (key2283, -96), (key2288, -96), (key2291, 96)]

def entry10_1 : Integer.Sparse Key := [(key739, 96), (key740, -96), (key744, -96), (key745, 96), (key819, -96), (key820, 96), (key826, 96), (key829, -96), (key903, 96), (key904, -96), (key909, -96), (key912, 96)]

def entry10_2 : Integer.Sparse Key := [(key2093, 96), (key2094, -96), (key2096, -96), (key2097, 96), (key2195, -96), (key2196, 96), (key2201, 96), (key2202, -96), (key2306, 96), (key2307, -96), (key2311, -96), (key2312, 96)]

def entry10_3 : Integer.Sparse Key := [(key717, 96), (key719, -192), (key720, 96), (key894, -96), (key896, 96), (key917, 96), (key920, -96), (key949, 96), (key950, -96), (key956, -96), (key958, 96)]

def entry10_4 : Integer.Sparse Key := [(key2002, 96), (key2004, -192), (key2005, 96), (key2271, -96), (key2273, 96), (key2295, 96), (key2297, -96), (key2325, 96), (key2326, -96), (key2337, -96), (key2338, 96)]

def entry10_5 : Integer.Sparse Key := [(key2178, 96), (key2180, -96), (key2190, -96), (key2192, 96), (key2278, -96), (key2282, 96), (key2290, 96), (key2298, -96), (key2329, 96), (key2331, -96), (key2335, -96), (key2339, 96)]

def entry10_6 : Integer.Sparse Key := [(key748, 96), (key749, -96), (key752, -96), (key753, 96), (key832, -96), (key833, 96), (key841, 96), (key842, -96), (key929, 96), (key930, -96), (key936, -96), (key937, 96)]

def entry10_7 : Integer.Sparse Key := [(key2177, -96), (key2181, 96), (key2188, 96), (key2191, -96), (key2277, 96), (key2283, -96), (key2288, -96), (key2296, 96), (key2342, -96), (key2344, 96), (key2348, 96), (key2350, -96)]

def entry10_8 : Integer.Sparse Key := [(key2081, 96), (key2083, -96), (key2088, -96), (key2090, 96), (key2278, -96), (key2282, 96), (key2290, 96), (key2298, -96), (key2329, 96), (key2332, -96), (key2334, -96), (key2339, 96)]

def entry10_9 : Integer.Sparse Key := [(key822, -96), (key823, 96), (key827, 96), (key828, -96), (key906, 96), (key910, -96), (key911, -96), (key918, 96), (key952, -96), (key953, 192), (key957, -96)]

def entry10_10 : Integer.Sparse Key := [(key781, 96), (key784, -192), (key786, 96), (key806, -96), (key809, 96), (key814, 124), (key816, -144), (key822, 68), (key823, -48), (key827, -96), (key828, 96)]

def entries : Fin 11 → Fin 11 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0, entry5_0, entry6_0, entry7_0, entry8_0, entry9_0, entry10_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1, entry5_1, entry6_1, entry7_1, entry8_1, entry9_1, entry10_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2, entry5_2, entry6_2, entry7_2, entry8_2, entry9_2, entry10_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3, entry5_3, entry6_3, entry7_3, entry8_3, entry9_3, entry10_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4, entry5_4, entry6_4, entry7_4, entry8_4, entry9_4, entry10_4],
  ![entry5_0, entry5_1, entry5_2, entry5_3, entry5_4, entry5_5, entry6_5, entry7_5, entry8_5, entry9_5, entry10_5],
  ![entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry7_6, entry8_6, entry9_6, entry10_6],
  ![entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry8_7, entry9_7, entry10_7],
  ![entry8_0, entry8_1, entry8_2, entry8_3, entry8_4, entry8_5, entry8_6, entry8_7, entry8_8, entry9_8, entry10_8],
  ![entry9_0, entry9_1, entry9_2, entry9_3, entry9_4, entry9_5, entry9_6, entry9_7, entry9_8, entry9_9, entry10_9],
  ![entry10_0, entry10_1, entry10_2, entry10_3, entry10_4, entry10_5, entry10_6, entry10_7, entry10_8, entry10_9, entry10_10]
]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1293 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

def row1294 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

def row1295 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

def row1296 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

def row1297 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

def row1298 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

def row1299 : Integer.Sparse Key := [(key1433, 2), (key1439, 4), (key1477, -2), (key1479, -4), (key1582, -2), (key1588, -4), (key1688, 6), (key1908, 2), (key1910, 4), (key1925, -6)]

def row1300 : Integer.Sparse Key := [(key1433, 2), (key1439, 4), (key1477, -2), (key1479, -4), (key1582, -2), (key1588, -4), (key1688, 6), (key1908, 2), (key1910, 4), (key1925, -6)]

def row1301 : Integer.Sparse Key := [(key1433, 2), (key1439, 4), (key1477, -2), (key1479, -4), (key1582, -2), (key1588, -4), (key1688, 6), (key1908, 2), (key1910, 4), (key1925, -6)]

def row1302 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

def row1303 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

def row1304 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

def row1305 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

def row1306 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

def row1307 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

def row1308 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

def row1309 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

def row1310 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

def row1311 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

def row1312 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

def row1313 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

def row1314 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

def row1315 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

def row1316 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

def row1317 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

def row1318 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

def row1319 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

def row1320 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key302, 2), (key307, 4), (key316, -2), (key321, -2), (key331, -2), (key385, -2), (key390, -2), (key400, -2), (key406, 2), (key411, 2), (key421, 2)]

def row1321 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key302, 2), (key307, 4), (key316, -2), (key321, -2), (key331, -2), (key385, -2), (key390, -2), (key400, -2), (key406, 2), (key411, 2), (key421, 2)]

def row1322 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key302, 2), (key307, 4), (key316, -2), (key321, -2), (key331, -2), (key385, -2), (key390, -2), (key400, -2), (key406, 2), (key411, 2), (key421, 2)]

def row1323 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

def row1324 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

def row1325 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

def row1326 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

def row1327 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

def row1328 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

def row1329 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, -2), (key253, -2), (key263, -2), (key302, -2), (key307, -4), (key316, 4), (key321, 4), (key331, 2), (key346, 2), (key406, -2), (key411, -2), (key421, -2)]

def row1330 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, -2), (key253, -2), (key263, -2), (key302, -2), (key307, -4), (key316, 4), (key321, 4), (key331, 2), (key346, 2), (key406, -2), (key411, -2), (key421, -2)]

def row1331 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, -2), (key253, -2), (key263, -2), (key302, -2), (key307, -4), (key316, 4), (key321, 4), (key331, 2), (key346, 2), (key406, -2), (key411, -2), (key421, -2)]

def row1332 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

def row1333 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

def row1334 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key445, -1), (key453, 1), (key658, -1), (key661, -1), (key662, 1)]

def row1335 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key445, -1), (key453, 1), (key658, -1), (key661, -1), (key662, 1)]

def row1336 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

def row1337 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

def row1338 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

def row1339 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

def row1340 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

def row1341 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

def row1342 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

def row1343 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

def row1344 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

def row1345 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

def row1346 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key487, 1), (key489, 1), (key658, 1), (key660, -1), (key662, -1)]

def row1347 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key487, 1), (key489, 1), (key658, 1), (key660, -1), (key662, -1)]

def row1348 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

def row1349 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

def row1350 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

def row1351 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

def row1352 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

def row1353 : Integer.Sparse Key := [(key1033, 6), (key1040, -6), (key1111, -6), (key1126, 6), (key1192, 6), (key1198, -6)]

def row1354 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

def row1355 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

def row1356 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

def row1357 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

def row1358 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

def row1359 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

def row1360 : Integer.Sparse Key := [(key1033, -6), (key1040, 6), (key1111, 6), (key1126, -6), (key1192, -6), (key1198, 6)]

def row1361 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

def row1362 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

def row1363 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

def row1364 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

def row1365 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

def row1366 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

def row1367 : Integer.Sparse Key := [(key17, 6), (key28, -6), (key42, -6), (key69, 6), (key108, 6), (key132, -6)]

def row1368 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

def row1369 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

def row1370 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

def row1371 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

def row1372 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

def row1373 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

def row1374 : Integer.Sparse Key := [(key17, -6), (key28, 6), (key42, 6), (key69, -6), (key108, -6), (key132, 6)]

def row1375 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

def row1376 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

def row1377 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

def row1378 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

def row1379 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

def row1380 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

def row1381 : Integer.Sparse Key := [(key1000, 6), (key1014, -6), (key1035, -6), (key1070, 6), (key1122, 6), (key1149, -6)]

def row1382 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

def row1383 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

def row1384 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

def row1385 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

def row1386 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

def row1387 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

def row1388 : Integer.Sparse Key := [(key1000, -6), (key1014, 6), (key1035, 6), (key1070, -6), (key1122, -6), (key1149, 6)]

def row1389 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

def row1390 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

def row1391 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

def row1392 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

def row1393 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

def row1394 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

def row1395 : Integer.Sparse Key := [(key2, 6), (key6, -6), (key85, -6), (key150, 6), (key166, 6), (key186, -6)]

def row1396 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

def row1397 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

def row1398 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

def row1399 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

def row1400 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

def row1401 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

def row1402 : Integer.Sparse Key := [(key2, -6), (key6, 6), (key85, 6), (key150, -6), (key166, -6), (key186, 6)]

def row1403 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

def row1404 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

def row1405 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

def row1406 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

def row1407 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1408 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

def row1409 : Integer.Sparse Key := [(key992, 6), (key1010, -6), (key1027, -6), (key1066, 6), (key1118, 6), (key1145, -6)]

def row1410 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

def row1411 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

def row1412 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

def row1413 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

def row1414 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

def row1415 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

def row1416 : Integer.Sparse Key := [(key992, -6), (key1010, 6), (key1027, 6), (key1066, -6), (key1118, -6), (key1145, 6)]

def row1417 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

def row1418 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

def row1419 : Integer.Sparse Key := [(key992, 2), (key1010, -2), (key1027, -2), (key1066, 2), (key1118, 2), (key1145, -2)]

def row1420 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

def row1421 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

def row1422 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

def row1423 : Integer.Sparse Key := [(key376, 6), (key380, -6), (key427, -6), (key459, 6), (key465, 6), (key482, -6)]

def row1424 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

def row1425 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

def row1426 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

def row1427 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

def row1428 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

def row1429 : Integer.Sparse Key := [(key376, -2), (key380, 2), (key427, 2), (key459, -2), (key465, -2), (key482, 2)]

def row1430 : Integer.Sparse Key := [(key376, -6), (key380, 6), (key427, 6), (key459, -6), (key465, -6), (key482, 6)]

def row1431 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

def row1432 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

def row1433 : Integer.Sparse Key := [(key376, 2), (key380, -2), (key427, -2), (key459, 2), (key465, 2), (key482, -2)]

def row1434 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

def row1435 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

def row1436 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

def row1437 : Integer.Sparse Key := [(key1049, 6), (key1053, -6), (key1135, -6), (key1141, 6), (key1237, 6), (key1239, -6)]

def row1438 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

def row1439 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

def row1440 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

def row1441 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

def row1442 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

def row1443 : Integer.Sparse Key := [(key1049, -2), (key1053, 2), (key1135, 2), (key1141, -2), (key1237, -2), (key1239, 2)]

def row1444 : Integer.Sparse Key := [(key1049, -6), (key1053, 6), (key1135, 6), (key1141, -6), (key1237, -6), (key1239, 6)]

def row1445 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

def row1446 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

def row1447 : Integer.Sparse Key := [(key1049, 2), (key1053, -2), (key1135, -2), (key1141, 2), (key1237, 2), (key1239, -2)]

def row1448 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

def row1449 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

def row1450 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

def row1451 : Integer.Sparse Key := [(key211, 6), (key216, -6), (key380, -6), (key465, 6), (key566, 6), (key591, -6)]

def row1452 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

def row1453 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

def row1454 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

def row1455 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

def row1456 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

def row1457 : Integer.Sparse Key := [(key211, -2), (key216, 2), (key380, 2), (key465, -2), (key566, -2), (key591, 2)]

def row1458 : Integer.Sparse Key := [(key211, -6), (key216, 6), (key380, 6), (key465, -6), (key566, -6), (key591, 6)]

def row1459 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

def row1460 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

def row1461 : Integer.Sparse Key := [(key211, 2), (key216, -2), (key380, -2), (key465, 2), (key566, 2), (key591, -2)]

def row1462 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -2), (key164, -2), (key184, 2)]

def row1463 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -2), (key164, -2), (key184, 2)]

def row1464 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -2), (key164, -2), (key184, 2)]

def row1465 : Integer.Sparse Key := [(key1, 6), (key4, -6), (key84, -6), (key148, 6), (key164, 6), (key184, -6)]

def row1466 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 8), (key164, -4), (key184, -2)]

def row1467 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 8), (key164, -4), (key184, -2)]

def row1468 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 8), (key164, -4), (key184, -2)]

def row1469 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -8), (key164, 4), (key184, 2)]

def row1470 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -8), (key164, 4), (key184, 2)]

def row1471 : Integer.Sparse Key := [(key1, -2), (key4, 2), (key84, 2), (key148, -8), (key164, 4), (key184, 2)]

def row1472 : Integer.Sparse Key := [(key1, -6), (key4, 6), (key84, 6), (key148, -6), (key164, -6), (key184, 6)]

def row1473 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 2), (key164, 2), (key184, -2)]

def row1474 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 2), (key164, 2), (key184, -2)]

def row1475 : Integer.Sparse Key := [(key1, 2), (key4, -2), (key84, -2), (key148, 2), (key164, 2), (key184, -2)]

def row1479 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

def row1480 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

def row1481 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

def row1482 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

def row1483 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

def row1484 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, -1), (key2749, 1), (key2751, -2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, -1), (key2899, 1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, 1), (key2978, -1), (key2994, -1), (key3001, 1), (key3004, -1)]

def row1488 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1489 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1490 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1491 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1492 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1493 : Integer.Sparse Key := [(key2672, -1), (key2675, 1), (key2707, -1), (key2730, -2), (key2739, -3), (key2787, 1), (key2797, 3), (key2810, 1), (key2899, -1), (key2906, 2), (key2946, 2), (key2964, -1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1497 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

def row1498 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

def row1499 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

def row1500 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

def row1501 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

def row1502 : Integer.Sparse Key := [(key1294, 2), (key1314, 2), (key1335, -4), (key1389, -2), (key1453, 2), (key1544, -2), (key1653, 2), (key1770, 4), (key1786, -2), (key1811, -2)]

def row1506 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

def row1507 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

def row1508 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

def row1509 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

def row1510 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

def row1511 : Integer.Sparse Key := [(key1314, -2), (key1335, 2), (key1422, -2), (key1453, 2), (key1544, 2), (key1571, 2), (key1653, -4), (key1770, -2), (key1786, -2), (key1811, 4)]

def row1512 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

def row1513 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

def row1514 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

def row1515 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

def row1516 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

def row1517 : Integer.Sparse Key := [(key1294, -2), (key1314, -2), (key1335, 4), (key1389, 2), (key1453, -2), (key1544, 2), (key1653, -2), (key1770, -4), (key1786, 2), (key1811, 2)]

def row1518 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

def row1519 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

def row1520 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

def row1521 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

def row1522 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

def row1523 : Integer.Sparse Key := [(key1314, 2), (key1335, -2), (key1422, 2), (key1453, -2), (key1544, -2), (key1571, -2), (key1653, 4), (key1770, 2), (key1786, 2), (key1811, -4)]

def row1527 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1528 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1529 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1530 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1531 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1532 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1536 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1537 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1538 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1539 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1540 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1541 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1542 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1543 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1544 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1545 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1546 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1547 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1548 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1549 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1550 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1551 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1552 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1553 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1557 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

def row1558 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

def row1559 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

def row1560 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

def row1561 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

def row1562 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

def row1566 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

def row1567 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

def row1568 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

def row1569 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

def row1570 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

def row1571 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

def row1572 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

def row1573 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

def row1574 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

def row1575 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

def row1576 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

def row1577 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

def row1578 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

def row1579 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

def row1580 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

def row1581 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

def row1582 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

def row1583 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

def row1587 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

def row1588 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

def row1589 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

def row1590 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

def row1591 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

def row1592 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

def row1596 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

def row1597 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

def row1598 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

def row1599 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

def row1600 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

def row1601 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

def row1602 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

def row1603 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

def row1604 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

def row1605 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

def row1606 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

def row1607 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

def row1608 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

def row1609 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

def row1610 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

def row1611 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

def row1612 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

def row1613 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

def row1617 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

def row1618 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

def row1619 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

def row1620 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

def row1621 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

def row1622 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

def row1626 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

def row1627 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

def row1628 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

def row1629 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

def row1630 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

def row1631 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

def row1632 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

def row1633 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

def row1634 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

def row1635 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

def row1636 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

def row1637 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

def row1638 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

def row1639 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

def row1640 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

def row1641 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

def row1642 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

def row1643 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

def row1647 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

def row1648 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

def row1649 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

def row1650 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

def row1651 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

def row1652 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

def row1656 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

def row1657 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

def row1658 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

def row1659 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

def row1660 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

def row1661 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

def row1662 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

def row1663 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1664 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

def row1665 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

def row1666 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

def row1667 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

def row1668 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

def row1669 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

def row1670 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

def row1671 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

def row1672 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

def row1673 : Integer.Sparse Key := [(key2686, -2), (key2693, 6), (key2719, -2), (key2822, -2), (key3051, 2), (key3055, -2), (key3057, -4), (key3074, 2), (key3077, 2), (key3078, -2), (key3112, 2), (key3116, 2), (key3117, -2)]

def row1677 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

def row1678 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

def row1679 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

def row1680 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

def row1681 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

def row1682 : Integer.Sparse Key := [(key1296, 1), (key1303, 1), (key1316, 1), (key1330, 1), (key1337, -2), (key1340, -1), (key1346, -1), (key1391, -1), (key1398, -1), (key1455, 1), (key1458, 1), (key1546, -1), (key1560, -1), (key1655, 1), (key1660, 1), (key1772, 2), (key1775, 1), (key1781, 1), (key1788, -1), (key1791, -1), (key1813, -1), (key1818, -1)]

def row1686 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

def row1687 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

def row1688 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

def row1689 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

def row1690 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

def row1691 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1337, 1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, -1), (key1668, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 2), (key1818, 1), (key1826, 1)]

def row1692 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

def row1693 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

def row1694 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

def row1695 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

def row1696 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

def row1697 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1316, -1), (key1330, -1), (key1337, 2), (key1340, 1), (key1346, 1), (key1391, 1), (key1398, 1), (key1455, -1), (key1458, -1), (key1546, 1), (key1560, 1), (key1655, -1), (key1660, -1), (key1772, -2), (key1775, -1), (key1781, -1), (key1788, 1), (key1791, 1), (key1813, 1), (key1818, 1)]

def row1698 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

def row1699 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

def row1700 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

def row1701 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

def row1702 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

def row1703 : Integer.Sparse Key := [(key1316, 1), (key1330, 1), (key1337, -1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, 1), (key1668, 1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -2), (key1818, -1), (key1826, -1)]

def row1707 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

def row1708 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

def row1709 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

def row1710 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

def row1711 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

def row1712 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -2), (key1075, 2), (key1111, -2), (key1154, 2), (key1192, 2), (key1198, 2), (key1211, -4)]

def row1716 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

def row1717 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

def row1718 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

def row1719 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

def row1720 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

def row1721 : Integer.Sparse Key := [(key998, -2), (key1005, 2), (key1033, -2), (key1040, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1192, -4), (key1198, 2), (key1211, 2)]

def row1722 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

def row1723 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

def row1724 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

def row1725 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

def row1726 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

def row1727 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, 2), (key1075, -2), (key1111, 2), (key1154, -2), (key1192, -2), (key1198, -2), (key1211, 4)]

def row1728 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

def row1729 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

def row1730 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

def row1731 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

def row1732 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

def row1733 : Integer.Sparse Key := [(key998, 2), (key1005, -2), (key1033, 2), (key1040, -2), (key1111, -4), (key1126, 2), (key1154, 2), (key1192, 4), (key1198, -2), (key1211, -2)]

def row1737 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

def row1738 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

def row1739 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

def row1740 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

def row1741 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

def row1742 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, 1), (key2915, 2), (key2940, 1), (key2946, 1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, -1), (key2999, 1), (key3004, -1)]

def row1746 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

def row1747 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

def row1748 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 2), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

def row1749 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 2), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

def row1750 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

def row1751 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, -1), (key2656, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, 1), (key2906, 1), (key2915, -3), (key2945, 1), (key2946, 1), (key2962, 1), (key2994, -1), (key3004, 2)]

def row1752 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1753 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1754 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1755 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1756 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1757 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, -1), (key2751, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, -1), (key2952, -2), (key2962, 1), (key2978, -2), (key2985, 1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row1758 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row1759 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row1760 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 2), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -2), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row1761 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 2), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -2), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row1762 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row1763 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2655, 1), (key2656, -1), (key2672, 1), (key2675, -1), (key2749, 1), (key2751, -1), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, 1), (key2945, -1), (key2952, 1), (key2962, -1), (key2999, 1), (key3001, 1), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5148 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5149 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5150 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5151 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5152 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5153 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5154 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5155 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5156 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5157 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5158 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5159 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5160 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5161 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5162 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2858, 2), (key2868, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5163 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5164 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5165 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2858, 2), (key2868, -2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5166 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2858, 2), (key2868, -2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5167 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5168 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5169 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2858, 2), (key2868, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5170 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5171 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5172 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -2), (key2704, 1), (key2757, 1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3011, 1), (key3021, 1), (key3022, -1)]

def row5173 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -2), (key2704, 1), (key2757, 1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3011, 1), (key3021, 1), (key3022, -1)]

def row5174 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3009, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5175 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3009, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5176 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2638, 1), (key2657, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 2), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5177 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2638, 1), (key2657, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 2), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5178 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5179 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5180 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5181 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5182 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5183 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5184 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2918, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5185 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2918, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5186 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3009, 1), (key3021, 1), (key3022, -1)]

def row5187 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3009, 1), (key3021, 1), (key3022, -1)]

def row5188 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5189 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5190 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5191 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5192 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5193 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5194 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5195 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5196 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5197 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5198 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5199 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5200 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5201 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5202 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5203 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5204 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5205 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5206 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5207 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5208 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5209 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5210 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5211 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5212 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5213 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5214 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5215 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5216 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5217 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5218 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5219 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5220 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5221 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5222 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5223 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5224 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5225 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5226 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5227 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5228 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5229 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5230 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -2), (key277, -2), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5231 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5232 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5233 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -4), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5234 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -4), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5235 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5236 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5237 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -2), (key277, -2), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5238 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5239 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5240 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5241 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5242 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 2), (key445, 2), (key453, -2), (key657, 2), (key658, -2), (key661, -2), (key662, 2)]

def row5243 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

def row5244 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

def row5245 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 4), (key445, 2), (key453, -2), (key658, -2), (key661, -2), (key662, 2)]

def row5246 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 4), (key445, 2), (key453, -2), (key658, -2), (key661, -2), (key662, 2)]

def row5247 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5248 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

def row5249 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 2), (key445, 2), (key453, -2), (key657, 2), (key658, -2), (key661, -2), (key662, 2)]

def row5250 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5251 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5252 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -2), (key321, 1), (key347, 1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key421, -1), (key487, -1), (key488, 1), (key655, -1), (key657, 1), (key660, 1), (key661, -1)]

def row5253 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -2), (key321, 1), (key347, 1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key421, -1), (key487, -1), (key488, 1), (key655, -1), (key657, 1), (key660, 1), (key661, -1)]

def row5254 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key656, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5255 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key656, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5256 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key263, 1), (key277, -1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 2), (key347, -1), (key385, 2), (key390, -1), (key400, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5257 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key263, 1), (key277, -1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 2), (key347, -1), (key385, 2), (key390, -1), (key400, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5258 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5259 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5260 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5261 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5262 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 1), (key321, -2), (key331, 1), (key347, -1), (key385, 1), (key390, -1), (key400, 1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5263 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 1), (key321, -2), (key331, 1), (key347, -1), (key385, 1), (key390, -1), (key400, 1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5264 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key347, -1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -1), (key487, -1), (key489, 1), (key657, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5265 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key347, -1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -1), (key487, -1), (key489, 1), (key657, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5266 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key655, -1), (key656, 1), (key660, 1), (key661, -1)]

def row5267 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key655, -1), (key656, 1), (key660, 1), (key661, -1)]

def row5268 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5269 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5270 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5271 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5272 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5273 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5274 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5275 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5276 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5277 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5278 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5279 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5280 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5281 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5282 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5283 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5284 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5285 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5286 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5287 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5288 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5289 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5290 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5291 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5292 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5293 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5294 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5295 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5296 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5297 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5298 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5299 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5300 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5301 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5302 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5303 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5304 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5305 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5306 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5307 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5308 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5309 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5310 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5311 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5312 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5313 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5314 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5315 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5316 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5317 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5318 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5319 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5320 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5321 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5322 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5323 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5324 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5325 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5326 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5327 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5328 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5329 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5330 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5331 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5332 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5333 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5334 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5335 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5336 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5337 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5338 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5339 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5340 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5341 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5342 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5343 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5344 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5345 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5346 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5347 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5348 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5349 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5350 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5351 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5352 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5353 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5354 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5355 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5356 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5357 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5358 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5359 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5360 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5361 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5362 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 2), (key2856, 2), (key2866, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5363 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5364 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5365 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 4), (key2856, 2), (key2866, -2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5366 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 4), (key2856, 2), (key2866, -2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5367 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5368 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5369 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 2), (key2856, 2), (key2866, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5370 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5371 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5372 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -2), (key2701, 1), (key2745, 1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2947, 1), (key2971, 1), (key2974, -1)]

def row5373 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -2), (key2701, 1), (key2745, 1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2947, 1), (key2971, 1), (key2974, -1)]

def row5374 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2941, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5375 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2941, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5376 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2636, 1), (key2645, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 2), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5377 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2636, 1), (key2645, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 2), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5378 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5379 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5380 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5381 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5382 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2790, 1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5383 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2790, 1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5384 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2892, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5385 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2892, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5386 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2941, 1), (key2971, 1), (key2974, -1)]

def row5387 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2941, 1), (key2971, 1), (key2974, -1)]

def row5388 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1125, -4), (key1130, 4), (key1152, 4), (key1159, -4)]

def row5389 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5390 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5391 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5392 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5393 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1125, -4), (key1130, 4), (key1152, 4), (key1159, -4)]

def row5394 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5395 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5396 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5397 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5398 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5399 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5400 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5401 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5402 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5403 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5404 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5405 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5406 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5407 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5408 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5409 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5410 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5411 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5412 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5413 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5414 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5415 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5416 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5417 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5418 : Integer.Sparse Key := [(key25, -4), (key27, 4), (key37, 4), (key40, -4), (key50, 4), (key52, -4), (key76, -4), (key81, 4), (key117, -4), (key120, 4), (key139, 4), (key144, -4)]

def row5419 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5420 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5421 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5422 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5423 : Integer.Sparse Key := [(key25, -4), (key27, 4), (key37, 4), (key40, -4), (key50, 4), (key52, -4), (key76, -4), (key81, 4), (key117, -4), (key120, 4), (key139, 4), (key144, -4)]

def row5424 : Integer.Sparse Key := [(key37, -2), (key40, 2), (key76, 2), (key81, -2), (key117, -2), (key139, 2), (key197, 2), (key201, -2), (key210, 2), (key213, -2), (key379, -2), (key382, 2), (key464, 4), (key466, -2), (key483, -2), (key590, -4), (key592, 2), (key609, 2)]

def row5425 : Integer.Sparse Key := [(key37, 1), (key40, -1), (key76, -1), (key81, 1), (key117, 1), (key139, -1), (key197, -1), (key201, 1), (key210, -1), (key213, 1), (key379, 1), (key382, -1), (key464, -2), (key466, 1), (key483, 1), (key590, 2), (key592, -1), (key609, -1)]

def row5426 : Integer.Sparse Key := [(key37, 1), (key40, -1), (key76, -1), (key81, 1), (key117, 1), (key139, -1), (key197, -1), (key201, 1), (key210, -1), (key213, 1), (key379, 1), (key382, -1), (key464, -2), (key466, 1), (key483, 1), (key590, 2), (key592, -1), (key609, -1)]

def row5427 : Integer.Sparse Key := [(key37, -2), (key40, 2), (key76, 2), (key81, -2), (key210, 2), (key213, -2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key590, -2), (key592, 2)]

def row5428 : Integer.Sparse Key := [(key40, -1), (key81, 1), (key210, -1), (key213, 1), (key215, 1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key590, 1), (key592, -1)]

def row5429 : Integer.Sparse Key := [(key40, -1), (key81, 1), (key210, -1), (key213, 1), (key215, 1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key590, 1), (key592, -1)]

def row5430 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, -1), (key76, -1), (key210, -2), (key213, 1), (key217, -1), (key379, 2), (key382, -1), (key464, -1), (key466, 1), (key567, 1), (key590, 1), (key592, -1)]

def row5431 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, -1), (key76, -1), (key210, -2), (key213, 1), (key217, -1), (key379, 2), (key382, -1), (key464, -1), (key466, 1), (key567, 1), (key590, 1), (key592, -1)]

def row5432 : Integer.Sparse Key := [(key25, -1), (key50, 1), (key117, 1), (key139, -1), (key213, 1), (key215, 1), (key217, -1), (key382, -1), (key464, -2), (key466, 1), (key565, -1), (key567, 1), (key590, 2), (key592, -1)]

def row5433 : Integer.Sparse Key := [(key25, -1), (key50, 1), (key117, 1), (key139, -1), (key213, 1), (key215, 1), (key217, -1), (key382, -1), (key464, -2), (key466, 1), (key565, -1), (key567, 1), (key590, 2), (key592, -1)]

def row5434 : Integer.Sparse Key := [(key37, -1), (key76, 1), (key117, -1), (key139, 1), (key210, 2), (key213, -2), (key215, -1), (key217, 2), (key379, -2), (key382, 2), (key464, 3), (key466, -2), (key565, 1), (key567, -2), (key590, -3), (key592, 2)]

def row5435 : Integer.Sparse Key := [(key37, -1), (key76, 1), (key117, -1), (key139, 1), (key210, 2), (key213, -2), (key215, -1), (key217, 2), (key379, -2), (key382, 2), (key464, 3), (key466, -2), (key565, 1), (key567, -2), (key590, -3), (key592, 2)]

def row5436 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5437 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5438 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5439 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5440 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5441 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5442 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5443 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5444 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5445 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5446 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5447 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5448 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, 4), (key1042, -4), (key1073, -4), (key1077, 4), (key1125, -4), (key1128, 4), (key1152, 4), (key1156, -4)]

def row5449 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5450 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5451 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5452 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5453 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, 4), (key1042, -4), (key1073, -4), (key1077, 4), (key1125, -4), (key1128, 4), (key1152, 4), (key1156, -4)]

def row5454 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5455 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5456 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5457 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5458 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5459 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5460 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5461 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5462 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5463 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5464 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5465 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5466 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5467 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5468 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5469 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5470 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5471 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5472 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5473 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5474 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5475 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5476 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5477 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5478 : Integer.Sparse Key := [(key10, -4), (key13, 8), (key15, -4), (key93, 4), (key96, -4), (key158, -4), (key163, 4), (key169, -4), (key170, 4), (key189, 4), (key192, -4)]

def row5479 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5480 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5481 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5482 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5483 : Integer.Sparse Key := [(key10, -4), (key13, 8), (key15, -4), (key93, 4), (key96, -4), (key158, -4), (key163, 4), (key169, -4), (key170, 4), (key189, 4), (key192, -4)]

def row5484 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

def row5485 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -3), (key163, 3), (key169, 1), (key170, -1), (key189, 1), (key192, -1)]

def row5486 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -3), (key163, 3), (key169, 1), (key170, -1), (key189, 1), (key192, -1)]

def row5487 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 4), (key163, -6), (key170, 2), (key189, -2), (key192, 2)]

def row5488 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -2), (key163, 3), (key170, -1), (key189, 1), (key192, -1)]

def row5489 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -2), (key163, 3), (key170, -1), (key189, 1), (key192, -1)]

def row5490 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -6), (key163, 3), (key169, 4), (key170, -1), (key189, 1), (key192, -1)]

def row5491 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -6), (key163, 3), (key169, 4), (key170, -1), (key189, 1), (key192, -1)]

def row5492 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 3), (key169, -1), (key170, -1), (key189, 1), (key192, -1)]

def row5493 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 3), (key169, -1), (key170, -1), (key189, 1), (key192, -1)]

def row5494 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

def row5495 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

def row5496 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5497 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5498 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5499 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

def row5500 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

def row5501 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key163, -2), (key169, 4), (key170, -2), (key189, -2), (key192, 2)]

def row5502 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key163, -2), (key169, 4), (key170, -2), (key189, -2), (key192, 2)]

def row5503 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5504 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

def row5505 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5506 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5507 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5508 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2480, -4), (key2484, 4), (key2503, 4), (key2509, -4)]

def row5509 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5510 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5511 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5512 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5513 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2480, -4), (key2484, 4), (key2503, 4), (key2509, -4)]

def row5514 : Integer.Sparse Key := [(key2390, -2), (key2394, 2), (key2437, 2), (key2443, -2), (key2480, -2), (key2503, 2), (key2571, 2), (key2576, -2), (key2587, 2), (key2593, -2), (key2766, -2), (key2772, 2), (key2887, 4), (key2889, -2), (key2910, -2), (key2966, -4), (key2968, 2), (key2989, 2)]

def row5515 : Integer.Sparse Key := [(key2390, 1), (key2394, -1), (key2437, -1), (key2443, 1), (key2480, 1), (key2503, -1), (key2571, -1), (key2576, 1), (key2587, -1), (key2593, 1), (key2766, 1), (key2772, -1), (key2887, -2), (key2889, 1), (key2910, 1), (key2966, 2), (key2968, -1), (key2989, -1)]

def row5516 : Integer.Sparse Key := [(key2390, 1), (key2394, -1), (key2437, -1), (key2443, 1), (key2480, 1), (key2503, -1), (key2571, -1), (key2576, 1), (key2587, -1), (key2593, 1), (key2766, 1), (key2772, -1), (key2887, -2), (key2889, 1), (key2910, 1), (key2966, 2), (key2968, -1), (key2989, -1)]

def row5517 : Integer.Sparse Key := [(key2390, -2), (key2394, 2), (key2437, 2), (key2443, -2), (key2587, 2), (key2593, -2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2966, -2), (key2968, 2)]

def row5518 : Integer.Sparse Key := [(key2394, -1), (key2443, 1), (key2587, -1), (key2593, 1), (key2598, 1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2966, 1), (key2968, -1)]

def row5519 : Integer.Sparse Key := [(key2394, -1), (key2443, 1), (key2587, -1), (key2593, 1), (key2598, 1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2966, 1), (key2968, -1)]

def row5520 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1), (key2587, -2), (key2593, 1), (key2600, -1), (key2766, 2), (key2772, -1), (key2887, -1), (key2889, 1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5521 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1), (key2587, -2), (key2593, 1), (key2600, -1), (key2766, 2), (key2772, -1), (key2887, -1), (key2889, 1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5522 : Integer.Sparse Key := [(key2378, -1), (key2406, 1), (key2480, 1), (key2503, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2772, -1), (key2887, -2), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 2), (key2968, -1)]

def row5523 : Integer.Sparse Key := [(key2378, -1), (key2406, 1), (key2480, 1), (key2503, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2772, -1), (key2887, -2), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 2), (key2968, -1)]

def row5524 : Integer.Sparse Key := [(key2390, -1), (key2437, 1), (key2480, -1), (key2503, 1), (key2587, 2), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 3), (key2889, -2), (key2929, 1), (key2931, -2), (key2966, -3), (key2968, 2)]

def row5525 : Integer.Sparse Key := [(key2390, -1), (key2437, 1), (key2480, -1), (key2503, 1), (key2587, 2), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 3), (key2889, -2), (key2929, 1), (key2931, -2), (key2966, -3), (key2968, 2)]

def row5526 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5527 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5528 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5529 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5530 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5531 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5532 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5533 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5534 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5535 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5536 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5537 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5538 : Integer.Sparse Key := [(key1256, -4), (key1261, 4), (key1265, 4), (key1268, -4), (key1531, 4), (key1536, -4), (key1648, -4), (key1651, 4), (key1765, -4), (key1768, 4), (key1806, 4), (key1809, -4)]

def row5539 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5540 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5541 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5542 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5543 : Integer.Sparse Key := [(key1256, -4), (key1261, 4), (key1265, 4), (key1268, -4), (key1531, 4), (key1536, -4), (key1648, -4), (key1651, 4), (key1765, -4), (key1768, 4), (key1806, 4), (key1809, -4)]

def row5544 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5545 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5546 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5547 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5548 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5549 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5550 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5551 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5552 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5553 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5554 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5555 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5556 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5557 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5558 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5559 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5560 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5561 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5562 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5563 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5564 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5565 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5566 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5567 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5568 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, 4), (key2409, -4), (key2437, -4), (key2440, 4), (key2480, -4), (key2482, 4), (key2503, 4), (key2506, -4)]

def row5569 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5570 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5571 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5572 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5573 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, 4), (key2409, -4), (key2437, -4), (key2440, 4), (key2480, -4), (key2482, 4), (key2503, 4), (key2506, -4)]

def row5574 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5575 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5576 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5577 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5578 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5579 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5580 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5581 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5582 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5583 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5584 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5585 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5586 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5587 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5588 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5589 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5590 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5591 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5592 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5593 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5594 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5595 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5596 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5597 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5598 : Integer.Sparse Key := [(key982, -4), (key986, 8), (key988, -4), (key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row5599 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5600 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5601 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5602 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5603 : Integer.Sparse Key := [(key982, -4), (key986, 8), (key988, -4), (key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row5604 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5605 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5606 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5607 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5608 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5609 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5610 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5611 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5612 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5613 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5614 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5615 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5616 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5617 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5618 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5619 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5620 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5621 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5622 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5623 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5624 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5625 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5626 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5627 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5628 : Integer.Sparse Key := [(key2362, -4), (key2365, 8), (key2367, -4), (key2457, 4), (key2460, -4), (key2521, -4), (key2525, 4), (key2532, -4), (key2533, 4), (key2562, 4), (key2564, -4)]

def row5629 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5630 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5631 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5632 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5633 : Integer.Sparse Key := [(key2362, -4), (key2365, 8), (key2367, -4), (key2457, 4), (key2460, -4), (key2521, -4), (key2525, 4), (key2532, -4), (key2533, 4), (key2562, 4), (key2564, -4)]

def row5634 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5635 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -3), (key2525, 3), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5636 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -3), (key2525, 3), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5637 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -6), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5638 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -2), (key2525, 3), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5639 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -2), (key2525, 3), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5640 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -6), (key2525, 3), (key2532, 4), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5641 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -6), (key2525, 3), (key2532, 4), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5642 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 3), (key2532, -1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5643 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 3), (key2532, -1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5644 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5645 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5646 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5647 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5648 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5649 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5650 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5651 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2525, -2), (key2532, 4), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5652 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2525, -2), (key2532, 4), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5653 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5654 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5655 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5656 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5657 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5658 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2809, 2), (key2829, -4), (key2835, 2), (key2860, -2), (key2870, 2), (key3012, -2), (key3017, 2), (key3023, 2), (key3026, -2)]

def row5659 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2860, 1), (key2870, -1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row5660 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2860, 1), (key2870, -1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row5661 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 2), (key2829, -4), (key2831, -2), (key2835, 2), (key2860, -2), (key2870, 2), (key3017, 2), (key3023, 2), (key3026, -2)]

def row5662 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2621, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2829, 1), (key2831, 1), (key2835, -1), (key2860, 1), (key2870, -1), (key2948, 1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5663 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2621, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2829, 1), (key2831, 1), (key2835, -1), (key2860, 1), (key2870, -1), (key2948, 1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5664 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5665 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5666 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5667 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5668 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2618, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -2), (key2831, -2), (key2860, -2), (key2870, 2), (key2948, -2), (key2950, 2), (key2960, 2), (key3023, 2), (key3026, -2)]

def row5669 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2618, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -2), (key2831, -2), (key2860, -2), (key2870, 2), (key2948, -2), (key2950, 2), (key2960, 2), (key3023, 2), (key3026, -2)]

def row5670 : Integer.Sparse Key := [(key2628, 2), (key2640, -2), (key2641, -2), (key2660, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2758, -2), (key2782, -2), (key2794, -2), (key2795, 2), (key2805, -2), (key2829, 2), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3010, 2), (key3017, -2)]

def row5671 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2758, 1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, 1)]

def row5672 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2758, 1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, 1)]

def row5673 : Integer.Sparse Key := [(key2628, 2), (key2640, -2), (key2641, -2), (key2660, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2735, -2), (key2747, 2), (key2758, -2), (key2782, -2), (key2795, 2), (key2805, -2), (key2829, 2), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3017, -2)]

def row5674 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2660, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2758, 1), (key2782, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5675 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2660, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2758, 1), (key2782, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5676 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2667, 1), (key2671, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5677 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2667, 1), (key2671, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5678 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2667, -1), (key2671, 1), (key2702, -1), (key2728, 1), (key2747, -1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5679 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2667, -1), (key2671, 1), (key2702, -1), (key2728, 1), (key2747, -1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5680 : Integer.Sparse Key := [(key2628, 2), (key2640, -1), (key2641, -2), (key2646, -1), (key2653, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2735, -1), (key2747, 2), (key2782, -2), (key2794, -1), (key2795, 2), (key2805, -2), (key2829, 1), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2936, 1), (key2943, -2), (key2948, 1), (key2960, -2), (key2972, -4), (key2976, 2), (key2983, 2)]

def row5681 : Integer.Sparse Key := [(key2628, 2), (key2640, -1), (key2641, -2), (key2646, -1), (key2653, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2735, -1), (key2747, 2), (key2782, -2), (key2794, -1), (key2795, 2), (key2805, -2), (key2829, 1), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2936, 1), (key2943, -2), (key2948, 1), (key2960, -2), (key2972, -4), (key2976, 2), (key2983, 2)]

def row5682 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5683 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5684 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5685 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5686 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5687 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5688 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5689 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5690 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5691 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5692 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5693 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5694 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5695 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5696 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5697 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5698 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5699 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5700 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5701 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5702 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5703 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5704 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5705 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5706 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5707 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5708 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5709 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5710 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5711 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5712 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5713 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5714 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5715 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5716 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5717 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5718 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5719 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5720 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5721 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5722 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5723 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5724 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5725 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5726 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5727 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5728 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5729 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5730 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5731 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5732 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5733 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5734 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5735 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5736 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5737 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5738 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5739 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5740 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5741 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5742 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5743 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5744 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5745 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5746 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5747 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5748 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5749 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5750 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5751 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5752 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5753 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5754 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5755 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5756 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5757 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5758 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5759 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5760 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5761 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5762 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5763 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5764 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5765 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5766 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5767 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5768 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5769 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5770 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5771 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5772 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5773 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5774 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5775 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5776 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5777 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5778 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5779 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5780 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5781 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5782 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5783 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5784 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5785 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5786 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5787 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5788 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5789 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5790 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5791 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5792 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5793 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5794 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5795 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5796 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5797 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5798 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5799 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5800 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5801 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5802 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5803 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5804 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5805 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5806 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5807 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5808 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5809 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5810 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5811 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5812 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5813 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5814 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5815 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5816 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5817 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5818 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5819 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5820 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5821 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5822 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5823 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5824 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5825 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5826 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5827 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5828 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5829 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5830 : Integer.Sparse Key := [(key2379, 2), (key2393, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2595, -2), (key2603, 2), (key2771, 2), (key2774, -2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, 2), (key2991, -2), (key2993, -2), (key3003, 4)]

def row5831 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2933, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5832 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2933, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5833 : Integer.Sparse Key := [(key2407, 2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2774, -2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, 2), (key2991, -2), (key2993, -2), (key3003, 4)]

def row5834 : Integer.Sparse Key := [(key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5835 : Integer.Sparse Key := [(key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5836 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2441, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, 2), (key2555, -1), (key2565, -2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, -1), (key2914, 1), (key2933, 2), (key2934, -1), (key2991, 2), (key2993, 1)]

def row5837 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2441, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, 2), (key2555, -1), (key2565, -2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, -1), (key2914, 1), (key2933, 2), (key2934, -1), (key2991, 2), (key2993, 1)]

def row5838 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, -1), (key2555, 2), (key2565, -2), (key2592, -1), (key2595, 1), (key2602, 2), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 2), (key2914, 1), (key2934, -1), (key2991, -1), (key2993, 1)]

def row5839 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, -1), (key2555, 2), (key2565, -2), (key2592, -1), (key2595, 1), (key2602, 2), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 2), (key2914, 1), (key2934, -1), (key2991, -1), (key2993, 1)]

def row5840 : Integer.Sparse Key := [(key2379, 2), (key2393, -2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2544, -2), (key2555, -2), (key2565, 4), (key2595, -2), (key2603, 2), (key2771, 2), (key2774, -2), (key2882, 4), (key2914, -2), (key2934, 2), (key2993, -2)]

def row5841 : Integer.Sparse Key := [(key2393, -2), (key2407, 2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2544, -2), (key2555, -2), (key2565, 4), (key2592, 2), (key2595, -2), (key2603, 2), (key2774, -2), (key2882, 4), (key2914, -2), (key2934, 2), (key2993, -2)]

def row5842 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

def row5843 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

def row5844 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2771, 2), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2933, -1), (key2970, 2), (key2991, -1)]

def row5845 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2771, 2), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2933, -1), (key2970, 2), (key2991, -1)]

def row5846 : Integer.Sparse Key := [(key2382, 2), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2602, 2), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2970, -1), (key2991, -1)]

def row5847 : Integer.Sparse Key := [(key2382, 2), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2602, 2), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2970, -1), (key2991, -1)]

def row5848 : Integer.Sparse Key := [(key2382, -1), (key2393, 2), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2592, -1), (key2595, 2), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2970, 2), (key2991, -1)]

def row5849 : Integer.Sparse Key := [(key2382, -1), (key2393, 2), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2592, -1), (key2595, 2), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2970, 2), (key2991, -1)]

def row5850 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2595, 2), (key2771, 2), (key2774, -1), (key2882, -1), (key2912, 2), (key2933, -1), (key2991, -1)]

def row5851 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2595, 2), (key2771, 2), (key2774, -1), (key2882, -1), (key2912, 2), (key2933, -1), (key2991, -1)]

def row5852 : Integer.Sparse Key := [(key2379, -1), (key2382, 2), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -4), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2595, -1), (key2771, -1), (key2774, -1), (key2882, 2)]

def row5853 : Integer.Sparse Key := [(key2382, 2), (key2393, 1), (key2395, -1), (key2407, -1), (key2410, 2), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -4), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2774, -1), (key2882, 2)]

def row5854 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, -2), (key2545, 1), (key2555, 1), (key2557, -2), (key2565, 1), (key2592, -1), (key2848, -1)]

def row5855 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, -2), (key2545, 1), (key2555, 1), (key2557, -2), (key2565, 1), (key2592, -1), (key2848, -1)]

def row5856 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2771, -1)]

def row5857 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2592, -1)]

def row5858 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5859 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, 1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5860 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, 1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5861 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2915, -2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5862 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2915, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5863 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2915, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5864 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, 2), (key2899, -1), (key2915, 1), (key2952, -4), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5865 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, 2), (key2899, -1), (key2915, 1), (key2952, -4), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5866 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -3), (key2899, -1), (key2915, 1), (key2952, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5867 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -3), (key2899, -1), (key2915, 1), (key2952, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5868 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5869 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5870 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5871 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5872 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5873 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -4), (key2751, 2), (key2797, 2), (key2915, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5874 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2751, -1), (key2797, -1), (key2915, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5875 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2751, -1), (key2797, -1), (key2915, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5876 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, -2), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 4), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5877 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, -2), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 4), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5878 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 3), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5879 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 3), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5880 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5881 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5882 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2739, -1), (key2749, 2), (key2787, 1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5883 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2739, -1), (key2749, 2), (key2787, 1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5884 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2749, 1), (key2797, 1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5885 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2749, 1), (key2797, 1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5886 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2797, -1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5887 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2797, -1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5888 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5889 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5890 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2730, 1), (key2739, 1), (key2749, 1), (key2787, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5891 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2730, 1), (key2739, 1), (key2749, 1), (key2787, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5892 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -2), (key2749, 1), (key2797, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5893 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -2), (key2749, 1), (key2797, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5894 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5895 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5896 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5897 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5898 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5899 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5900 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5901 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5902 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5903 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5904 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5905 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5906 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5907 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5908 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5909 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5910 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5911 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5912 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5913 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5914 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5915 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5916 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5917 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5918 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5919 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5920 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5921 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5922 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5923 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5924 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5925 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5926 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5927 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5928 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5929 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5930 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5931 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5932 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5933 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5934 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5935 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5936 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5937 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5938 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5939 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5940 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5941 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5942 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5943 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5944 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5945 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5946 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5947 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5948 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5949 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5950 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5951 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5952 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5953 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5954 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5955 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5956 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5957 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5958 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5959 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5960 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5961 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5962 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5963 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5964 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5965 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5966 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5967 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5968 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5969 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5970 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5971 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5972 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5973 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5974 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5975 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5976 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5977 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5978 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5979 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5980 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5981 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5982 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5983 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5984 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5985 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5986 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5987 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5988 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5989 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5990 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5991 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5992 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row5993 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5994 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5995 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row5996 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row5997 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5998 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5999 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row6000 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6001 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6002 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6003 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6004 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6005 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6006 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6007 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6008 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6009 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6010 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6011 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6012 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6013 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6014 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6015 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6016 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6017 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6018 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6019 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6020 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6021 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6022 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6023 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6024 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6025 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6026 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6027 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6028 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6029 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6030 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6031 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6032 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6033 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6034 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6035 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6036 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6037 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6038 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6039 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6040 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6041 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6042 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6043 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6044 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6045 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6046 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6047 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6048 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6049 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6050 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6051 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6052 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6053 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6054 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6055 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6056 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6057 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6058 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6059 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6060 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6061 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6062 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6063 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6064 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6065 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6066 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6067 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6068 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6069 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6070 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6071 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6072 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6073 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6074 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6075 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6076 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6077 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6078 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6079 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6080 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6081 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6082 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6083 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6084 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6085 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6086 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6087 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6088 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6089 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6090 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6091 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6092 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6093 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6094 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6095 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6096 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6097 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6098 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6099 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6100 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6101 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6102 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6103 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6104 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6105 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6106 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6107 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6108 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6109 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6110 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6111 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6112 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6113 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6114 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6115 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6116 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6117 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6118 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6119 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6120 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6121 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6122 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6123 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6124 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6125 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6126 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6127 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6128 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6129 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6130 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6131 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6132 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6133 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6134 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6135 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6136 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6137 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6138 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6139 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6140 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -2), (key267, -2), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

def row6141 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6142 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6143 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -4), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6144 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -4), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

def row6145 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6146 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6147 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -2), (key267, -2), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

def row6148 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6149 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6150 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6151 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6152 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 2), (key442, 2), (key450, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row6153 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6154 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6155 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 4), (key442, 2), (key450, -2), (key583, -2), (key595, -2), (key601, 2)]

def row6156 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 4), (key442, 2), (key450, -2), (key583, -2), (key595, -2), (key601, 2)]

def row6157 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6158 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6159 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 2), (key442, 2), (key450, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row6160 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6161 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6162 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -2), (key319, 1), (key340, 1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key418, -1), (key467, -1), (key469, 1), (key568, -1), (key578, 1), (key593, 1), (key595, -1)]

def row6163 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -2), (key319, 1), (key340, 1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key418, -1), (key467, -1), (key469, 1), (key568, -1), (key578, 1), (key593, 1), (key595, -1)]

def row6164 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key572, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6165 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key572, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6166 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key260, 1), (key267, -1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 2), (key340, -1), (key385, 2), (key388, -1), (key397, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6167 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key260, 1), (key267, -1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 2), (key340, -1), (key385, 2), (key388, -1), (key397, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6168 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6169 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6170 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6278 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

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

def row7018 : Integer.Sparse Key := [(key2080, -4), (key2084, 4), (key2086, 4), (key2089, -4), (key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2280, -4), (key2283, 4), (key2288, 4), (key2291, -4)]

def row7019 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7020 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7021 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7022 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7023 : Integer.Sparse Key := [(key2080, -4), (key2084, 4), (key2086, 4), (key2089, -4), (key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2280, -4), (key2283, 4), (key2288, 4), (key2291, -4)]

def row7024 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7025 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7026 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7027 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7028 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7029 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7030 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7031 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7032 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7033 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7034 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7035 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7036 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7037 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7038 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7039 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7040 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7041 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7042 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7043 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7044 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7045 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7046 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7047 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7048 : Integer.Sparse Key := [(key739, -4), (key740, 4), (key744, 4), (key745, -4), (key819, 4), (key820, -4), (key826, -4), (key829, 4), (key903, -4), (key904, 4), (key909, 4), (key912, -4)]

def row7049 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7050 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7051 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7052 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7053 : Integer.Sparse Key := [(key739, -4), (key740, 4), (key744, 4), (key745, -4), (key819, 4), (key820, -4), (key826, -4), (key829, 4), (key903, -4), (key904, 4), (key909, 4), (key912, -4)]

def row7054 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7055 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7056 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7057 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7058 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7059 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7060 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7061 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7062 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7063 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7064 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7065 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7066 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7067 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7068 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7069 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7070 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7071 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7072 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7073 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7074 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7075 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7076 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7077 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7078 : Integer.Sparse Key := [(key2093, -4), (key2094, 4), (key2096, 4), (key2097, -4), (key2195, 4), (key2196, -4), (key2201, -4), (key2202, 4), (key2306, -4), (key2307, 4), (key2311, 4), (key2312, -4)]

def row7079 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7080 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7081 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7082 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7083 : Integer.Sparse Key := [(key2093, -4), (key2094, 4), (key2096, 4), (key2097, -4), (key2195, 4), (key2196, -4), (key2201, -4), (key2202, 4), (key2306, -4), (key2307, 4), (key2311, 4), (key2312, -4)]

def row7084 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7085 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7086 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7087 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7088 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7089 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7090 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7091 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7092 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7093 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7094 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7095 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7096 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7097 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7098 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7099 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7100 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7101 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7102 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7103 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7104 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7105 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7106 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7107 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7108 : Integer.Sparse Key := [(key717, -4), (key719, 8), (key720, -4), (key894, 4), (key896, -4), (key917, -4), (key920, 4), (key949, -4), (key950, 4), (key956, 4), (key958, -4)]

def row7109 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7110 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7111 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7112 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7113 : Integer.Sparse Key := [(key717, -4), (key719, 8), (key720, -4), (key894, 4), (key896, -4), (key917, -4), (key920, 4), (key949, -4), (key950, 4), (key956, 4), (key958, -4)]

def row7114 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7115 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7116 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7117 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7118 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7119 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7120 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7121 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7122 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7123 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7124 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7125 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7126 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7127 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7128 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7129 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7130 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7131 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7132 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7133 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7134 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7135 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7136 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7137 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7138 : Integer.Sparse Key := [(key2002, -4), (key2004, 8), (key2005, -4), (key2271, 4), (key2273, -4), (key2295, -4), (key2297, 4), (key2325, -4), (key2326, 4), (key2337, 4), (key2338, -4)]

def row7139 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7140 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7141 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7142 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7143 : Integer.Sparse Key := [(key2002, -4), (key2004, 8), (key2005, -4), (key2271, 4), (key2273, -4), (key2295, -4), (key2297, 4), (key2325, -4), (key2326, 4), (key2337, 4), (key2338, -4)]

def row7144 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7145 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7146 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7147 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7148 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7149 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7150 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7151 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7152 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7153 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7154 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7155 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7156 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7157 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7158 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7159 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7160 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7161 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7162 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7163 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7164 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7165 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7166 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7167 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7168 : Integer.Sparse Key := [(key2178, -4), (key2180, 4), (key2190, 4), (key2192, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2331, 4), (key2335, 4), (key2339, -4)]

def row7169 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7170 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7171 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7172 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7173 : Integer.Sparse Key := [(key2178, -4), (key2180, 4), (key2190, 4), (key2192, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2331, 4), (key2335, 4), (key2339, -4)]

def row7174 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7175 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7176 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7177 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7178 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7179 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7180 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7181 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7182 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7183 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7184 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7185 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7186 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7187 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7188 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7189 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7190 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7191 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7192 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7193 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7194 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7195 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7196 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7197 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7198 : Integer.Sparse Key := [(key748, -4), (key749, 4), (key752, 4), (key753, -4), (key832, 4), (key833, -4), (key841, -4), (key842, 4), (key929, -4), (key930, 4), (key936, 4), (key937, -4)]

def row7199 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7200 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7201 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7202 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7203 : Integer.Sparse Key := [(key748, -4), (key749, 4), (key752, 4), (key753, -4), (key832, 4), (key833, -4), (key841, -4), (key842, 4), (key929, -4), (key930, 4), (key936, 4), (key937, -4)]

def row7204 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7205 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7206 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7207 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7208 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7209 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7210 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7211 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7212 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7213 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7214 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7215 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7216 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7217 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7218 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7219 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7220 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7221 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7222 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7223 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7224 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7225 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

def row7226 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7227 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

def row7228 : Integer.Sparse Key := [(key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2277, -4), (key2283, 4), (key2288, 4), (key2296, -4), (key2342, 4), (key2344, -4), (key2348, -4), (key2350, 4)]

def row7229 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7230 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7231 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7232 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7233 : Integer.Sparse Key := [(key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2277, -4), (key2283, 4), (key2288, 4), (key2296, -4), (key2342, 4), (key2344, -4), (key2348, -4), (key2350, 4)]

def row7234 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7235 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7236 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7237 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7238 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7239 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7240 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7241 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7242 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7243 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7244 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7245 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7246 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7247 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7248 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7249 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7250 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7251 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7252 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7253 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7254 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7255 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

def row7256 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7257 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7258 : Integer.Sparse Key := [(key2081, -4), (key2083, 4), (key2088, 4), (key2090, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2332, 4), (key2334, 4), (key2339, -4)]

def row7259 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7260 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7261 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7262 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7263 : Integer.Sparse Key := [(key2081, -4), (key2083, 4), (key2088, 4), (key2090, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2332, 4), (key2334, 4), (key2339, -4)]

def row7264 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7265 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7266 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7267 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7268 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7269 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7270 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7271 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7272 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7273 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7274 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7275 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7276 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7277 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7278 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7279 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7280 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7281 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7282 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7283 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7284 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7285 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7286 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7287 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7288 : Integer.Sparse Key := [(key822, 4), (key823, -4), (key827, -4), (key828, 4), (key906, -4), (key910, 4), (key911, 4), (key918, -4), (key952, 4), (key953, -8), (key957, 4)]

def row7289 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7290 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7291 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7292 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7293 : Integer.Sparse Key := [(key822, 4), (key823, -4), (key827, -4), (key828, 4), (key906, -4), (key910, 4), (key911, 4), (key918, -4), (key952, 4), (key953, -8), (key957, 4)]

def row7294 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7295 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

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

def row7296 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7297 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7298 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7299 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7300 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7301 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7302 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7303 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7304 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7305 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7306 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7307 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7308 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7309 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7310 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7311 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7312 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7313 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7314 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7315 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7316 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7317 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7318 : Integer.Sparse Key := [(key781, -4), (key784, 8), (key786, -4), (key806, 4), (key809, -4), (key814, -4), (key816, 4), (key822, -4), (key823, 4), (key827, 4), (key828, -4)]

def row7319 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7320 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7321 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7322 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7323 : Integer.Sparse Key := [(key781, -4), (key784, 8), (key786, -4), (key806, 4), (key809, -4), (key814, -4), (key816, 4), (key822, -4), (key823, 4), (key827, 4), (key828, -4)]

def row7324 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

def row7325 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -3), (key816, 3), (key822, 1), (key823, -1), (key827, 1), (key828, -1)]

def row7326 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -3), (key816, 3), (key822, 1), (key823, -1), (key827, 1), (key828, -1)]

def row7327 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 4), (key816, -6), (key823, 2), (key827, -2), (key828, 2)]

def row7328 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -2), (key816, 3), (key823, -1), (key827, 1), (key828, -1)]

def row7329 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -2), (key816, 3), (key823, -1), (key827, 1), (key828, -1)]

def row7330 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -6), (key816, 3), (key822, 4), (key823, -1), (key827, 1), (key828, -1)]

def row7331 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -6), (key816, 3), (key822, 4), (key823, -1), (key827, 1), (key828, -1)]

def row7332 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 3), (key822, -1), (key823, -1), (key827, 1), (key828, -1)]

def row7333 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 3), (key822, -1), (key823, -1), (key827, 1), (key828, -1)]

def row7334 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

def row7335 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

def row7336 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

def row7337 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

def row7338 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7339 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7340 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7341 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key816, -2), (key822, 4), (key823, -2), (key827, -2), (key828, 2)]

def row7342 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key816, -2), (key822, 4), (key823, -2), (key827, -2), (key828, 2)]

def row7343 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7344 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7345 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7346 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

def row7347 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

end MUB6.Certificate.GramRows

end OAI
end


