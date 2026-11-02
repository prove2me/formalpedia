-- Prove2me | Definitions.Def_OAIQ106D143
-- name    : OAIQ106D143
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:51:57.596186+00:00
-- url     : https://prove2.me/theorems/ba712cce-9618-4dd5-ba7c-4d6200d1bf0d
-- title:
--   Definitions bundle OAIQ106D143 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 856 declarations of OpenAI's Lean: 856 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block2.entries`, `OAI.MUB6.Certificate.GramEntries.Block2.entry1_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry1_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entry8_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry8_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry8_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entry8_8`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms3`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms4`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms5`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms6`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms7`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms8`, `OAI.MUB6.Certificate.GramFunctions.Block1.terms9`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms0`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms10`, `OAI.MUB6.Certificate.GramRows.row1000`, `OAI.MUB6.Certificate.GramRows.row1001`, `OAI.MUB6.Certificate.GramRows.row1002`, `OAI.MUB6.Certificate.GramRows.row1003`, `OAI.MUB6.Certificate.GramRows.row1004`, `OAI.MUB6.Certificate.GramRows.row1005`, `OAI.MUB6.Certificate.GramRows.row1006`, `OAI.MUB6.Certificate.GramRows.row1007`, `OAI.MUB6.Certificate.GramRows.row1008`, `OAI.MUB6.Certificate.GramRows.row1009`, `OAI.MUB6.Certificate.GramRows.row1010`, `OAI.MUB6.Certificate.GramRows.row1011`, `OAI.MUB6.Certificate.GramRows.row1012`, `OAI.MUB6.Certificate.GramRows.row1013`, `OAI.MUB6.Certificate.GramRows.row1014`, `OAI.MUB6.Certificate.GramRows.row1015`, `OAI.MUB6.Certificate.GramRows.row1016` and 816 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block2Data`, `MutuallyUnbiased_GramFunctions_Block1`, `MutuallyUnbiased_GramFunctions_Block2`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block20`, `MutuallyUnbiased_GramRows_Block25`, `MutuallyUnbiased_GramRows_Block26`, `MutuallyUnbiased_GramRows_Block27`, `MutuallyUnbiased_GramRows_Block28`, `MutuallyUnbiased_GramRows_Block29`, `MutuallyUnbiased_GramRows_Block30`, `MutuallyUnbiased_GramRows_Block31`, `MutuallyUnbiased_GramRows_Block32`, `MutuallyUnbiased_GramRows_Block33`, `MutuallyUnbiased_GramRows_Block34`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block80`.
--
--   **Imports.** It imports the bundles `OAIQ106D073`, `OAIQ106D076`, `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D086` and `OAIQ106D087` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D198`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D073
import Definitions.Def_OAIQ106D076
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization

def entry1_0 : Integer.Sparse Key := [(key1291, 64), (key1299, -64), (key1311, -64), (key1319, 96), (key1327, -32), (key1352, -32), (key1355, 32), (key1386, -64), (key1394, 64), (key1419, 64), (key1427, -96), (key1445, 32), (key1473, 32), (key1481, -32), (key1541, 64), (key1549, -96), (key1557, 32), (key1568, -64), (key1576, 96), (key1594, -32), (key1684, -32), (key1690, 32), (key1897, 32), (key1900, -32), (key1904, -32), (key1912, 32), (key1921, 32), (key1927, -32)]

def entry1_1 : Integer.Sparse Key := [(key236, 64), (key241, -64), (key248, -64), (key253, 96), (key263, -52), (key277, -12), (key278, 32), (key302, -64), (key307, 64), (key316, 84), (key321, -144), (key331, 60), (key346, 56), (key347, -60), (key385, 44), (key390, -48), (key400, 8), (key406, -64), (key411, 96), (key421, -52), (key488, -32), (key489, 32), (key655, 4), (key656, -4), (key657, -12), (key658, 32), (key661, 32), (key662, -32)]

def entry5_1 : Integer.Sparse Key := [(key1296, -32), (key1303, 32), (key1316, 32), (key1330, -32), (key1340, -32), (key1346, 32), (key1391, 32), (key1398, -32), (key1424, 64), (key1448, -64), (key1455, -96), (key1458, 32), (key1467, 64), (key1546, -32), (key1560, 32), (key1573, -64), (key1597, 64), (key1655, 96), (key1660, -32), (key1668, -64), (key1775, 32), (key1781, -32), (key1788, 96), (key1791, -32), (key1799, -64), (key1813, -96), (key1818, 32), (key1826, 64)]

def entry6_0 : Integer.Sparse Key := [(key1292, 64), (key1298, -64), (key1312, -64), (key1318, 96), (key1326, -32), (key1351, -32), (key1354, 32), (key1387, -64), (key1393, 64), (key1420, 64), (key1426, -96), (key1444, 32), (key1472, 32), (key1480, -32), (key1542, 64), (key1548, -96), (key1556, 32), (key1569, -64), (key1575, 96), (key1593, -32), (key1683, -32), (key1689, 32), (key1896, 32), (key1899, -32), (key1903, -32), (key1911, 32), (key1920, 32), (key1926, -32)]

def entry6_1 : Integer.Sparse Key := [(key237, 64), (key240, -64), (key249, -64), (key252, 96), (key262, -32), (key268, -32), (key273, 32), (key303, -64), (key306, 64), (key317, 64), (key320, -96), (key330, 32), (key336, 32), (key342, -32), (key386, 64), (key389, -96), (key399, 32), (key407, -64), (key410, 96), (key420, -32), (key471, -32), (key477, 32), (key569, 32), (key574, -32), (key579, -32), (key585, 32), (key597, 32), (key603, -32)]

def entry6_2 : Integer.Sparse Key := [(key1291, 64), (key1295, -64), (key1311, -64), (key1315, 96), (key1324, -32), (key1336, -32), (key1343, 32), (key1386, -64), (key1390, 64), (key1419, 64), (key1423, -96), (key1442, 32), (key1454, 32), (key1464, -32), (key1541, 64), (key1545, -96), (key1554, 32), (key1568, -64), (key1572, 96), (key1591, -32), (key1657, -32), (key1665, 32), (key1771, 32), (key1778, -32), (key1787, -32), (key1796, 32), (key1815, 32), (key1823, -32)]

def entry6_4 : Integer.Sparse Key := [(key1256, 96), (key1260, -96), (key1265, -96), (key1267, 96), (key1531, -96), (key1535, 96), (key1648, 96), (key1650, -96), (key1765, 96), (key1767, -96), (key1806, -96), (key1808, 96)]

def entry6_5 : Integer.Sparse Key := [(key1296, -32), (key1302, 32), (key1316, 32), (key1329, -32), (key1339, -32), (key1345, 32), (key1391, 32), (key1397, -32), (key1424, 64), (key1447, -64), (key1455, -96), (key1457, 32), (key1466, 64), (key1546, -32), (key1559, 32), (key1573, -64), (key1596, 64), (key1655, 96), (key1659, -32), (key1667, -64), (key1774, 32), (key1780, -32), (key1788, 96), (key1790, -32), (key1798, -64), (key1813, -96), (key1817, 32), (key1825, 64)]

def entry7_6 : Integer.Sparse Key := [(key1292, 32), (key1298, -32), (key1312, -32), (key1326, 32), (key1351, 32), (key1354, -32), (key1387, -32), (key1393, 32), (key1420, 32), (key1426, -96), (key1444, 64), (key1472, 64), (key1480, -64), (key1542, 32), (key1556, -32), (key1569, -32), (key1575, 96), (key1593, -64), (key1681, -96), (key1683, 32), (key1689, 64), (key1896, -32), (key1899, 32), (key1903, -64), (key1911, 64), (key1918, 96), (key1920, -32), (key1926, -64)]

def entry8_1 : Integer.Sparse Key := [(key1296, 32), (key1303, -32), (key1316, 64), (key1330, -64), (key1337, -96), (key1340, 32), (key1346, 64), (key1391, -32), (key1398, 32), (key1424, 32), (key1448, -32), (key1458, -32), (key1467, 32), (key1546, -64), (key1560, 64), (key1573, -32), (key1597, 32), (key1655, 96), (key1660, -64), (key1668, -32), (key1772, 96), (key1775, -32), (key1781, -64), (key1791, 32), (key1799, -32), (key1813, -96), (key1818, 64), (key1826, 32)]

def entry8_5 : Integer.Sparse Key := [(key2617, 32), (key2620, -32), (key2633, -32), (key2643, 44), (key2650, 20), (key2655, -32), (key2672, 64), (key2675, -64), (key2707, -4), (key2730, 12), (key2739, -8), (key2749, -80), (key2751, 72), (key2787, -28), (key2797, 40), (key2810, -32), (key2833, 44), (key2899, 32), (key2906, 16), (key2915, -72), (key2940, 20), (key2945, -48), (key2946, 24), (key2952, 20), (key2962, -32), (key2978, 16), (key2985, 32), (key2994, -72), (key2999, -24), (key3001, -24), (key3004, 96)]

def entry8_6 : Integer.Sparse Key := [(key1296, 32), (key1302, -32), (key1316, 64), (key1329, -64), (key1337, -96), (key1339, 32), (key1345, 64), (key1391, -32), (key1397, 32), (key1424, 32), (key1447, -32), (key1457, -32), (key1466, 32), (key1546, -64), (key1559, 64), (key1573, -32), (key1596, 32), (key1655, 96), (key1659, -64), (key1667, -32), (key1772, 96), (key1774, -32), (key1780, -64), (key1790, 32), (key1798, -32), (key1813, -96), (key1817, 64), (key1825, 32)]

def entry8_8 : Integer.Sparse Key := [(key2617, 64), (key2620, -64), (key2633, 32), (key2643, -36), (key2650, -28), (key2655, -64), (key2656, 96), (key2672, 32), (key2675, -32), (key2707, -8), (key2730, 24), (key2739, 8), (key2749, -40), (key2787, -56), (key2797, 56), (key2810, -64), (key2833, 84), (key2899, 64), (key2906, 56), (key2915, -144), (key2940, 40), (key2945, -24), (key2952, 44), (key2962, -64), (key2978, 8), (key2985, -32), (key2999, -48), (key3004, 96)]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block1

def terms3 : Array TaggedTerm := #[
  ⟨0, ![1, -3, 0, 0, 0, 2], -2⟩,
  ⟨0, ![1, -3, 0, 0, 2, 0], -2⟩,
  ⟨0, ![1, -3, 0, 2, 0, 0], -2⟩,
  ⟨0, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨0, ![1, 0, -3, 0, 0, 2], 2⟩,
  ⟨0, ![1, 0, -3, 0, 2, 0], 2⟩,
  ⟨0, ![1, 0, -3, 2, 0, 0], 2⟩,
  ⟨0, ![1, 0, 2, -3, 0, 0], -2⟩,
  ⟨0, ![1, 0, 2, 0, -3, 0], -2⟩,
  ⟨0, ![1, 0, 2, 0, 0, -3], -2⟩,
  ⟨0, ![1, 2, -3, 0, 0, 0], -6⟩,
  ⟨0, ![1, 2, 0, -3, 0, 0], 2⟩,
  ⟨0, ![1, 2, 0, 0, -3, 0], 2⟩,
  ⟨0, ![1, 2, 0, 0, 0, -3], 2⟩
]

def terms4 : Array TaggedTerm := #[
  ⟨1, ![3, -2, -1, 0, 0, 0], -6⟩,
  ⟨1, ![3, -2, 0, -1, 0, 0], 2⟩,
  ⟨1, ![3, -2, 0, 0, -1, 0], 2⟩,
  ⟨1, ![3, -2, 0, 0, 0, -1], 2⟩,
  ⟨1, ![3, -1, -2, 0, 0, 0], 6⟩,
  ⟨1, ![3, -1, 0, -2, 0, 0], -2⟩,
  ⟨1, ![3, -1, 0, 0, -2, 0], -2⟩,
  ⟨1, ![3, -1, 0, 0, 0, -2], -2⟩,
  ⟨1, ![3, 0, -2, -1, 0, 0], -2⟩,
  ⟨1, ![3, 0, -2, 0, -1, 0], -2⟩,
  ⟨1, ![3, 0, -2, 0, 0, -1], -2⟩,
  ⟨1, ![3, 0, -1, -2, 0, 0], 2⟩,
  ⟨1, ![3, 0, -1, 0, -2, 0], 2⟩,
  ⟨1, ![3, 0, -1, 0, 0, -2], 2⟩
]

def terms5 : Array TaggedTerm := #[
  ⟨0, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨0, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨0, ![1, -1, 0, 0, -2, 2], -1⟩,
  ⟨0, ![1, -1, 0, 0, 2, -2], -1⟩,
  ⟨0, ![1, -1, 0, 2, -2, 0], -1⟩,
  ⟨0, ![1, -1, 0, 2, 0, -2], -1⟩,
  ⟨0, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨0, ![1, -1, 2, 0, -2, 0], 2⟩,
  ⟨0, ![1, -1, 2, 0, 0, -2], 2⟩,
  ⟨0, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨0, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨0, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨0, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨0, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨0, ![1, 0, -1, 2, 0, -2], 1⟩,
  ⟨0, ![1, 0, 2, -2, -1, 0], -1⟩,
  ⟨0, ![1, 0, 2, -2, 0, -1], -1⟩,
  ⟨0, ![1, 0, 2, -1, -2, 0], -1⟩,
  ⟨0, ![1, 0, 2, -1, 0, -2], -1⟩,
  ⟨0, ![1, 0, 2, 0, -2, -1], -1⟩,
  ⟨0, ![1, 0, 2, 0, -1, -2], -1⟩,
  ⟨0, ![1, 2, -1, -2, 0, 0], -2⟩,
  ⟨0, ![1, 2, -1, 0, -2, 0], -2⟩,
  ⟨0, ![1, 2, -1, 0, 0, -2], -2⟩,
  ⟨0, ![1, 2, 0, -2, -1, 0], 1⟩,
  ⟨0, ![1, 2, 0, -2, 0, -1], 1⟩,
  ⟨0, ![1, 2, 0, -1, -2, 0], 1⟩,
  ⟨0, ![1, 2, 0, -1, 0, -2], 1⟩,
  ⟨0, ![1, 2, 0, 0, -2, -1], 1⟩,
  ⟨0, ![1, 2, 0, 0, -1, -2], 1⟩
]

def terms6 : Array TaggedTerm := #[
  ⟨1, ![1, -1, 0, -1, -1, 2], -2⟩,
  ⟨1, ![1, -1, 0, -1, 2, -1], -2⟩,
  ⟨1, ![1, -1, 0, 2, -1, -1], -2⟩,
  ⟨1, ![1, -1, 2, -1, -1, 0], 2⟩,
  ⟨1, ![1, -1, 2, -1, 0, -1], 2⟩,
  ⟨1, ![1, -1, 2, 0, -1, -1], 2⟩,
  ⟨1, ![1, 0, -1, -1, -1, 2], 2⟩,
  ⟨1, ![1, 0, -1, -1, 2, -1], 2⟩,
  ⟨1, ![1, 0, -1, 2, -1, -1], 2⟩,
  ⟨1, ![1, 0, 2, -1, -1, -1], -6⟩,
  ⟨1, ![1, 2, -1, -1, -1, 0], -2⟩,
  ⟨1, ![1, 2, -1, -1, 0, -1], -2⟩,
  ⟨1, ![1, 2, -1, 0, -1, -1], -2⟩,
  ⟨1, ![1, 2, 0, -1, -1, -1], 6⟩
]

def terms7 : Array TaggedTerm := #[
  ⟨0, ![1, -2, -1, 0, 0, 2], -2⟩,
  ⟨0, ![1, -2, -1, 0, 2, 0], -2⟩,
  ⟨0, ![1, -2, -1, 2, 0, 0], -2⟩,
  ⟨0, ![1, -2, 0, -1, 0, 2], 1⟩,
  ⟨0, ![1, -2, 0, -1, 2, 0], 1⟩,
  ⟨0, ![1, -2, 0, 0, -1, 2], 1⟩,
  ⟨0, ![1, -2, 0, 0, 2, -1], 1⟩,
  ⟨0, ![1, -2, 0, 2, -1, 0], 1⟩,
  ⟨0, ![1, -2, 0, 2, 0, -1], 1⟩,
  ⟨0, ![1, -1, -2, 0, 0, 2], 2⟩,
  ⟨0, ![1, -1, -2, 0, 2, 0], 2⟩,
  ⟨0, ![1, -1, -2, 2, 0, 0], 2⟩,
  ⟨0, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨0, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨0, ![1, -1, 0, 0, -2, 2], -1⟩,
  ⟨0, ![1, -1, 0, 0, 2, -2], -1⟩,
  ⟨0, ![1, -1, 0, 2, -2, 0], -1⟩,
  ⟨0, ![1, -1, 0, 2, 0, -2], -1⟩,
  ⟨0, ![1, 0, -2, -1, 0, 2], -1⟩,
  ⟨0, ![1, 0, -2, -1, 2, 0], -1⟩,
  ⟨0, ![1, 0, -2, 0, -1, 2], -1⟩,
  ⟨0, ![1, 0, -2, 0, 2, -1], -1⟩,
  ⟨0, ![1, 0, -2, 2, -1, 0], -1⟩,
  ⟨0, ![1, 0, -2, 2, 0, -1], -1⟩,
  ⟨0, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨0, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨0, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨0, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨0, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨0, ![1, 0, -1, 2, 0, -2], 1⟩
]

def terms8 : Array TaggedTerm := #[
  ⟨0, ![2, -3, 0, 0, 0, 1], -2⟩,
  ⟨0, ![2, -3, 0, 0, 1, 0], -2⟩,
  ⟨0, ![2, -3, 0, 1, 0, 0], -2⟩,
  ⟨0, ![2, -3, 1, 0, 0, 0], 6⟩,
  ⟨0, ![2, 0, -3, 0, 0, 1], 2⟩,
  ⟨0, ![2, 0, -3, 0, 1, 0], 2⟩,
  ⟨0, ![2, 0, -3, 1, 0, 0], 2⟩,
  ⟨0, ![2, 0, 1, -3, 0, 0], -2⟩,
  ⟨0, ![2, 0, 1, 0, -3, 0], -2⟩,
  ⟨0, ![2, 0, 1, 0, 0, -3], -2⟩,
  ⟨0, ![2, 1, -3, 0, 0, 0], -6⟩,
  ⟨0, ![2, 1, 0, -3, 0, 0], 2⟩,
  ⟨0, ![2, 1, 0, 0, -3, 0], 2⟩,
  ⟨0, ![2, 1, 0, 0, 0, -3], 2⟩
]

def terms9 : Array TaggedTerm := #[
  ⟨1, ![1, -2, 0, -1, 1, 1], -2⟩,
  ⟨1, ![1, -2, 0, 1, -1, 1], -2⟩,
  ⟨1, ![1, -2, 0, 1, 1, -1], -2⟩,
  ⟨1, ![1, -2, 1, -1, 0, 1], 1⟩,
  ⟨1, ![1, -2, 1, -1, 1, 0], 1⟩,
  ⟨1, ![1, -2, 1, 0, -1, 1], 1⟩,
  ⟨1, ![1, -2, 1, 0, 1, -1], 1⟩,
  ⟨1, ![1, -2, 1, 1, -1, 0], 1⟩,
  ⟨1, ![1, -2, 1, 1, 0, -1], 1⟩,
  ⟨1, ![1, 0, -2, -1, 1, 1], 2⟩,
  ⟨1, ![1, 0, -2, 1, -1, 1], 2⟩,
  ⟨1, ![1, 0, -2, 1, 1, -1], 2⟩,
  ⟨1, ![1, 0, 1, -2, -1, 1], -1⟩,
  ⟨1, ![1, 0, 1, -2, 1, -1], -1⟩,
  ⟨1, ![1, 0, 1, -1, -2, 1], -1⟩,
  ⟨1, ![1, 0, 1, -1, 1, -2], -1⟩,
  ⟨1, ![1, 0, 1, 1, -2, -1], -1⟩,
  ⟨1, ![1, 0, 1, 1, -1, -2], -1⟩,
  ⟨1, ![1, 1, -2, -1, 0, 1], -1⟩,
  ⟨1, ![1, 1, -2, -1, 1, 0], -1⟩,
  ⟨1, ![1, 1, -2, 0, -1, 1], -1⟩,
  ⟨1, ![1, 1, -2, 0, 1, -1], -1⟩,
  ⟨1, ![1, 1, -2, 1, -1, 0], -1⟩,
  ⟨1, ![1, 1, -2, 1, 0, -1], -1⟩,
  ⟨1, ![1, 1, 0, -2, -1, 1], 1⟩,
  ⟨1, ![1, 1, 0, -2, 1, -1], 1⟩,
  ⟨1, ![1, 1, 0, -1, -2, 1], 1⟩,
  ⟨1, ![1, 1, 0, -1, 1, -2], 1⟩,
  ⟨1, ![1, 1, 0, 1, -2, -1], 1⟩,
  ⟨1, ![1, 1, 0, 1, -1, -2], 1⟩
]

end MUB6.Certificate.GramFunctions.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block2

def terms0 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 0, 2], -1⟩,
  ⟨1, ![1, -2, -1, 0, 2, 0], -1⟩,
  ⟨1, ![1, -2, -1, 2, 0, 0], 2⟩,
  ⟨1, ![1, -2, 0, -1, 0, 2], -1⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], -1⟩,
  ⟨1, ![1, -2, 0, 0, -1, 2], 2⟩,
  ⟨1, ![1, -2, 0, 0, 2, -1], 2⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], -1⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], -1⟩,
  ⟨1, ![1, -2, 2, -1, 0, 0], 2⟩,
  ⟨1, ![1, -2, 2, 0, -1, 0], -1⟩,
  ⟨1, ![1, -2, 2, 0, 0, -1], -1⟩,
  ⟨1, ![1, -1, -2, 0, 0, 2], 1⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 1⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], 1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -2⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -2⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], 1⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], 1⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], 1⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], -1⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], -1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], -1⟩,
  ⟨1, ![1, 0, 0, -2, -1, 2], -1⟩,
  ⟨1, ![1, 0, 0, -2, 2, -1], -1⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 1⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 1⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], 1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], 1⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], -1⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], -1⟩
]

def terms10 : Array TaggedTerm := #[
  ⟨0, ![-1, -1, 0, 0, 1, 1], -4⟩,
  ⟨0, ![-1, -1, 0, 1, 0, 1], 2⟩,
  ⟨0, ![-1, -1, 0, 1, 1, 0], 2⟩,
  ⟨0, ![-1, -1, 1, 0, 0, 1], 2⟩,
  ⟨0, ![-1, -1, 1, 0, 1, 0], 2⟩,
  ⟨0, ![-1, -1, 1, 1, 0, 0], -4⟩,
  ⟨0, ![-1, 0, -1, 0, 1, 1], 2⟩,
  ⟨0, ![-1, 0, -1, 1, 0, 1], -1⟩,
  ⟨0, ![-1, 0, -1, 1, 1, 0], -1⟩,
  ⟨0, ![-1, 0, 0, -1, 1, 1], 2⟩,
  ⟨0, ![-1, 0, 0, 1, -1, 1], -1⟩,
  ⟨0, ![-1, 0, 0, 1, 1, -1], -1⟩,
  ⟨0, ![-1, 0, 1, -1, 0, 1], -1⟩,
  ⟨0, ![-1, 0, 1, -1, 1, 0], -1⟩,
  ⟨0, ![-1, 0, 1, 0, -1, 1], -1⟩,
  ⟨0, ![-1, 0, 1, 0, 1, -1], -1⟩,
  ⟨0, ![-1, 0, 1, 1, -1, 0], 2⟩,
  ⟨0, ![-1, 0, 1, 1, 0, -1], 2⟩,
  ⟨0, ![-1, 1, -1, 0, 0, 1], -1⟩,
  ⟨0, ![-1, 1, -1, 0, 1, 0], -1⟩,
  ⟨0, ![-1, 1, -1, 1, 0, 0], 2⟩,
  ⟨0, ![-1, 1, 0, -1, 0, 1], -1⟩,
  ⟨0, ![-1, 1, 0, -1, 1, 0], -1⟩,
  ⟨0, ![-1, 1, 0, 0, -1, 1], 2⟩,
  ⟨0, ![-1, 1, 0, 0, 1, -1], 2⟩,
  ⟨0, ![-1, 1, 0, 1, -1, 0], -1⟩,
  ⟨0, ![-1, 1, 0, 1, 0, -1], -1⟩,
  ⟨0, ![-1, 1, 1, -1, 0, 0], 2⟩,
  ⟨0, ![-1, 1, 1, 0, -1, 0], -1⟩,
  ⟨0, ![-1, 1, 1, 0, 0, -1], -1⟩
]

end MUB6.Certificate.GramFunctions.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row722 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row723 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row724 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row725 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row726 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row727 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row728 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row729 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row736 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row737 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row738 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row739 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row740 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row741 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row904 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row905 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row906 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row907 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row908 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row909 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row913 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row914 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row915 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row916 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row917 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row918 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row919 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row920 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row921 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row922 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row923 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row924 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row928 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row929 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row930 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row931 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row932 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row933 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row934 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row935 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row936 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row937 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row938 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row939 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row940 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

def row941 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

def row942 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

def row943 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row944 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row945 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row946 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row947 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row948 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row949 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row950 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row951 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row952 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row953 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row954 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row955 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

def row956 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

def row957 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

def row958 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row959 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row960 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row961 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row962 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row963 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row964 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row965 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row966 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row967 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row968 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row969 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row973 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row974 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row975 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row976 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row977 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row978 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row979 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row980 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row981 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row982 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row983 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row984 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row988 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row989 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row990 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row991 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row992 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row993 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row994 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row995 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row996 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row997 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row998 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row999 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row1000 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

def row1001 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

def row1002 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

def row1003 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1004 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1005 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1006 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1007 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1008 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1009 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1010 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1011 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1012 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1013 : Integer.Sparse Key := [(key18, -2), (key100, 4), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key432, 2), (key460, -6)]

def row1014 : Integer.Sparse Key := [(key43, -2), (key100, 4), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key432, 2), (key460, -6)]

def row1015 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

def row1016 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

def row1017 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1024 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1025 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1026 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1027 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1028 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1029 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1030 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

def row1031 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

def row1032 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

def row1033 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1034 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1035 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1036 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1037 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1038 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1039 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1040 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1041 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1042 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1043 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1044 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1045 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

def row1046 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

def row1047 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

def row1048 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1049 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1050 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1051 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1052 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1053 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1054 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1055 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1056 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1057 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1058 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1059 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1060 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

def row1061 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

def row1062 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

def row1063 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1064 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1065 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1066 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1067 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1068 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1069 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1070 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1071 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key331, -1), (key346, 1), (key347, 1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1072 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key331, -1), (key346, 1), (key347, 1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1073 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1074 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1075 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

def row1076 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

def row1077 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

def row1078 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1079 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1080 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key331, 1), (key346, 1), (key347, -1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1081 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key331, 1), (key346, 1), (key347, -1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1082 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1083 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1084 : Integer.Sparse Key := [(key2693, -2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2)]

def row1085 : Integer.Sparse Key := [(key2693, -2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2)]

def row1086 : Integer.Sparse Key := [(key2693, -4), (key3018, -2), (key3055, 2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2), (key3117, 2)]

def row1087 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1088 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

def row1089 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

def row1090 : Integer.Sparse Key := [(key2693, 2), (key2719, -2), (key2733, 2), (key3057, -2), (key3074, 2), (key3078, -2)]

def row1091 : Integer.Sparse Key := [(key2693, 2), (key2719, -2), (key2733, 2), (key3057, -2), (key3074, 2), (key3078, -2)]

def row1092 : Integer.Sparse Key := [(key2693, 4), (key2719, -2), (key2733, 2), (key3018, 2), (key3055, -2), (key3057, -2), (key3074, 2), (key3078, -2), (key3117, -2)]

def row1093 : Integer.Sparse Key := [(key2693, -6), (key2719, 6), (key2733, -6), (key2759, 6), (key3057, 6), (key3074, -6)]

def row1094 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

def row1095 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

def row1096 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

def row1097 : Integer.Sparse Key := [(key2693, 6), (key2695, -6), (key2719, -6), (key2733, 6), (key2756, 6), (key2759, -6)]

def row1098 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1099 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1100 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1101 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1102 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1103 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1104 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1105 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1106 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1107 : Integer.Sparse Key := [(key1432, -6), (key1475, 6), (key1581, 6), (key1686, -6), (key1906, -6), (key1923, 6)]

def row1108 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1109 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1110 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1111 : Integer.Sparse Key := [(key1432, 6), (key1475, -6), (key1581, -6), (key1686, 6), (key1906, 6), (key1923, -6)]

def row1112 : Integer.Sparse Key := [(key2679, 1), (key2691, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3047, -1), (key3058, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3115, -2), (key3142, -2), (key3143, 2)]

def row1113 : Integer.Sparse Key := [(key2679, 1), (key2691, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3047, -1), (key3058, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3115, -2), (key3142, -2), (key3143, 2)]

def row1114 : Integer.Sparse Key := [(key2679, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3014, -2), (key3047, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3142, -2), (key3143, 2)]

def row1115 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

def row1116 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

def row1117 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

def row1118 : Integer.Sparse Key := [(key2679, -1), (key2691, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3024, -2), (key3047, 1), (key3058, 1), (key3115, 2)]

def row1119 : Integer.Sparse Key := [(key2679, -1), (key2691, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3024, -2), (key3047, 1), (key3058, 1), (key3115, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1120 : Integer.Sparse Key := [(key2679, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3014, 2), (key3024, -2), (key3047, 1)]

def row1122 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row1123 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row1124 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row1125 : Integer.Sparse Key := [(key2717, 6), (key2755, -6), (key2820, -6), (key2921, 6), (key3014, 6), (key3024, -6)]

def row1126 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1127 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1128 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1129 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1130 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1131 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1132 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1133 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1134 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1135 : Integer.Sparse Key := [(key1048, -6), (key1054, 6), (key1134, 6), (key1142, -6), (key1238, -6), (key1240, 6)]

def row1136 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1137 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1138 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1139 : Integer.Sparse Key := [(key1048, 6), (key1054, -6), (key1134, -6), (key1142, 6), (key1238, 6), (key1240, -6)]

def row1140 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1141 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1142 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1143 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1144 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1145 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1146 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1147 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1148 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1149 : Integer.Sparse Key := [(key3063, -6), (key3065, 6), (key3098, 6), (key3102, -6), (key3124, -6), (key3126, 6)]

def row1150 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1151 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1152 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1153 : Integer.Sparse Key := [(key3063, 6), (key3065, -6), (key3098, -6), (key3102, 6), (key3124, 6), (key3126, -6)]

def row1154 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1155 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1156 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1157 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1158 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1159 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1160 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1161 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1162 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1163 : Integer.Sparse Key := [(key1405, -6), (key1410, 6), (key1433, 6), (key1439, -6), (key1477, -6), (key1479, 6)]

def row1164 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1165 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1166 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1167 : Integer.Sparse Key := [(key1405, 6), (key1410, -6), (key1433, -6), (key1439, 6), (key1477, 6), (key1479, -6)]

def row1168 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1169 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1170 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1171 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

def row1172 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

def row1173 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

def row1174 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

def row1175 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

def row1176 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

def row1177 : Integer.Sparse Key := [(key3081, -6), (key3083, 6), (key3086, 6), (key3089, -12), (key3093, 6)]

def row1178 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1179 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1180 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1181 : Integer.Sparse Key := [(key3081, 6), (key3083, -6), (key3086, -6), (key3089, 6), (key3092, 6), (key3093, -6)]

def row1182 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

def row1183 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

def row1184 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

def row1185 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1186 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1187 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1188 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1189 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1190 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1191 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

def row1192 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

def row1193 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

def row1194 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1195 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1196 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1197 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1198 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1199 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1200 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

def row1201 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

def row1202 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

def row1203 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1204 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1205 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1206 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1207 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1208 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1209 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

def row1210 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

def row1211 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

def row1212 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1213 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1214 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1215 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1216 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1217 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1218 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

def row1219 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

def row1220 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

def row1221 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1222 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1223 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1224 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1225 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1226 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1227 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

def row1228 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

def row1229 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

def row1230 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1231 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1232 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1233 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1234 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1235 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1236 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

def row1237 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

def row1238 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

def row1239 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1240 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1241 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1242 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1243 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1244 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1245 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

def row1246 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

def row1247 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

def row1248 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1249 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1250 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1251 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1252 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1253 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1254 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

def row1255 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

def row1256 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

def row1257 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1258 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1259 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1260 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1261 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1262 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1263 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

def row1264 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

def row1265 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

def row1266 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1267 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1268 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1269 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1270 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1271 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1272 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row1273 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row1274 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row1275 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1276 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1277 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1278 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1279 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

end MUB6.Certificate.GramRows

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

def row1280 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1281 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

def row1282 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

def row1283 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

def row1284 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1285 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1286 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1287 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1288 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1289 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1290 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

def row1291 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

def row1292 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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

end MUB6.Certificate.GramRows

end OAI
end


