-- Prove2me | Definitions.Def_OAIQ106D172
-- name    : OAIQ106D172
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:37:49.229447+00:00
-- url     : https://prove2.me/theorems/35b2340b-85e0-4deb-b406-c2db9005a803
-- title:
--   Definitions bundle OAIQ106D172 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 430 declarations of OpenAI's Lean: 430 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow4567`, `OAI.MUB6.Certificate.GramRows.rawRow4568`, `OAI.MUB6.Certificate.GramRows.rawRow4569`, `OAI.MUB6.Certificate.GramRows.rawRow457`, `OAI.MUB6.Certificate.GramRows.rawRow4570`, `OAI.MUB6.Certificate.GramRows.rawRow4571`, `OAI.MUB6.Certificate.GramRows.rawRow4572`, `OAI.MUB6.Certificate.GramRows.rawRow4574`, `OAI.MUB6.Certificate.GramRows.rawRow4575`, `OAI.MUB6.Certificate.GramRows.rawRow4576`, `OAI.MUB6.Certificate.GramRows.rawRow4577`, `OAI.MUB6.Certificate.GramRows.rawRow4578`, `OAI.MUB6.Certificate.GramRows.rawRow4579`, `OAI.MUB6.Certificate.GramRows.rawRow458`, `OAI.MUB6.Certificate.GramRows.rawRow4581`, `OAI.MUB6.Certificate.GramRows.rawRow4582`, `OAI.MUB6.Certificate.GramRows.rawRow4583`, `OAI.MUB6.Certificate.GramRows.rawRow4584`, `OAI.MUB6.Certificate.GramRows.rawRow4585`, `OAI.MUB6.Certificate.GramRows.rawRow4586`, `OAI.MUB6.Certificate.GramRows.rawRow4588`, `OAI.MUB6.Certificate.GramRows.rawRow4589`, `OAI.MUB6.Certificate.GramRows.rawRow459`, `OAI.MUB6.Certificate.GramRows.rawRow4590`, `OAI.MUB6.Certificate.GramRows.rawRow4591`, `OAI.MUB6.Certificate.GramRows.rawRow4592`, `OAI.MUB6.Certificate.GramRows.rawRow4593`, `OAI.MUB6.Certificate.GramRows.rawRow4595`, `OAI.MUB6.Certificate.GramRows.rawRow4596`, `OAI.MUB6.Certificate.GramRows.rawRow4597`, `OAI.MUB6.Certificate.GramRows.rawRow4598`, `OAI.MUB6.Certificate.GramRows.rawRow4599`, `OAI.MUB6.Certificate.GramRows.rawRow46`, `OAI.MUB6.Certificate.GramRows.rawRow460`, `OAI.MUB6.Certificate.GramRows.rawRow4600`, `OAI.MUB6.Certificate.GramRows.rawRow4602`, `OAI.MUB6.Certificate.GramRows.rawRow4603`, `OAI.MUB6.Certificate.GramRows.rawRow4604`, `OAI.MUB6.Certificate.GramRows.rawRow4605`, `OAI.MUB6.Certificate.GramRows.rawRow4606` and 390 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block11.lean), [`MutuallyUnbiased_GramRows_Block59`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block59.lean), [`MutuallyUnbiased_GramRows_Block60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block60.lean), [`MutuallyUnbiased_GramRows_Block61`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block61.lean), [`MutuallyUnbiased_GramRows_Block62`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block62.lean), [`MutuallyUnbiased_GramRows_Block64`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block64.lean), [`MutuallyUnbiased_GramRows_Block65`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block65.lean), [`MutuallyUnbiased_GramRows_Block66`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block66.lean), [`MutuallyUnbiased_TaoCertificate_Merge36`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge36.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092`, `OAIQ106D094` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow5 : Integer.Sparse Key := [(key251, -1), (key260, -1), (key248, 2), (key267, 1), (key271, 1), (key236, -1), (key248, -1), (key260, -2), (key239, 1), (key251, 1), (key319, 1), (key335, 1), (key316, -2), (key328, -1), (key340, -1), (key302, 1), (key316, 1), (key328, 2), (key305, -1), (key319, -1), (key442, -1), (key469, -1), (key406, 1), (key435, 1), (key450, 1), (key475, 1), (key385, -1), (key435, -1), (key418, -1), (key450, -1), (key397, 1), (key442, 1), (key595, 2), (key578, -1), (key593, -1), (key601, -2), (key568, 1), (key593, 1), (key583, 1), (key601, 1), (key572, -1), (key595, -1)]

def rawRow46 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1316, 2), (key1337, 1), (key1345, 1), (key1296, -1), (key1337, -1), (key1339, -2), (key1302, 1), (key1339, 1), (key1546, 1), (key1559, 1), (key1546, -2), (key1772, -1), (key1780, -1), (key1391, 1), (key1772, 1), (key1774, 2), (key1397, -1), (key1774, -1), (key1655, -1), (key1659, -1), (key1573, 1), (key1655, 1), (key1813, 1), (key1817, 1), (key1424, -1), (key1813, -1), (key1790, -1), (key1839, -1), (key1457, 1), (key1839, 1), (key1667, 2), (key1596, -1), (key1667, -1), (key1825, -2), (key1447, 1), (key1825, 1), (key1798, 1), (key1844, 1), (key1466, -1), (key1844, -1)]

def rawRow47 : Integer.Sparse Key := [(key1329, -1), (key1316, -1), (key1316, 2), (key1345, 1), (key1337, 1), (key1337, -1), (key1296, -1), (key1339, -2), (key1339, 1), (key1302, 1), (key1559, 1), (key1546, 1), (key1546, -2), (key1780, -1), (key1772, -1), (key1772, 1), (key1391, 1), (key1774, 2), (key1774, -1), (key1397, -1), (key1659, -1), (key1655, -1), (key1655, 1), (key1573, 1), (key1817, 1), (key1813, 1), (key1813, -1), (key1424, -1), (key1839, -1), (key1790, -1), (key1839, 1), (key1457, 1), (key1667, 2), (key1667, -1), (key1596, -1), (key1825, -2), (key1825, 1), (key1447, 1), (key1844, 1), (key1798, 1), (key1844, -1), (key1466, -1)]

def rawRow48 : Integer.Sparse Key := [(key1337, -1), (key1339, -1), (key1345, 2), (key1296, 1), (key1302, 1), (key1329, -1), (key1345, -1), (key1296, -2), (key1316, 1), (key1337, 1), (key1772, 1), (key1774, 1), (key1780, -2), (key1391, -1), (key1397, -1), (key1559, 1), (key1780, 1), (key1391, 2), (key1546, -1), (key1772, -1), (key1788, -1), (key1790, -1), (key1817, 1), (key1841, 1), (key1455, 1), (key1457, 1), (key1659, -1), (key1841, -1), (key1424, -1), (key1455, -1), (key1573, 1), (key1788, 1), (key1798, 2), (key1825, -1), (key1844, -1), (key1466, -2), (key1667, 1), (key1844, 1), (key1447, 1), (key1466, 1), (key1596, -1), (key1798, -1)]

def rawRow49 : Integer.Sparse Key := [(key1339, -1), (key1337, -1), (key1345, 2), (key1302, 1), (key1296, 1), (key1345, -1), (key1329, -1), (key1296, -2), (key1337, 1), (key1316, 1), (key1774, 1), (key1772, 1), (key1780, -2), (key1397, -1), (key1391, -1), (key1780, 1), (key1559, 1), (key1391, 2), (key1772, -1), (key1546, -1), (key1790, -1), (key1788, -1), (key1841, 1), (key1817, 1), (key1457, 1), (key1455, 1), (key1841, -1), (key1659, -1), (key1455, -1), (key1424, -1), (key1788, 1), (key1573, 1), (key1798, 2), (key1844, -1), (key1825, -1), (key1466, -2), (key1844, 1), (key1667, 1), (key1466, 1), (key1447, 1), (key1798, -1), (key1596, -1)]

def rawRow50 : Integer.Sparse Key := [(key1337, -1), (key1345, -1), (key1339, 2), (key1316, 1), (key1329, 1), (key1302, -1), (key1339, -1), (key1316, -2), (key1296, 1), (key1337, 1), (key1772, 1), (key1780, 1), (key1774, -2), (key1546, -1), (key1559, -1), (key1397, 1), (key1774, 1), (key1546, 2), (key1391, -1), (key1772, -1), (key1813, -1), (key1817, -1), (key1790, 1), (key1839, 1), (key1655, 1), (key1659, 1), (key1457, -1), (key1839, -1), (key1573, -1), (key1655, -1), (key1424, 1), (key1813, 1), (key1825, 2), (key1798, -1), (key1844, -1), (key1667, -2), (key1466, 1), (key1844, 1), (key1596, 1), (key1667, 1), (key1447, -1), (key1825, -1)]

def rawRow51 : Integer.Sparse Key := [(key1345, -1), (key1337, -1), (key1339, 2), (key1329, 1), (key1316, 1), (key1339, -1), (key1302, -1), (key1316, -2), (key1337, 1), (key1296, 1), (key1780, 1), (key1772, 1), (key1774, -2), (key1559, -1), (key1546, -1), (key1774, 1), (key1397, 1), (key1546, 2), (key1772, -1), (key1391, -1), (key1817, -1), (key1813, -1), (key1839, 1), (key1790, 1), (key1659, 1), (key1655, 1), (key1839, -1), (key1457, -1), (key1655, -1), (key1573, -1), (key1813, 1), (key1424, 1), (key1825, 2), (key1844, -1), (key1798, -1), (key1667, -2), (key1844, 1), (key1466, 1), (key1667, 1), (key1596, 1), (key1825, -1), (key1447, -1)]

def rawRow53 : Integer.Sparse Key := [(key1391, -1), (key1397, -1), (key1391, 2), (key1455, 1), (key1457, 1), (key1424, -1), (key1455, -1), (key1466, -2), (key1447, 1), (key1466, 1), (key1296, 1), (key1302, 1), (key1296, -2), (key1788, -1), (key1790, -1), (key1573, 1), (key1788, 1), (key1798, 2), (key1596, -1), (key1798, -1), (key1337, -1), (key1339, -1), (key1316, 1), (key1337, 1), (key1772, 1), (key1774, 1), (key1546, -1), (key1772, -1), (key1825, -1), (key1844, -1), (key1667, 1), (key1844, 1), (key1345, 2), (key1329, -1), (key1345, -1), (key1780, -2), (key1559, 1), (key1780, 1), (key1817, 1), (key1841, 1), (key1659, -1), (key1841, -1)]

def rawRow54 : Integer.Sparse Key := [(key1397, -1), (key1391, -1), (key1391, 2), (key1457, 1), (key1455, 1), (key1455, -1), (key1424, -1), (key1466, -2), (key1466, 1), (key1447, 1), (key1302, 1), (key1296, 1), (key1296, -2), (key1790, -1), (key1788, -1), (key1788, 1), (key1573, 1), (key1798, 2), (key1798, -1), (key1596, -1), (key1339, -1), (key1337, -1), (key1337, 1), (key1316, 1), (key1774, 1), (key1772, 1), (key1772, -1), (key1546, -1), (key1844, -1), (key1825, -1), (key1844, 1), (key1667, 1), (key1345, 2), (key1345, -1), (key1329, -1), (key1780, -2), (key1780, 1), (key1559, 1), (key1841, 1), (key1817, 1), (key1841, -1), (key1659, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow457 : Integer.Sparse Key := [(key1796, -1), (key1787, -1), (key1787, 2), (key1823, 1), (key1812, 1), (key1812, -1), (key1771, -1), (key1815, -2), (key1815, 1), (key1778, 1), (key1464, 1), (key1454, 1), (key1454, -2), (key1665, -1), (key1654, -1), (key1654, 1), (key1336, 1), (key1657, 2), (key1657, -1), (key1343, -1), (key1442, -1), (key1423, -1), (key1423, 1), (key1390, 1), (key1591, 1), (key1572, 1), (key1572, -1), (key1295, -1), (key1622, -1), (key1554, -1), (key1622, 1), (key1324, 1), (key1419, 2), (key1419, -1), (key1386, -1), (key1568, -2), (key1568, 1), (key1291, 1), (key1617, 1), (key1541, 1), (key1617, -1), (key1311, -1)]

def rawRow458 : Integer.Sparse Key := [(key1812, -1), (key1815, -1), (key1823, 2), (key1771, 1), (key1778, 1), (key1796, -1), (key1823, -1), (key1771, -2), (key1787, 1), (key1812, 1), (key1654, 1), (key1657, 1), (key1665, -2), (key1336, -1), (key1343, -1), (key1464, 1), (key1665, 1), (key1336, 2), (key1454, -1), (key1654, -1), (key1545, -1), (key1554, -1), (key1591, 1), (key1631, 1), (key1315, 1), (key1324, 1), (key1442, -1), (key1631, -1), (key1295, -1), (key1315, -1), (key1390, 1), (key1545, 1), (key1541, 2), (key1568, -1), (key1617, -1), (key1311, -2), (key1419, 1), (key1617, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1541, -1)]

def rawRow459 : Integer.Sparse Key := [(key1815, -1), (key1812, -1), (key1823, 2), (key1778, 1), (key1771, 1), (key1823, -1), (key1796, -1), (key1771, -2), (key1812, 1), (key1787, 1), (key1657, 1), (key1654, 1), (key1665, -2), (key1343, -1), (key1336, -1), (key1665, 1), (key1464, 1), (key1336, 2), (key1654, -1), (key1454, -1), (key1554, -1), (key1545, -1), (key1631, 1), (key1591, 1), (key1324, 1), (key1315, 1), (key1631, -1), (key1442, -1), (key1315, -1), (key1295, -1), (key1545, 1), (key1390, 1), (key1541, 2), (key1617, -1), (key1568, -1), (key1311, -2), (key1617, 1), (key1419, 1), (key1311, 1), (key1291, 1), (key1541, -1), (key1386, -1)]

def rawRow460 : Integer.Sparse Key := [(key1812, -1), (key1823, -1), (key1815, 2), (key1787, 1), (key1796, 1), (key1778, -1), (key1815, -1), (key1787, -2), (key1771, 1), (key1812, 1), (key1654, 1), (key1665, 1), (key1657, -2), (key1454, -1), (key1464, -1), (key1343, 1), (key1657, 1), (key1454, 2), (key1336, -1), (key1654, -1), (key1572, -1), (key1591, -1), (key1554, 1), (key1622, 1), (key1423, 1), (key1442, 1), (key1324, -1), (key1622, -1), (key1390, -1), (key1423, -1), (key1295, 1), (key1572, 1), (key1568, 2), (key1541, -1), (key1617, -1), (key1419, -2), (key1311, 1), (key1617, 1), (key1386, 1), (key1419, 1), (key1291, -1), (key1568, -1)]

def rawRow461 : Integer.Sparse Key := [(key1823, -1), (key1812, -1), (key1815, 2), (key1796, 1), (key1787, 1), (key1815, -1), (key1778, -1), (key1787, -2), (key1812, 1), (key1771, 1), (key1665, 1), (key1654, 1), (key1657, -2), (key1464, -1), (key1454, -1), (key1657, 1), (key1343, 1), (key1454, 2), (key1654, -1), (key1336, -1), (key1591, -1), (key1572, -1), (key1622, 1), (key1554, 1), (key1442, 1), (key1423, 1), (key1622, -1), (key1324, -1), (key1423, -1), (key1390, -1), (key1572, 1), (key1295, 1), (key1568, 2), (key1617, -1), (key1541, -1), (key1419, -2), (key1617, 1), (key1311, 1), (key1419, 1), (key1386, 1), (key1568, -1), (key1291, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4567 : Integer.Sparse Key := [(key1379, -2), (key1870, -2), (key1870, -2), (key1379, 1), (key1379, 1), (key1728, 1), (key1728, 1), (key1870, 1), (key1870, 1), (key1370, 2), (key1865, 2), (key1865, 2), (key1370, -1), (key1370, -1), (key1496, -1), (key1496, -1), (key1865, -1), (key1865, -1), (key1366, -1), (key1366, -1), (key1718, -1), (key1718, -1), (key1863, -1), (key1863, -1), (key1366, 1), (key1366, 1), (key1492, 1), (key1492, 1), (key1863, 1), (key1863, 1)]

def rawRow4568 : Integer.Sparse Key := [(key1870, -2), (key1379, -2), (key1870, -2), (key1728, 1), (key1870, 1), (key1379, 1), (key1870, 1), (key1379, 1), (key1728, 1), (key1865, 2), (key1370, 2), (key1865, 2), (key1496, -1), (key1865, -1), (key1370, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1718, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1718, -1), (key1492, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1492, 1)]

def rawRow4569 : Integer.Sparse Key := [(key1870, -2), (key1870, -2), (key1379, -2), (key1870, 1), (key1728, 1), (key1870, 1), (key1379, 1), (key1728, 1), (key1379, 1), (key1865, 2), (key1865, 2), (key1370, 2), (key1865, -1), (key1496, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1370, -1), (key1863, -1), (key1718, -1), (key1863, -1), (key1366, -1), (key1718, -1), (key1366, -1), (key1863, 1), (key1492, 1), (key1863, 1), (key1366, 1), (key1492, 1), (key1366, 1)]

def rawRow4570 : Integer.Sparse Key := [(key281, -6), (key281, 2), (key281, 2), (key290, 2), (key350, 6), (key350, -2), (key350, -2), (key367, -2), (key507, -2), (key507, -2), (key516, -2), (key507, 2), (key507, 2), (key538, 2)]

def rawRow4571 : Integer.Sparse Key := [(key281, -6), (key281, 2), (key290, 2), (key281, 2), (key350, 6), (key350, -2), (key367, -2), (key350, -2), (key507, -2), (key516, -2), (key507, -2), (key507, 2), (key538, 2), (key507, 2)]

def rawRow4572 : Integer.Sparse Key := [(key281, -6), (key290, 2), (key281, 2), (key281, 2), (key350, 6), (key367, -2), (key350, -2), (key350, -2), (key516, -2), (key507, -2), (key507, -2), (key538, 2), (key507, 2), (key507, 2)]

def rawRow4574 : Integer.Sparse Key := [(key350, -6), (key507, 2), (key507, 2), (key516, 2), (key281, 6), (key507, -2), (key507, -2), (key538, -2), (key281, -2), (key281, -2), (key290, -2), (key350, 2), (key350, 2), (key367, 2)]

def rawRow4575 : Integer.Sparse Key := [(key350, -6), (key507, 2), (key516, 2), (key507, 2), (key281, 6), (key507, -2), (key538, -2), (key507, -2), (key281, -2), (key290, -2), (key281, -2), (key350, 2), (key367, 2), (key350, 2)]

def rawRow4576 : Integer.Sparse Key := [(key350, -6), (key516, 2), (key507, 2), (key507, 2), (key281, 6), (key538, -2), (key507, -2), (key507, -2), (key290, -2), (key281, -2), (key281, -2), (key367, 2), (key350, 2), (key350, 2)]

def rawRow4577 : Integer.Sparse Key := [(key516, -6), (key350, 2), (key507, 2), (key507, 2), (key538, 6), (key281, -2), (key507, -2), (key507, -2), (key367, -2), (key538, -2), (key538, -2), (key290, 2), (key516, 2), (key516, 2)]

def rawRow4578 : Integer.Sparse Key := [(key516, -6), (key507, 2), (key350, 2), (key507, 2), (key538, 6), (key507, -2), (key281, -2), (key507, -2), (key538, -2), (key367, -2), (key538, -2), (key516, 2), (key290, 2), (key516, 2)]

def rawRow4579 : Integer.Sparse Key := [(key516, -6), (key507, 2), (key507, 2), (key350, 2), (key538, 6), (key507, -2), (key507, -2), (key281, -2), (key538, -2), (key538, -2), (key367, -2), (key516, 2), (key516, 2), (key290, 2)]

def rawRow4581 : Integer.Sparse Key := [(key538, -6), (key367, 2), (key538, 2), (key538, 2), (key516, 6), (key290, -2), (key516, -2), (key516, -2), (key350, -2), (key507, -2), (key507, -2), (key281, 2), (key507, 2), (key507, 2)]

def rawRow4582 : Integer.Sparse Key := [(key538, -6), (key538, 2), (key367, 2), (key538, 2), (key516, 6), (key516, -2), (key290, -2), (key516, -2), (key507, -2), (key350, -2), (key507, -2), (key507, 2), (key281, 2), (key507, 2)]

def rawRow4583 : Integer.Sparse Key := [(key538, -6), (key538, 2), (key538, 2), (key367, 2), (key516, 6), (key516, -2), (key516, -2), (key290, -2), (key507, -2), (key507, -2), (key350, -2), (key507, 2), (key507, 2), (key281, 2)]

def rawRow4584 : Integer.Sparse Key := [(key1362, -2), (key1367, -2), (key1367, -2), (key1362, 1), (key1367, 1), (key1362, 1), (key1376, 1), (key1367, 1), (key1376, 1), (key1488, 2), (key1493, 2), (key1493, 2), (key1488, -1), (key1493, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1515, -1), (key1714, -1), (key1719, -1), (key1714, -1), (key1725, -1), (key1719, -1), (key1725, -1), (key1714, 1), (key1719, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1743, 1)]

def rawRow4585 : Integer.Sparse Key := [(key1367, -2), (key1362, -2), (key1367, -2), (key1367, 1), (key1362, 1), (key1376, 1), (key1362, 1), (key1376, 1), (key1367, 1), (key1493, 2), (key1488, 2), (key1493, 2), (key1493, -1), (key1488, -1), (key1515, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1719, -1), (key1714, -1), (key1725, -1), (key1714, -1), (key1725, -1), (key1719, -1), (key1719, 1), (key1714, 1), (key1743, 1), (key1714, 1), (key1743, 1), (key1719, 1)]

def rawRow4586 : Integer.Sparse Key := [(key1367, -2), (key1367, -2), (key1362, -2), (key1376, 1), (key1376, 1), (key1367, 1), (key1367, 1), (key1362, 1), (key1362, 1), (key1493, 2), (key1493, 2), (key1488, 2), (key1515, -1), (key1515, -1), (key1493, -1), (key1493, -1), (key1488, -1), (key1488, -1), (key1725, -1), (key1725, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1743, 1), (key1743, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1)]

def rawRow4588 : Integer.Sparse Key := [(key1488, -2), (key1493, -2), (key1493, -2), (key1714, 1), (key1719, 1), (key1714, 1), (key1725, 1), (key1719, 1), (key1725, 1), (key1362, 2), (key1367, 2), (key1367, 2), (key1714, -1), (key1719, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1362, -1), (key1367, -1), (key1362, -1), (key1376, -1), (key1367, -1), (key1376, -1), (key1488, 1), (key1493, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1515, 1)]

def rawRow4589 : Integer.Sparse Key := [(key1493, -2), (key1488, -2), (key1493, -2), (key1719, 1), (key1714, 1), (key1725, 1), (key1714, 1), (key1725, 1), (key1719, 1), (key1367, 2), (key1362, 2), (key1367, 2), (key1719, -1), (key1714, -1), (key1743, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1367, -1), (key1362, -1), (key1376, -1), (key1362, -1), (key1376, -1), (key1367, -1), (key1493, 1), (key1488, 1), (key1515, 1), (key1488, 1), (key1515, 1), (key1493, 1)]

def rawRow4590 : Integer.Sparse Key := [(key1493, -2), (key1493, -2), (key1488, -2), (key1725, 1), (key1725, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1), (key1367, 2), (key1367, 2), (key1362, 2), (key1743, -1), (key1743, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1376, -1), (key1376, -1), (key1367, -1), (key1367, -1), (key1362, -1), (key1362, -1), (key1515, 1), (key1515, 1), (key1493, 1), (key1493, 1), (key1488, 1), (key1488, 1)]

def rawRow4591 : Integer.Sparse Key := [(key1725, -2), (key1725, -2), (key1941, -2), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1), (key1743, 2), (key1743, 2), (key1950, 2), (key1367, -1), (key1367, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1515, -1), (key1515, -1), (key1743, -1), (key1743, -1), (key1950, -1), (key1950, -1), (key1376, 1), (key1376, 1), (key1725, 1), (key1725, 1), (key1941, 1), (key1941, 1)]

def rawRow4592 : Integer.Sparse Key := [(key1725, -2), (key1941, -2), (key1725, -2), (key1719, 1), (key1938, 1), (key1493, 1), (key1938, 1), (key1493, 1), (key1719, 1), (key1743, 2), (key1950, 2), (key1743, 2), (key1719, -1), (key1938, -1), (key1367, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1743, -1), (key1950, -1), (key1515, -1), (key1950, -1), (key1515, -1), (key1743, -1), (key1725, 1), (key1941, 1), (key1376, 1), (key1941, 1), (key1376, 1), (key1725, 1)]

def rawRow4593 : Integer.Sparse Key := [(key1941, -2), (key1725, -2), (key1725, -2), (key1938, 1), (key1719, 1), (key1938, 1), (key1493, 1), (key1719, 1), (key1493, 1), (key1950, 2), (key1743, 2), (key1743, 2), (key1938, -1), (key1719, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1950, -1), (key1743, -1), (key1950, -1), (key1515, -1), (key1743, -1), (key1515, -1), (key1941, 1), (key1725, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1376, 1)]

def rawRow4595 : Integer.Sparse Key := [(key1743, -2), (key1743, -2), (key1950, -2), (key1515, 1), (key1515, 1), (key1743, 1), (key1743, 1), (key1950, 1), (key1950, 1), (key1725, 2), (key1725, 2), (key1941, 2), (key1376, -1), (key1376, -1), (key1725, -1), (key1725, -1), (key1941, -1), (key1941, -1), (key1493, -1), (key1493, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1367, 1), (key1367, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1)]

def rawRow4596 : Integer.Sparse Key := [(key1743, -2), (key1950, -2), (key1743, -2), (key1743, 1), (key1950, 1), (key1515, 1), (key1950, 1), (key1515, 1), (key1743, 1), (key1725, 2), (key1941, 2), (key1725, 2), (key1725, -1), (key1941, -1), (key1376, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1719, -1), (key1938, -1), (key1493, -1), (key1938, -1), (key1493, -1), (key1719, -1), (key1719, 1), (key1938, 1), (key1367, 1), (key1938, 1), (key1367, 1), (key1719, 1)]

def rawRow4597 : Integer.Sparse Key := [(key1950, -2), (key1743, -2), (key1743, -2), (key1950, 1), (key1743, 1), (key1950, 1), (key1515, 1), (key1743, 1), (key1515, 1), (key1941, 2), (key1725, 2), (key1725, 2), (key1941, -1), (key1725, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1376, -1), (key1938, -1), (key1719, -1), (key1938, -1), (key1493, -1), (key1719, -1), (key1493, -1), (key1938, 1), (key1719, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1367, 1)]

def rawRow4598 : Integer.Sparse Key := [(key29, -2), (key33, -2), (key33, -2), (key33, 6), (key495, 2), (key500, 2), (key500, 2), (key500, -2), (key500, -2), (key554, -2), (key665, -6), (key665, 2), (key665, 2), (key682, 2)]

def rawRow4599 : Integer.Sparse Key := [(key33, -2), (key29, -2), (key33, -2), (key33, 6), (key500, 2), (key495, 2), (key500, 2), (key500, -2), (key554, -2), (key500, -2), (key665, -6), (key665, 2), (key682, 2), (key665, 2)]

def rawRow4600 : Integer.Sparse Key := [(key33, -2), (key33, -2), (key29, -2), (key33, 6), (key500, 2), (key500, 2), (key495, 2), (key554, -2), (key500, -2), (key500, -2), (key665, -6), (key682, 2), (key665, 2), (key665, 2)]

def rawRow4602 : Integer.Sparse Key := [(key109, -2), (key113, -2), (key113, -2), (key149, 6), (key29, 2), (key33, 2), (key33, 2), (key665, -2), (key665, -2), (key682, -2), (key228, -6), (key500, 2), (key500, 2), (key554, 2)]

def rawRow4603 : Integer.Sparse Key := [(key113, -2), (key109, -2), (key113, -2), (key149, 6), (key33, 2), (key29, 2), (key33, 2), (key665, -2), (key682, -2), (key665, -2), (key228, -6), (key500, 2), (key554, 2), (key500, 2)]

def rawRow4604 : Integer.Sparse Key := [(key113, -2), (key113, -2), (key109, -2), (key149, 6), (key33, 2), (key33, 2), (key29, 2), (key682, -2), (key665, -2), (key665, -2), (key228, -6), (key554, 2), (key500, 2), (key500, 2)]

def rawRow4605 : Integer.Sparse Key := [(key113, -2), (key113, -2), (key149, -2), (key109, 6), (key175, 2), (key175, 2), (key185, 2), (key223, -2), (key495, -2), (key495, -2), (key554, -6), (key228, 2), (key500, 2), (key500, 2)]

def rawRow4606 : Integer.Sparse Key := [(key113, -2), (key149, -2), (key113, -2), (key109, 6), (key175, 2), (key185, 2), (key175, 2), (key495, -2), (key223, -2), (key495, -2), (key554, -6), (key500, 2), (key228, 2), (key500, 2)]

def rawRow4607 : Integer.Sparse Key := [(key149, -2), (key113, -2), (key113, -2), (key109, 6), (key185, 2), (key175, 2), (key175, 2), (key495, -2), (key495, -2), (key223, -2), (key554, -6), (key500, 2), (key500, 2), (key228, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4609 : Integer.Sparse Key := [(key175, -2), (key175, -2), (key185, -2), (key175, 6), (key113, 2), (key113, 2), (key149, 2), (key33, -2), (key113, -2), (key113, -2), (key495, -6), (key223, 2), (key495, 2), (key495, 2)]

def rawRow4610 : Integer.Sparse Key := [(key175, -2), (key185, -2), (key175, -2), (key175, 6), (key113, 2), (key149, 2), (key113, 2), (key113, -2), (key33, -2), (key113, -2), (key495, -6), (key495, 2), (key223, 2), (key495, 2)]

def rawRow4611 : Integer.Sparse Key := [(key185, -2), (key175, -2), (key175, -2), (key175, 6), (key149, 2), (key113, 2), (key113, 2), (key113, -2), (key113, -2), (key33, -2), (key495, -6), (key495, 2), (key495, 2), (key223, 2)]

def rawRow4612 : Integer.Sparse Key := [(key1361, -6), (key1361, 2), (key1361, 2), (key1373, 2), (key1487, 6), (key1487, -2), (key1487, -2), (key1512, -2), (key1713, -2), (key1713, -2), (key1722, -2), (key1713, 2), (key1713, 2), (key1740, 2)]

def rawRow4613 : Integer.Sparse Key := [(key1361, -6), (key1361, 2), (key1373, 2), (key1361, 2), (key1487, 6), (key1487, -2), (key1512, -2), (key1487, -2), (key1713, -2), (key1722, -2), (key1713, -2), (key1713, 2), (key1740, 2), (key1713, 2)]

def rawRow4614 : Integer.Sparse Key := [(key1361, -6), (key1373, 2), (key1361, 2), (key1361, 2), (key1487, 6), (key1512, -2), (key1487, -2), (key1487, -2), (key1722, -2), (key1713, -2), (key1713, -2), (key1740, 2), (key1713, 2), (key1713, 2)]

def rawRow4616 : Integer.Sparse Key := [(key1487, -6), (key1713, 2), (key1713, 2), (key1722, 2), (key1361, 6), (key1713, -2), (key1713, -2), (key1740, -2), (key1361, -2), (key1361, -2), (key1373, -2), (key1487, 2), (key1487, 2), (key1512, 2)]

def rawRow4617 : Integer.Sparse Key := [(key1487, -6), (key1713, 2), (key1722, 2), (key1713, 2), (key1361, 6), (key1713, -2), (key1740, -2), (key1713, -2), (key1361, -2), (key1373, -2), (key1361, -2), (key1487, 2), (key1512, 2), (key1487, 2)]

def rawRow4618 : Integer.Sparse Key := [(key1487, -6), (key1722, 2), (key1713, 2), (key1713, 2), (key1361, 6), (key1740, -2), (key1713, -2), (key1713, -2), (key1373, -2), (key1361, -2), (key1361, -2), (key1512, 2), (key1487, 2), (key1487, 2)]

def rawRow4619 : Integer.Sparse Key := [(key1722, -6), (key1487, 2), (key1713, 2), (key1713, 2), (key1740, 6), (key1361, -2), (key1713, -2), (key1713, -2), (key1512, -2), (key1740, -2), (key1740, -2), (key1373, 2), (key1722, 2), (key1722, 2)]

def rawRow4620 : Integer.Sparse Key := [(key1722, -6), (key1713, 2), (key1487, 2), (key1713, 2), (key1740, 6), (key1713, -2), (key1361, -2), (key1713, -2), (key1740, -2), (key1512, -2), (key1740, -2), (key1722, 2), (key1373, 2), (key1722, 2)]

def rawRow4621 : Integer.Sparse Key := [(key1722, -6), (key1713, 2), (key1713, 2), (key1487, 2), (key1740, 6), (key1713, -2), (key1713, -2), (key1361, -2), (key1740, -2), (key1740, -2), (key1512, -2), (key1722, 2), (key1722, 2), (key1373, 2)]

def rawRow4623 : Integer.Sparse Key := [(key1740, -6), (key1512, 2), (key1740, 2), (key1740, 2), (key1722, 6), (key1373, -2), (key1722, -2), (key1722, -2), (key1487, -2), (key1713, -2), (key1713, -2), (key1361, 2), (key1713, 2), (key1713, 2)]

def rawRow4624 : Integer.Sparse Key := [(key1740, -6), (key1740, 2), (key1512, 2), (key1740, 2), (key1722, 6), (key1722, -2), (key1373, -2), (key1722, -2), (key1713, -2), (key1487, -2), (key1713, -2), (key1713, 2), (key1361, 2), (key1713, 2)]

def rawRow4625 : Integer.Sparse Key := [(key1740, -6), (key1740, 2), (key1740, 2), (key1512, 2), (key1722, 6), (key1722, -2), (key1722, -2), (key1373, -2), (key1713, -2), (key1713, -2), (key1487, -2), (key1713, 2), (key1713, 2), (key1361, 2)]

def rawRow4626 : Integer.Sparse Key := [(key351, -1), (key354, -1), (key351, -1), (key371, -1), (key354, -1), (key371, -1), (key354, 2), (key354, 2), (key371, 2), (key508, 1), (key511, 1), (key508, 1), (key543, 1), (key511, 1), (key543, 1), (key511, -1), (key523, -1), (key511, -1), (key543, -1), (key523, -1), (key543, -1), (key668, -2), (key668, -2), (key678, -2), (key668, 1), (key672, 1), (key668, 1), (key678, 1), (key672, 1), (key678, 1)]

def rawRow4627 : Integer.Sparse Key := [(key354, -1), (key351, -1), (key371, -1), (key351, -1), (key371, -1), (key354, -1), (key354, 2), (key371, 2), (key354, 2), (key511, 1), (key508, 1), (key543, 1), (key508, 1), (key543, 1), (key511, 1), (key523, -1), (key511, -1), (key543, -1), (key511, -1), (key543, -1), (key523, -1), (key668, -2), (key678, -2), (key668, -2), (key672, 1), (key668, 1), (key678, 1), (key668, 1), (key678, 1), (key672, 1)]

def rawRow4628 : Integer.Sparse Key := [(key371, -1), (key371, -1), (key354, -1), (key354, -1), (key351, -1), (key351, -1), (key371, 2), (key354, 2), (key354, 2), (key543, 1), (key543, 1), (key511, 1), (key511, 1), (key508, 1), (key508, 1), (key543, -1), (key543, -1), (key523, -1), (key523, -1), (key511, -1), (key511, -1), (key678, -2), (key668, -2), (key668, -2), (key678, 1), (key678, 1), (key672, 1), (key672, 1), (key668, 1), (key668, 1)]

def rawRow4630 : Integer.Sparse Key := [(key439, -1), (key443, -1), (key439, -1), (key596, -1), (key443, -1), (key596, -1), (key458, 2), (key458, 2), (key607, 2), (key351, 1), (key354, 1), (key351, 1), (key371, 1), (key354, 1), (key371, 1), (key668, -1), (key672, -1), (key668, -1), (key678, -1), (key672, -1), (key678, -1), (key354, -2), (key354, -2), (key371, -2), (key511, 1), (key523, 1), (key511, 1), (key543, 1), (key523, 1), (key543, 1)]

def rawRow4631 : Integer.Sparse Key := [(key443, -1), (key439, -1), (key596, -1), (key439, -1), (key596, -1), (key443, -1), (key458, 2), (key607, 2), (key458, 2), (key354, 1), (key351, 1), (key371, 1), (key351, 1), (key371, 1), (key354, 1), (key672, -1), (key668, -1), (key678, -1), (key668, -1), (key678, -1), (key672, -1), (key354, -2), (key371, -2), (key354, -2), (key523, 1), (key511, 1), (key543, 1), (key511, 1), (key543, 1), (key523, 1)]

def rawRow4632 : Integer.Sparse Key := [(key596, -1), (key596, -1), (key443, -1), (key443, -1), (key439, -1), (key439, -1), (key607, 2), (key458, 2), (key458, 2), (key371, 1), (key371, 1), (key354, 1), (key354, 1), (key351, 1), (key351, 1), (key678, -1), (key678, -1), (key672, -1), (key672, -1), (key668, -1), (key668, -1), (key371, -2), (key354, -2), (key354, -2), (key543, 1), (key543, 1), (key523, 1), (key523, 1), (key511, 1), (key511, 1)]

def rawRow4633 : Integer.Sparse Key := [(key261, -1), (key261, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key257, 2), (key439, 2), (key439, 2), (key272, 1), (key272, 1), (key470, 1), (key470, 1), (key481, 1), (key481, 1), (key282, -1), (key282, -1), (key351, -1), (key351, -1), (key508, -1), (key508, -1), (key295, -2), (key523, -2), (key523, -2), (key285, 1), (key285, 1), (key354, 1), (key354, 1), (key511, 1), (key511, 1)]

def rawRow4634 : Integer.Sparse Key := [(key443, -1), (key458, -1), (key261, -1), (key458, -1), (key261, -1), (key443, -1), (key439, 2), (key257, 2), (key439, 2), (key470, 1), (key481, 1), (key272, 1), (key481, 1), (key272, 1), (key470, 1), (key351, -1), (key508, -1), (key282, -1), (key508, -1), (key282, -1), (key351, -1), (key523, -2), (key295, -2), (key523, -2), (key354, 1), (key511, 1), (key285, 1), (key511, 1), (key285, 1), (key354, 1)]

def rawRow4635 : Integer.Sparse Key := [(key458, -1), (key443, -1), (key458, -1), (key261, -1), (key443, -1), (key261, -1), (key439, 2), (key439, 2), (key257, 2), (key481, 1), (key470, 1), (key481, 1), (key272, 1), (key470, 1), (key272, 1), (key508, -1), (key351, -1), (key508, -1), (key282, -1), (key351, -1), (key282, -1), (key523, -2), (key523, -2), (key295, -2), (key511, 1), (key354, 1), (key511, 1), (key285, 1), (key354, 1), (key285, 1)]

def rawRow4637 : Integer.Sparse Key := [(key272, -1), (key272, -1), (key470, -1), (key470, -1), (key481, -1), (key481, -1), (key272, 2), (key470, 2), (key470, 2), (key261, 1), (key261, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1), (key261, -1), (key261, -1), (key398, -1), (key398, -1), (key443, -1), (key443, -1), (key282, -2), (key508, -2), (key508, -2), (key282, 1), (key282, 1), (key351, 1), (key351, 1), (key508, 1), (key508, 1)]

def rawRow4638 : Integer.Sparse Key := [(key470, -1), (key481, -1), (key272, -1), (key481, -1), (key272, -1), (key470, -1), (key470, 2), (key272, 2), (key470, 2), (key443, 1), (key458, 1), (key261, 1), (key458, 1), (key261, 1), (key443, 1), (key398, -1), (key443, -1), (key261, -1), (key443, -1), (key261, -1), (key398, -1), (key508, -2), (key282, -2), (key508, -2), (key351, 1), (key508, 1), (key282, 1), (key508, 1), (key282, 1), (key351, 1)]

def rawRow4639 : Integer.Sparse Key := [(key481, -1), (key470, -1), (key481, -1), (key272, -1), (key470, -1), (key272, -1), (key470, 2), (key470, 2), (key272, 2), (key458, 1), (key443, 1), (key458, 1), (key261, 1), (key443, 1), (key261, 1), (key443, -1), (key398, -1), (key443, -1), (key261, -1), (key398, -1), (key261, -1), (key508, -2), (key508, -2), (key282, -2), (key508, 1), (key351, 1), (key508, 1), (key282, 1), (key351, 1), (key282, 1)]

def rawRow4640 : Integer.Sparse Key := [(key1502, -2), (key1508, -2), (key1508, -2), (key1504, 2), (key1508, 2), (key1508, 2), (key1734, 2), (key1737, 2), (key1737, 2), (key1737, -6), (key1945, -2), (key1947, -2), (key1947, -2), (key1947, 6)]

def rawRow4641 : Integer.Sparse Key := [(key1508, -2), (key1502, -2), (key1508, -2), (key1508, 2), (key1504, 2), (key1508, 2), (key1737, 2), (key1734, 2), (key1737, 2), (key1737, -6), (key1947, -2), (key1945, -2), (key1947, -2), (key1947, 6)]

def rawRow4642 : Integer.Sparse Key := [(key1508, -2), (key1508, -2), (key1502, -2), (key1508, 2), (key1508, 2), (key1504, 2), (key1737, 2), (key1737, 2), (key1734, 2), (key1737, -6), (key1947, -2), (key1947, -2), (key1945, -2), (key1947, 6)]

def rawRow4644 : Integer.Sparse Key := [(key1734, -2), (key1737, -2), (key1737, -2), (key1945, 2), (key1947, 2), (key1947, 2), (key1502, 2), (key1508, 2), (key1508, 2), (key1947, -6), (key1504, -2), (key1508, -2), (key1508, -2), (key1737, 6)]

def rawRow4645 : Integer.Sparse Key := [(key1737, -2), (key1734, -2), (key1737, -2), (key1947, 2), (key1945, 2), (key1947, 2), (key1508, 2), (key1502, 2), (key1508, 2), (key1947, -6), (key1508, -2), (key1504, -2), (key1508, -2), (key1737, 6)]

def rawRow4646 : Integer.Sparse Key := [(key1737, -2), (key1737, -2), (key1734, -2), (key1947, 2), (key1947, 2), (key1945, 2), (key1508, 2), (key1508, 2), (key1502, 2), (key1947, -6), (key1508, -2), (key1508, -2), (key1504, -2), (key1737, 6)]

def rawRow4647 : Integer.Sparse Key := [(key1504, -2), (key1504, -2), (key1945, -2), (key1502, 2), (key1502, 2), (key1734, 2), (key1508, 2), (key1508, 2), (key1947, 2), (key1502, -6), (key1508, -2), (key1508, -2), (key1737, -2), (key1504, 6)]

def rawRow4648 : Integer.Sparse Key := [(key1504, -2), (key1945, -2), (key1504, -2), (key1502, 2), (key1734, 2), (key1502, 2), (key1508, 2), (key1947, 2), (key1508, 2), (key1502, -6), (key1508, -2), (key1737, -2), (key1508, -2), (key1504, 6)]

def rawRow4649 : Integer.Sparse Key := [(key1945, -2), (key1504, -2), (key1504, -2), (key1734, 2), (key1502, 2), (key1502, 2), (key1947, 2), (key1508, 2), (key1508, 2), (key1502, -6), (key1737, -2), (key1508, -2), (key1508, -2), (key1504, 6)]

def rawRow4651 : Integer.Sparse Key := [(key1508, -2), (key1508, -2), (key1947, -2), (key1508, 2), (key1508, 2), (key1737, 2), (key1504, 2), (key1504, 2), (key1945, 2), (key1504, -6), (key1502, -2), (key1502, -2), (key1734, -2), (key1502, 6)]

def rawRow4652 : Integer.Sparse Key := [(key1508, -2), (key1947, -2), (key1508, -2), (key1508, 2), (key1737, 2), (key1508, 2), (key1504, 2), (key1945, 2), (key1504, 2), (key1504, -6), (key1502, -2), (key1734, -2), (key1502, -2), (key1502, 6)]

def rawRow4653 : Integer.Sparse Key := [(key1947, -2), (key1508, -2), (key1508, -2), (key1737, 2), (key1508, 2), (key1508, 2), (key1945, 2), (key1504, 2), (key1504, 2), (key1504, -6), (key1734, -2), (key1502, -2), (key1502, -2), (key1502, 6)]

def rawRow4654 : Integer.Sparse Key := [(key257, -2), (key261, -2), (key261, -2), (key257, 1), (key261, 1), (key257, 1), (key295, 1), (key285, 1), (key295, 1), (key351, 2), (key354, 2), (key354, 2), (key351, -1), (key354, -1), (key351, -1), (key371, -1), (key354, -1), (key371, -1), (key508, -1), (key511, -1), (key508, -1), (key523, -1), (key511, -1), (key523, -1), (key508, 1), (key511, 1), (key508, 1), (key543, 1), (key511, 1), (key543, 1)]

def rawRow4655 : Integer.Sparse Key := [(key261, -2), (key257, -2), (key261, -2), (key261, 1), (key257, 1), (key272, 1), (key282, 1), (key295, 1), (key285, 1), (key354, 2), (key351, 2), (key354, 2), (key354, -1), (key351, -1), (key371, -1), (key351, -1), (key371, -1), (key354, -1), (key511, -1), (key508, -1), (key523, -1), (key508, -1), (key523, -1), (key511, -1), (key511, 1), (key508, 1), (key543, 1), (key508, 1), (key543, 1), (key511, 1)]

def rawRow4656 : Integer.Sparse Key := [(key261, -2), (key261, -2), (key257, -2), (key272, 1), (key272, 1), (key261, 1), (key261, 1), (key282, 1), (key282, 1), (key354, 2), (key354, 2), (key351, 2), (key371, -1), (key371, -1), (key354, -1), (key354, -1), (key351, -1), (key351, -1), (key523, -1), (key523, -1), (key511, -1), (key511, -1), (key508, -1), (key508, -1), (key543, 1), (key543, 1), (key511, 1), (key511, 1), (key508, 1), (key508, 1)]

def rawRow4658 : Integer.Sparse Key := [(key394, -2), (key398, -2), (key398, -2), (key439, 1), (key443, 1), (key439, 1), (key470, 1), (key443, 1), (key470, 1), (key257, 2), (key261, 2), (key261, 2), (key439, -1), (key443, -1), (key439, -1), (key596, -1), (key443, -1), (key596, -1), (key257, -1), (key261, -1), (key257, -1), (key295, -1), (key285, -1), (key295, -1), (key351, 1), (key354, 1), (key351, 1), (key371, 1), (key354, 1), (key371, 1)]

def rawRow4659 : Integer.Sparse Key := [(key398, -2), (key394, -2), (key398, -2), (key443, 1), (key439, 1), (key470, 1), (key439, 1), (key470, 1), (key443, 1), (key261, 2), (key257, 2), (key261, 2), (key443, -1), (key439, -1), (key596, -1), (key439, -1), (key596, -1), (key443, -1), (key261, -1), (key257, -1), (key272, -1), (key282, -1), (key295, -1), (key285, -1), (key354, 1), (key351, 1), (key371, 1), (key351, 1), (key371, 1), (key354, 1)]

def rawRow4660 : Integer.Sparse Key := [(key398, -2), (key398, -2), (key394, -2), (key470, 1), (key470, 1), (key443, 1), (key443, 1), (key439, 1), (key439, 1), (key261, 2), (key261, 2), (key257, 2), (key596, -1), (key596, -1), (key443, -1), (key443, -1), (key439, -1), (key439, -1), (key272, -1), (key272, -1), (key261, -1), (key261, -1), (key282, -1), (key282, -1), (key371, 1), (key371, 1), (key354, 1), (key354, 1), (key351, 1), (key351, 1)]

def rawRow4661 : Integer.Sparse Key := [(key470, -2), (key470, -2), (key481, -2), (key398, 1), (key398, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1), (key596, 2), (key596, 2), (key607, 2), (key261, -1), (key261, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key573, -1), (key573, -1), (key596, -1), (key596, -1), (key607, -1), (key607, -1), (key272, 1), (key272, 1), (key470, 1), (key470, 1), (key481, 1), (key481, 1)]

def rawRow4662 : Integer.Sparse Key := [(key470, -2), (key481, -2), (key470, -2), (key443, 1), (key458, 1), (key398, 1), (key458, 1), (key398, 1), (key443, 1), (key596, 2), (key607, 2), (key596, 2), (key443, -1), (key458, -1), (key261, -1), (key458, -1), (key261, -1), (key443, -1), (key596, -1), (key607, -1), (key573, -1), (key607, -1), (key573, -1), (key596, -1), (key470, 1), (key481, 1), (key272, 1), (key481, 1), (key272, 1), (key470, 1)]

def rawRow4663 : Integer.Sparse Key := [(key481, -2), (key470, -2), (key470, -2), (key458, 1), (key443, 1), (key458, 1), (key398, 1), (key443, 1), (key398, 1), (key607, 2), (key596, 2), (key596, 2), (key458, -1), (key443, -1), (key458, -1), (key261, -1), (key443, -1), (key261, -1), (key607, -1), (key596, -1), (key607, -1), (key573, -1), (key596, -1), (key573, -1), (key481, 1), (key470, 1), (key481, 1), (key272, 1), (key470, 1), (key272, 1)]

def rawRow4665 : Integer.Sparse Key := [(key596, -2), (key596, -2), (key607, -2), (key573, 1), (key573, 1), (key596, 1), (key596, 1), (key607, 1), (key607, 1), (key470, 2), (key470, 2), (key481, 2), (key272, -1), (key272, -1), (key470, -1), (key470, -1), (key481, -1), (key481, -1), (key398, -1), (key398, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key261, 1), (key261, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1)]

def rawRow4666 : Integer.Sparse Key := [(key596, -2), (key607, -2), (key596, -2), (key596, 1), (key607, 1), (key573, 1), (key607, 1), (key573, 1), (key596, 1), (key470, 2), (key481, 2), (key470, 2), (key470, -1), (key481, -1), (key272, -1), (key481, -1), (key272, -1), (key470, -1), (key443, -1), (key458, -1), (key398, -1), (key458, -1), (key398, -1), (key443, -1), (key443, 1), (key458, 1), (key261, 1), (key458, 1), (key261, 1), (key443, 1)]

def rawRow4667 : Integer.Sparse Key := [(key607, -2), (key596, -2), (key596, -2), (key607, 1), (key596, 1), (key607, 1), (key573, 1), (key596, 1), (key573, 1), (key481, 2), (key470, 2), (key470, 2), (key481, -1), (key470, -1), (key481, -1), (key272, -1), (key470, -1), (key272, -1), (key458, -1), (key443, -1), (key458, -1), (key398, -1), (key443, -1), (key398, -1), (key458, 1), (key443, 1), (key458, 1), (key261, 1), (key443, 1), (key261, 1)]

def rawRow4668 : Integer.Sparse Key := [(key223, -2), (key226, -2), (key226, -2), (key226, 6), (key495, 2), (key498, 2), (key498, 2), (key498, -2), (key498, -2), (key552, -2), (key620, -6), (key620, 2), (key620, 2), (key646, 2)]

def rawRow4669 : Integer.Sparse Key := [(key226, -2), (key223, -2), (key226, -2), (key226, 6), (key498, 2), (key495, 2), (key498, 2), (key498, -2), (key552, -2), (key498, -2), (key620, -6), (key620, 2), (key646, 2), (key620, 2)]

def rawRow4670 : Integer.Sparse Key := [(key226, -2), (key226, -2), (key223, -2), (key226, 6), (key498, 2), (key498, 2), (key495, 2), (key552, -2), (key498, -2), (key498, -2), (key620, -6), (key646, 2), (key620, 2), (key620, 2)]

def rawRow4672 : Integer.Sparse Key := [(key495, -2), (key498, -2), (key498, -2), (key620, 6), (key223, 2), (key226, 2), (key226, 2), (key620, -2), (key620, -2), (key646, -2), (key226, -6), (key498, 2), (key498, 2), (key552, 2)]

def rawRow4673 : Integer.Sparse Key := [(key498, -2), (key495, -2), (key498, -2), (key620, 6), (key226, 2), (key223, 2), (key226, 2), (key620, -2), (key646, -2), (key620, -2), (key226, -6), (key498, 2), (key552, 2), (key498, 2)]

def rawRow4674 : Integer.Sparse Key := [(key498, -2), (key498, -2), (key495, -2), (key620, 6), (key226, 2), (key226, 2), (key223, 2), (key646, -2), (key620, -2), (key620, -2), (key226, -6), (key552, 2), (key498, 2), (key498, 2)]

def rawRow4675 : Integer.Sparse Key := [(key498, -2), (key498, -2), (key620, -2), (key495, 6), (key552, 2), (key552, 2), (key646, 2), (key223, -2), (key495, -2), (key495, -2), (key552, -6), (key226, 2), (key498, 2), (key498, 2)]

def rawRow4676 : Integer.Sparse Key := [(key498, -2), (key620, -2), (key498, -2), (key495, 6), (key552, 2), (key646, 2), (key552, 2), (key495, -2), (key223, -2), (key495, -2), (key552, -6), (key498, 2), (key226, 2), (key498, 2)]

def rawRow4677 : Integer.Sparse Key := [(key620, -2), (key498, -2), (key498, -2), (key495, 6), (key646, 2), (key552, 2), (key552, 2), (key495, -2), (key495, -2), (key223, -2), (key552, -6), (key498, 2), (key498, 2), (key226, 2)]

def rawRow4679 : Integer.Sparse Key := [(key552, -2), (key552, -2), (key646, -2), (key552, 6), (key498, 2), (key498, 2), (key620, 2), (key226, -2), (key498, -2), (key498, -2), (key495, -6), (key223, 2), (key495, 2), (key495, 2)]

def rawRow4680 : Integer.Sparse Key := [(key552, -2), (key646, -2), (key552, -2), (key552, 6), (key498, 2), (key620, 2), (key498, 2), (key498, -2), (key226, -2), (key498, -2), (key495, -6), (key495, 2), (key223, 2), (key495, 2)]

def rawRow4681 : Integer.Sparse Key := [(key646, -2), (key552, -2), (key552, -2), (key552, 6), (key620, 2), (key498, 2), (key498, 2), (key498, -2), (key498, -2), (key226, -2), (key495, -6), (key495, 2), (key495, 2), (key223, 2)]

def rawRow4682 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1379, -2), (key1366, 1), (key1370, 1), (key1366, 1), (key1379, 1), (key1370, 1), (key1379, 1), (key1718, 2), (key1718, 2), (key1728, 2), (key1718, -1), (key1728, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1747, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1870, -1), (key1865, -1), (key1870, -1), (key1863, 1), (key1870, 1), (key1863, 1), (key1880, 1), (key1870, 1), (key1880, 1)]

def rawRow4683 : Integer.Sparse Key := [(key1366, -2), (key1379, -2), (key1366, -2), (key1370, 1), (key1366, 1), (key1379, 1), (key1366, 1), (key1379, 1), (key1370, 1), (key1718, 2), (key1728, 2), (key1718, 2), (key1728, -1), (key1718, -1), (key1747, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1865, -1), (key1863, -1), (key1870, -1), (key1863, -1), (key1870, -1), (key1865, -1), (key1870, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1870, 1)]

def rawRow4684 : Integer.Sparse Key := [(key1379, -2), (key1366, -2), (key1366, -2), (key1379, 1), (key1379, 1), (key1370, 1), (key1370, 1), (key1366, 1), (key1366, 1), (key1728, 2), (key1718, 2), (key1718, 2), (key1747, -1), (key1747, -1), (key1728, -1), (key1728, -1), (key1718, -1), (key1718, -1), (key1870, -1), (key1870, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, 1), (key1880, 1), (key1870, 1), (key1870, 1), (key1863, 1), (key1863, 1)]

def rawRow4686 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1728, -2), (key1863, 1), (key1865, 1), (key1863, 1), (key1870, 1), (key1865, 1), (key1870, 1), (key1366, 2), (key1366, 2), (key1379, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1366, -1), (key1370, -1), (key1366, -1), (key1379, -1), (key1370, -1), (key1379, -1), (key1718, 1), (key1728, 1), (key1718, 1), (key1747, 1), (key1728, 1), (key1747, 1)]

def rawRow4687 : Integer.Sparse Key := [(key1718, -2), (key1728, -2), (key1718, -2), (key1865, 1), (key1863, 1), (key1870, 1), (key1863, 1), (key1870, 1), (key1865, 1), (key1366, 2), (key1379, 2), (key1366, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1370, -1), (key1366, -1), (key1379, -1), (key1366, -1), (key1379, -1), (key1370, -1), (key1728, 1), (key1718, 1), (key1747, 1), (key1718, 1), (key1747, 1), (key1728, 1)]

def rawRow4688 : Integer.Sparse Key := [(key1728, -2), (key1718, -2), (key1718, -2), (key1870, 1), (key1870, 1), (key1865, 1), (key1865, 1), (key1863, 1), (key1863, 1), (key1379, 2), (key1366, 2), (key1366, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1379, -1), (key1379, -1), (key1370, -1), (key1370, -1), (key1366, -1), (key1366, -1), (key1747, 1), (key1747, 1), (key1728, 1), (key1728, 1), (key1718, 1), (key1718, 1)]

def rawRow4689 : Integer.Sparse Key := [(key1496, -2), (key1865, -2), (key1865, -2), (key1492, 1), (key1492, 1), (key1718, 1), (key1718, 1), (key1863, 1), (key1863, 1), (key1519, 2), (key1880, 2), (key1880, 2), (key1366, -1), (key1366, -1), (key1492, -1), (key1492, -1), (key1863, -1), (key1863, -1), (key1519, -1), (key1519, -1), (key1747, -1), (key1747, -1), (key1880, -1), (key1880, -1), (key1370, 1), (key1370, 1), (key1496, 1), (key1496, 1), (key1865, 1), (key1865, 1)]

def rawRow4690 : Integer.Sparse Key := [(key1865, -2), (key1496, -2), (key1865, -2), (key1718, 1), (key1863, 1), (key1492, 1), (key1863, 1), (key1492, 1), (key1718, 1), (key1880, 2), (key1519, 2), (key1880, 2), (key1492, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1747, -1), (key1880, -1), (key1519, -1), (key1880, -1), (key1519, -1), (key1747, -1), (key1496, 1), (key1865, 1), (key1370, 1), (key1865, 1), (key1370, 1), (key1496, 1)]

def rawRow4691 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1496, -2), (key1863, 1), (key1718, 1), (key1863, 1), (key1492, 1), (key1718, 1), (key1492, 1), (key1880, 2), (key1880, 2), (key1519, 2), (key1863, -1), (key1492, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1366, -1), (key1880, -1), (key1747, -1), (key1880, -1), (key1519, -1), (key1747, -1), (key1519, -1), (key1865, 1), (key1496, 1), (key1865, 1), (key1370, 1), (key1496, 1), (key1370, 1)]

def rawRow4693 : Integer.Sparse Key := [(key1519, -2), (key1880, -2), (key1880, -2), (key1519, 1), (key1519, 1), (key1747, 1), (key1747, 1), (key1880, 1), (key1880, 1), (key1496, 2), (key1865, 2), (key1865, 2), (key1370, -1), (key1370, -1), (key1496, -1), (key1496, -1), (key1865, -1), (key1865, -1), (key1492, -1), (key1492, -1), (key1718, -1), (key1718, -1), (key1863, -1), (key1863, -1), (key1366, 1), (key1366, 1), (key1492, 1), (key1492, 1), (key1863, 1), (key1863, 1)]

def rawRow4694 : Integer.Sparse Key := [(key1880, -2), (key1519, -2), (key1880, -2), (key1747, 1), (key1880, 1), (key1519, 1), (key1880, 1), (key1519, 1), (key1747, 1), (key1865, 2), (key1496, 2), (key1865, 2), (key1496, -1), (key1865, -1), (key1370, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1718, -1), (key1863, -1), (key1492, -1), (key1863, -1), (key1492, -1), (key1718, -1), (key1492, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1492, 1)]

def rawRow4695 : Integer.Sparse Key := [(key1880, -2), (key1880, -2), (key1519, -2), (key1880, 1), (key1747, 1), (key1880, 1), (key1519, 1), (key1747, 1), (key1519, 1), (key1865, 2), (key1865, 2), (key1496, 2), (key1865, -1), (key1496, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1370, -1), (key1863, -1), (key1718, -1), (key1863, -1), (key1492, -1), (key1718, -1), (key1492, -1), (key1863, 1), (key1492, 1), (key1863, 1), (key1366, 1), (key1492, 1), (key1366, 1)]

def rawRow4696 : Integer.Sparse Key := [(key1276, -2), (key1281, -2), (key1281, -2), (key1281, 6), (key1699, 2), (key1704, 2), (key1704, 2), (key1704, -2), (key1704, -2), (key1753, -2), (key1934, -6), (key1934, 2), (key1934, 2), (key1954, 2)]

def rawRow4697 : Integer.Sparse Key := [(key1281, -2), (key1276, -2), (key1281, -2), (key1281, 6), (key1704, 2), (key1699, 2), (key1704, 2), (key1704, -2), (key1753, -2), (key1704, -2), (key1934, -6), (key1934, 2), (key1954, 2), (key1934, 2)]

def rawRow4698 : Integer.Sparse Key := [(key1281, -2), (key1281, -2), (key1276, -2), (key1281, 6), (key1704, 2), (key1704, 2), (key1699, 2), (key1753, -2), (key1704, -2), (key1704, -2), (key1934, -6), (key1954, 2), (key1934, 2), (key1934, 2)]

def rawRow4700 : Integer.Sparse Key := [(key1699, -2), (key1704, -2), (key1704, -2), (key1934, 6), (key1276, 2), (key1281, 2), (key1281, 2), (key1934, -2), (key1934, -2), (key1954, -2), (key1281, -6), (key1704, 2), (key1704, 2), (key1753, 2)]

def rawRow4701 : Integer.Sparse Key := [(key1704, -2), (key1699, -2), (key1704, -2), (key1934, 6), (key1281, 2), (key1276, 2), (key1281, 2), (key1934, -2), (key1954, -2), (key1934, -2), (key1281, -6), (key1704, 2), (key1753, 2), (key1704, 2)]

def rawRow4702 : Integer.Sparse Key := [(key1704, -2), (key1704, -2), (key1699, -2), (key1934, 6), (key1281, 2), (key1281, 2), (key1276, 2), (key1954, -2), (key1934, -2), (key1934, -2), (key1281, -6), (key1753, 2), (key1704, 2), (key1704, 2)]

def rawRow4703 : Integer.Sparse Key := [(key1704, -2), (key1704, -2), (key1934, -2), (key1699, 6), (key1753, 2), (key1753, 2), (key1954, 2), (key1276, -2), (key1699, -2), (key1699, -2), (key1753, -6), (key1281, 2), (key1704, 2), (key1704, 2)]

def rawRow4704 : Integer.Sparse Key := [(key1704, -2), (key1934, -2), (key1704, -2), (key1699, 6), (key1753, 2), (key1954, 2), (key1753, 2), (key1699, -2), (key1276, -2), (key1699, -2), (key1753, -6), (key1704, 2), (key1281, 2), (key1704, 2)]

def rawRow4705 : Integer.Sparse Key := [(key1934, -2), (key1704, -2), (key1704, -2), (key1699, 6), (key1954, 2), (key1753, 2), (key1753, 2), (key1699, -2), (key1699, -2), (key1276, -2), (key1753, -6), (key1704, 2), (key1704, 2), (key1281, 2)]

def rawRow4707 : Integer.Sparse Key := [(key1753, -2), (key1753, -2), (key1954, -2), (key1753, 6), (key1704, 2), (key1704, 2), (key1934, 2), (key1281, -2), (key1704, -2), (key1704, -2), (key1699, -6), (key1276, 2), (key1699, 2), (key1699, 2)]

def rawRow4708 : Integer.Sparse Key := [(key1753, -2), (key1954, -2), (key1753, -2), (key1753, 6), (key1704, 2), (key1934, 2), (key1704, 2), (key1704, -2), (key1281, -2), (key1704, -2), (key1699, -6), (key1699, 2), (key1276, 2), (key1699, 2)]

def rawRow4709 : Integer.Sparse Key := [(key1954, -2), (key1753, -2), (key1753, -2), (key1753, 6), (key1934, 2), (key1704, 2), (key1704, 2), (key1704, -2), (key1704, -2), (key1281, -2), (key1699, -6), (key1699, 2), (key1699, 2), (key1276, 2)]

def rawRow4710 : Integer.Sparse Key := [(key1276, -2), (key1279, -2), (key1279, -2), (key1279, 6), (key1699, 2), (key1702, 2), (key1702, 2), (key1702, -2), (key1702, -2), (key1752, -2), (key1853, -6), (key1853, 2), (key1853, 2), (key1885, 2)]

def rawRow4711 : Integer.Sparse Key := [(key1279, -2), (key1276, -2), (key1279, -2), (key1279, 6), (key1702, 2), (key1699, 2), (key1702, 2), (key1702, -2), (key1752, -2), (key1702, -2), (key1853, -6), (key1853, 2), (key1885, 2), (key1853, 2)]

def rawRow4712 : Integer.Sparse Key := [(key1279, -2), (key1279, -2), (key1276, -2), (key1279, 6), (key1702, 2), (key1702, 2), (key1699, 2), (key1752, -2), (key1702, -2), (key1702, -2), (key1853, -6), (key1885, 2), (key1853, 2), (key1853, 2)]

def rawRow4714 : Integer.Sparse Key := [(key1699, -2), (key1702, -2), (key1702, -2), (key1853, 6), (key1276, 2), (key1279, 2), (key1279, 2), (key1853, -2), (key1853, -2), (key1885, -2), (key1279, -6), (key1702, 2), (key1702, 2), (key1752, 2)]

def rawRow4715 : Integer.Sparse Key := [(key1702, -2), (key1699, -2), (key1702, -2), (key1853, 6), (key1279, 2), (key1276, 2), (key1279, 2), (key1853, -2), (key1885, -2), (key1853, -2), (key1279, -6), (key1702, 2), (key1752, 2), (key1702, 2)]

def rawRow4716 : Integer.Sparse Key := [(key1702, -2), (key1702, -2), (key1699, -2), (key1853, 6), (key1279, 2), (key1279, 2), (key1276, 2), (key1885, -2), (key1853, -2), (key1853, -2), (key1279, -6), (key1752, 2), (key1702, 2), (key1702, 2)]

def rawRow4717 : Integer.Sparse Key := [(key1702, -2), (key1702, -2), (key1853, -2), (key1699, 6), (key1752, 2), (key1752, 2), (key1885, 2), (key1276, -2), (key1699, -2), (key1699, -2), (key1752, -6), (key1279, 2), (key1702, 2), (key1702, 2)]

def rawRow4718 : Integer.Sparse Key := [(key1702, -2), (key1853, -2), (key1702, -2), (key1699, 6), (key1752, 2), (key1885, 2), (key1752, 2), (key1699, -2), (key1276, -2), (key1699, -2), (key1752, -6), (key1702, 2), (key1279, 2), (key1702, 2)]

def rawRow4719 : Integer.Sparse Key := [(key1853, -2), (key1702, -2), (key1702, -2), (key1699, 6), (key1885, 2), (key1752, 2), (key1752, 2), (key1699, -2), (key1699, -2), (key1276, -2), (key1752, -6), (key1702, 2), (key1702, 2), (key1279, 2)]

def rawRow4721 : Integer.Sparse Key := [(key1752, -2), (key1752, -2), (key1885, -2), (key1752, 6), (key1702, 2), (key1702, 2), (key1853, 2), (key1279, -2), (key1702, -2), (key1702, -2), (key1699, -6), (key1276, 2), (key1699, 2), (key1699, 2)]

def rawRow4722 : Integer.Sparse Key := [(key1752, -2), (key1885, -2), (key1752, -2), (key1752, 6), (key1702, 2), (key1853, 2), (key1702, 2), (key1702, -2), (key1279, -2), (key1702, -2), (key1699, -6), (key1699, 2), (key1276, 2), (key1699, 2)]

def rawRow4723 : Integer.Sparse Key := [(key1885, -2), (key1752, -2), (key1752, -2), (key1752, 6), (key1853, 2), (key1702, 2), (key1702, 2), (key1702, -2), (key1702, -2), (key1279, -2), (key1699, -6), (key1699, 2), (key1699, 2), (key1276, 2)]

def rawRow4724 : Integer.Sparse Key := [(key1362, -2), (key1365, -2), (key1365, -2), (key1362, 1), (key1365, 1), (key1362, 1), (key1375, 1), (key1365, 1), (key1375, 1), (key1488, 2), (key1491, 2), (key1491, 2), (key1488, -1), (key1491, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1514, -1), (key1714, -1), (key1717, -1), (key1714, -1), (key1724, -1), (key1717, -1), (key1724, -1), (key1714, 1), (key1717, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1742, 1)]

def rawRow4725 : Integer.Sparse Key := [(key1365, -2), (key1362, -2), (key1365, -2), (key1365, 1), (key1362, 1), (key1375, 1), (key1362, 1), (key1375, 1), (key1365, 1), (key1491, 2), (key1488, 2), (key1491, 2), (key1491, -1), (key1488, -1), (key1514, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1717, -1), (key1714, -1), (key1724, -1), (key1714, -1), (key1724, -1), (key1717, -1), (key1717, 1), (key1714, 1), (key1742, 1), (key1714, 1), (key1742, 1), (key1717, 1)]

def rawRow4726 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1362, -2), (key1375, 1), (key1375, 1), (key1365, 1), (key1365, 1), (key1362, 1), (key1362, 1), (key1491, 2), (key1491, 2), (key1488, 2), (key1514, -1), (key1514, -1), (key1491, -1), (key1491, -1), (key1488, -1), (key1488, -1), (key1724, -1), (key1724, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1742, 1), (key1742, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1)]

def rawRow4728 : Integer.Sparse Key := [(key1488, -2), (key1491, -2), (key1491, -2), (key1714, 1), (key1717, 1), (key1714, 1), (key1724, 1), (key1717, 1), (key1724, 1), (key1362, 2), (key1365, 2), (key1365, 2), (key1714, -1), (key1717, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1362, -1), (key1365, -1), (key1362, -1), (key1375, -1), (key1365, -1), (key1375, -1), (key1488, 1), (key1491, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1514, 1)]

def rawRow4729 : Integer.Sparse Key := [(key1491, -2), (key1488, -2), (key1491, -2), (key1717, 1), (key1714, 1), (key1724, 1), (key1714, 1), (key1724, 1), (key1717, 1), (key1365, 2), (key1362, 2), (key1365, 2), (key1717, -1), (key1714, -1), (key1742, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1365, -1), (key1362, -1), (key1375, -1), (key1362, -1), (key1375, -1), (key1365, -1), (key1491, 1), (key1488, 1), (key1514, 1), (key1488, 1), (key1514, 1), (key1491, 1)]

def rawRow4730 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1488, -2), (key1724, 1), (key1724, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1), (key1365, 2), (key1365, 2), (key1362, 2), (key1742, -1), (key1742, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1375, -1), (key1375, -1), (key1365, -1), (key1365, -1), (key1362, -1), (key1362, -1), (key1514, 1), (key1514, 1), (key1491, 1), (key1491, 1), (key1488, 1), (key1488, 1)]

def rawRow4731 : Integer.Sparse Key := [(key1724, -2), (key1724, -2), (key1868, -2), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1), (key1742, 2), (key1742, 2), (key1878, 2), (key1365, -1), (key1365, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1514, -1), (key1514, -1), (key1742, -1), (key1742, -1), (key1878, -1), (key1878, -1), (key1375, 1), (key1375, 1), (key1724, 1), (key1724, 1), (key1868, 1), (key1868, 1)]

def rawRow4732 : Integer.Sparse Key := [(key1724, -2), (key1868, -2), (key1724, -2), (key1717, 1), (key1862, 1), (key1491, 1), (key1862, 1), (key1491, 1), (key1717, 1), (key1742, 2), (key1878, 2), (key1742, 2), (key1717, -1), (key1862, -1), (key1365, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1742, -1), (key1878, -1), (key1514, -1), (key1878, -1), (key1514, -1), (key1742, -1), (key1724, 1), (key1868, 1), (key1375, 1), (key1868, 1), (key1375, 1), (key1724, 1)]

def rawRow4733 : Integer.Sparse Key := [(key1868, -2), (key1724, -2), (key1724, -2), (key1862, 1), (key1717, 1), (key1862, 1), (key1491, 1), (key1717, 1), (key1491, 1), (key1878, 2), (key1742, 2), (key1742, 2), (key1862, -1), (key1717, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1878, -1), (key1742, -1), (key1878, -1), (key1514, -1), (key1742, -1), (key1514, -1), (key1868, 1), (key1724, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1375, 1)]

def rawRow4735 : Integer.Sparse Key := [(key1742, -2), (key1742, -2), (key1878, -2), (key1514, 1), (key1514, 1), (key1742, 1), (key1742, 1), (key1878, 1), (key1878, 1), (key1724, 2), (key1724, 2), (key1868, 2), (key1375, -1), (key1375, -1), (key1724, -1), (key1724, -1), (key1868, -1), (key1868, -1), (key1491, -1), (key1491, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1365, 1), (key1365, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4736 : Integer.Sparse Key := [(key1742, -2), (key1878, -2), (key1742, -2), (key1742, 1), (key1878, 1), (key1514, 1), (key1878, 1), (key1514, 1), (key1742, 1), (key1724, 2), (key1868, 2), (key1724, 2), (key1724, -1), (key1868, -1), (key1375, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1717, -1), (key1862, -1), (key1491, -1), (key1862, -1), (key1491, -1), (key1717, -1), (key1717, 1), (key1862, 1), (key1365, 1), (key1862, 1), (key1365, 1), (key1717, 1)]

def rawRow4737 : Integer.Sparse Key := [(key1878, -2), (key1742, -2), (key1742, -2), (key1878, 1), (key1742, 1), (key1878, 1), (key1514, 1), (key1742, 1), (key1514, 1), (key1868, 2), (key1724, 2), (key1724, 2), (key1868, -1), (key1724, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1375, -1), (key1862, -1), (key1717, -1), (key1862, -1), (key1491, -1), (key1717, -1), (key1491, -1), (key1862, 1), (key1717, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1365, 1)]

def rawRow4738 : Integer.Sparse Key := [(key741, -2), (key742, -2), (key742, -2), (key742, 6), (key900, 2), (key901, 2), (key901, 2), (key901, -2), (key901, -2), (key951, -2), (key913, -6), (key913, 2), (key913, 2), (key954, 2)]

def rawRow4739 : Integer.Sparse Key := [(key742, -2), (key741, -2), (key742, -2), (key742, 6), (key901, 2), (key900, 2), (key901, 2), (key901, -2), (key951, -2), (key901, -2), (key913, -6), (key913, 2), (key954, 2), (key913, 2)]

def rawRow4740 : Integer.Sparse Key := [(key742, -2), (key742, -2), (key741, -2), (key742, 6), (key901, 2), (key901, 2), (key900, 2), (key951, -2), (key901, -2), (key901, -2), (key913, -6), (key954, 2), (key913, 2), (key913, 2)]

def rawRow4742 : Integer.Sparse Key := [(key900, -2), (key901, -2), (key901, -2), (key913, 6), (key741, 2), (key742, 2), (key742, 2), (key913, -2), (key913, -2), (key954, -2), (key742, -6), (key901, 2), (key901, 2), (key951, 2)]

def rawRow4743 : Integer.Sparse Key := [(key901, -2), (key900, -2), (key901, -2), (key913, 6), (key742, 2), (key741, 2), (key742, 2), (key913, -2), (key954, -2), (key913, -2), (key742, -6), (key901, 2), (key951, 2), (key901, 2)]

def rawRow4744 : Integer.Sparse Key := [(key901, -2), (key901, -2), (key900, -2), (key913, 6), (key742, 2), (key742, 2), (key741, 2), (key954, -2), (key913, -2), (key913, -2), (key742, -6), (key951, 2), (key901, 2), (key901, 2)]

def rawRow4745 : Integer.Sparse Key := [(key901, -2), (key901, -2), (key913, -2), (key900, 6), (key951, 2), (key951, 2), (key954, 2), (key741, -2), (key900, -2), (key900, -2), (key951, -6), (key742, 2), (key901, 2), (key901, 2)]

def rawRow4746 : Integer.Sparse Key := [(key901, -2), (key913, -2), (key901, -2), (key900, 6), (key951, 2), (key954, 2), (key951, 2), (key900, -2), (key741, -2), (key900, -2), (key951, -6), (key901, 2), (key742, 2), (key901, 2)]

def rawRow4747 : Integer.Sparse Key := [(key913, -2), (key901, -2), (key901, -2), (key900, 6), (key954, 2), (key951, 2), (key951, 2), (key900, -2), (key900, -2), (key741, -2), (key951, -6), (key901, 2), (key901, 2), (key742, 2)]

def rawRow4749 : Integer.Sparse Key := [(key951, -2), (key951, -2), (key954, -2), (key951, 6), (key901, 2), (key901, 2), (key913, 2), (key742, -2), (key901, -2), (key901, -2), (key900, -6), (key741, 2), (key900, 2), (key900, 2)]

def rawRow4750 : Integer.Sparse Key := [(key951, -2), (key954, -2), (key951, -2), (key951, 6), (key901, 2), (key913, 2), (key901, 2), (key901, -2), (key742, -2), (key901, -2), (key900, -6), (key900, 2), (key741, 2), (key900, 2)]

def rawRow4751 : Integer.Sparse Key := [(key954, -2), (key951, -2), (key951, -2), (key951, 6), (key913, 2), (key901, 2), (key901, 2), (key901, -2), (key901, -2), (key742, -2), (key900, -6), (key900, 2), (key900, 2), (key741, 2)]

def rawRow4752 : Integer.Sparse Key := [(key1280, -2), (key1280, -2), (key1284, -2), (key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1703, 2), (key1707, 2), (key1703, -1), (key1707, -1), (key1703, -1), (key1757, -1), (key1707, -1), (key1757, -1), (key1854, -2), (key1856, -2), (key1856, -2), (key1854, 1), (key1856, 1), (key1854, 1), (key1887, 1), (key1856, 1), (key1887, 1)]

def rawRow4753 : Integer.Sparse Key := [(key1280, -2), (key1284, -2), (key1280, -2), (key1284, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1707, 2), (key1703, 2), (key1707, -1), (key1703, -1), (key1757, -1), (key1703, -1), (key1757, -1), (key1707, -1), (key1856, -2), (key1854, -2), (key1856, -2), (key1856, 1), (key1854, 1), (key1887, 1), (key1854, 1), (key1887, 1), (key1856, 1)]

def rawRow4754 : Integer.Sparse Key := [(key1284, -2), (key1280, -2), (key1280, -2), (key1284, 2), (key1284, 2), (key1280, 2), (key1707, 2), (key1703, 2), (key1703, 2), (key1757, -1), (key1757, -1), (key1707, -1), (key1707, -1), (key1703, -1), (key1703, -1), (key1856, -2), (key1856, -2), (key1854, -2), (key1887, 1), (key1887, 1), (key1856, 1), (key1856, 1), (key1854, 1), (key1854, 1)]

def rawRow4756 : Integer.Sparse Key := [(key1703, -2), (key1703, -2), (key1707, -2), (key1854, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1280, 2), (key1284, 2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1280, -2), (key1284, -2), (key1284, -2), (key1703, 1), (key1707, 1), (key1703, 1), (key1757, 1), (key1707, 1), (key1757, 1)]

def rawRow4757 : Integer.Sparse Key := [(key1703, -2), (key1707, -2), (key1703, -2), (key1856, 2), (key1854, 2), (key1856, 2), (key1280, 2), (key1284, 2), (key1280, 2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1284, -2), (key1280, -2), (key1284, -2), (key1707, 1), (key1703, 1), (key1757, 1), (key1703, 1), (key1757, 1), (key1707, 1)]

def rawRow4758 : Integer.Sparse Key := [(key1707, -2), (key1703, -2), (key1703, -2), (key1856, 2), (key1856, 2), (key1854, 2), (key1284, 2), (key1280, 2), (key1280, 2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1284, -2), (key1284, -2), (key1280, -2), (key1757, 1), (key1757, 1), (key1707, 1), (key1707, 1), (key1703, 1), (key1703, 1)]

def rawRow4759 : Integer.Sparse Key := [(key1707, -2), (key1856, -2), (key1856, -2), (key1703, 2), (key1703, 2), (key1854, 2), (key1757, 2), (key1887, 2), (key1887, 2), (key1280, -1), (key1280, -1), (key1703, -1), (key1703, -1), (key1854, -1), (key1854, -1), (key1757, -2), (key1757, -2), (key1887, -2), (key1284, 1), (key1284, 1), (key1707, 1), (key1707, 1), (key1856, 1), (key1856, 1)]

def rawRow4760 : Integer.Sparse Key := [(key1856, -2), (key1707, -2), (key1856, -2), (key1703, 2), (key1854, 2), (key1703, 2), (key1887, 2), (key1757, 2), (key1887, 2), (key1703, -1), (key1854, -1), (key1280, -1), (key1854, -1), (key1280, -1), (key1703, -1), (key1757, -2), (key1887, -2), (key1757, -2), (key1707, 1), (key1856, 1), (key1284, 1), (key1856, 1), (key1284, 1), (key1707, 1)]

def rawRow4761 : Integer.Sparse Key := [(key1856, -2), (key1856, -2), (key1707, -2), (key1854, 2), (key1703, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1757, 2), (key1854, -1), (key1703, -1), (key1854, -1), (key1280, -1), (key1703, -1), (key1280, -1), (key1887, -2), (key1757, -2), (key1757, -2), (key1856, 1), (key1707, 1), (key1856, 1), (key1284, 1), (key1707, 1), (key1284, 1)]

def rawRow4763 : Integer.Sparse Key := [(key1757, -2), (key1887, -2), (key1887, -2), (key1757, 2), (key1757, 2), (key1887, 2), (key1707, 2), (key1856, 2), (key1856, 2), (key1284, -1), (key1284, -1), (key1707, -1), (key1707, -1), (key1856, -1), (key1856, -1), (key1703, -2), (key1703, -2), (key1854, -2), (key1280, 1), (key1280, 1), (key1703, 1), (key1703, 1), (key1854, 1), (key1854, 1)]

def rawRow4764 : Integer.Sparse Key := [(key1887, -2), (key1757, -2), (key1887, -2), (key1757, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1707, -1), (key1856, -1), (key1284, -1), (key1856, -1), (key1284, -1), (key1707, -1), (key1703, -2), (key1854, -2), (key1703, -2), (key1703, 1), (key1854, 1), (key1280, 1), (key1854, 1), (key1280, 1), (key1703, 1)]

def rawRow4765 : Integer.Sparse Key := [(key1887, -2), (key1887, -2), (key1757, -2), (key1887, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1707, 2), (key1856, -1), (key1707, -1), (key1856, -1), (key1284, -1), (key1707, -1), (key1284, -1), (key1854, -2), (key1703, -2), (key1703, -2), (key1854, 1), (key1703, 1), (key1854, 1), (key1280, 1), (key1703, 1), (key1280, 1)]

def rawRow4766 : Integer.Sparse Key := [(key1488, -1), (key1493, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1515, -1), (key1493, 2), (key1493, 2), (key1515, 2), (key1714, 1), (key1719, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1743, 1), (key1719, -1), (key1725, -1), (key1719, -1), (key1743, -1), (key1725, -1), (key1743, -1), (key1938, -2), (key1938, -2), (key1950, -2), (key1938, 1), (key1941, 1), (key1938, 1), (key1950, 1), (key1941, 1), (key1950, 1)]

def rawRow4767 : Integer.Sparse Key := [(key1493, -1), (key1488, -1), (key1515, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1493, 2), (key1515, 2), (key1493, 2), (key1719, 1), (key1714, 1), (key1743, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1725, -1), (key1719, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1725, -1), (key1938, -2), (key1950, -2), (key1938, -2), (key1941, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1950, 1), (key1941, 1)]

def rawRow4768 : Integer.Sparse Key := [(key1515, -1), (key1515, -1), (key1493, -1), (key1493, -1), (key1488, -1), (key1488, -1), (key1515, 2), (key1493, 2), (key1493, 2), (key1743, 1), (key1743, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1), (key1743, -1), (key1743, -1), (key1725, -1), (key1725, -1), (key1719, -1), (key1719, -1), (key1950, -2), (key1938, -2), (key1938, -2), (key1950, 1), (key1950, 1), (key1941, 1), (key1941, 1), (key1938, 1), (key1938, 1)]

def rawRow4770 : Integer.Sparse Key := [(key1714, -1), (key1719, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1488, 1), (key1493, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1515, 1), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1), (key1493, -2), (key1493, -2), (key1515, -2), (key1719, 1), (key1725, 1), (key1719, 1), (key1743, 1), (key1725, 1), (key1743, 1)]

def rawRow4771 : Integer.Sparse Key := [(key1719, -1), (key1714, -1), (key1743, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1493, 1), (key1488, 1), (key1515, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1493, -2), (key1515, -2), (key1493, -2), (key1725, 1), (key1719, 1), (key1743, 1), (key1719, 1), (key1743, 1), (key1725, 1)]

def rawRow4772 : Integer.Sparse Key := [(key1743, -1), (key1743, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1515, 1), (key1515, 1), (key1493, 1), (key1493, 1), (key1488, 1), (key1488, 1), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1), (key1515, -2), (key1493, -2), (key1493, -2), (key1743, 1), (key1743, 1), (key1725, 1), (key1725, 1), (key1719, 1), (key1719, 1)]

def rawRow4773 : Integer.Sparse Key := [(key1367, -1), (key1367, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1362, 2), (key1714, 2), (key1714, 2), (key1376, 1), (key1376, 1), (key1725, 1), (key1725, 1), (key1941, 1), (key1941, 1), (key1362, -1), (key1362, -1), (key1488, -1), (key1488, -1), (key1714, -1), (key1714, -1), (key1376, -2), (key1725, -2), (key1725, -2), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1)]

def rawRow4774 : Integer.Sparse Key := [(key1719, -1), (key1938, -1), (key1367, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1714, 2), (key1362, 2), (key1714, 2), (key1725, 1), (key1941, 1), (key1376, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1488, -1), (key1714, -1), (key1362, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1725, -2), (key1376, -2), (key1725, -2), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1)]

def rawRow4775 : Integer.Sparse Key := [(key1938, -1), (key1719, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1714, 2), (key1714, 2), (key1362, 2), (key1941, 1), (key1725, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1376, 1), (key1714, -1), (key1488, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1362, -1), (key1725, -2), (key1725, -2), (key1376, -2), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1)]

def rawRow4777 : Integer.Sparse Key := [(key1376, -1), (key1376, -1), (key1725, -1), (key1725, -1), (key1941, -1), (key1941, -1), (key1376, 2), (key1725, 2), (key1725, 2), (key1367, 1), (key1367, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1), (key1367, -1), (key1367, -1), (key1493, -1), (key1493, -1), (key1719, -1), (key1719, -1), (key1362, -2), (key1714, -2), (key1714, -2), (key1362, 1), (key1362, 1), (key1488, 1), (key1488, 1), (key1714, 1), (key1714, 1)]

def rawRow4778 : Integer.Sparse Key := [(key1725, -1), (key1941, -1), (key1376, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1725, 2), (key1376, 2), (key1725, 2), (key1719, 1), (key1938, 1), (key1367, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1493, -1), (key1719, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1493, -1), (key1714, -2), (key1362, -2), (key1714, -2), (key1488, 1), (key1714, 1), (key1362, 1), (key1714, 1), (key1362, 1), (key1488, 1)]

def rawRow4779 : Integer.Sparse Key := [(key1941, -1), (key1725, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1376, -1), (key1725, 2), (key1725, 2), (key1376, 2), (key1938, 1), (key1719, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1719, -1), (key1493, -1), (key1719, -1), (key1367, -1), (key1493, -1), (key1367, -1), (key1714, -2), (key1714, -2), (key1362, -2), (key1714, 1), (key1488, 1), (key1714, 1), (key1362, 1), (key1488, 1), (key1362, 1)]

def rawRow4794 : Integer.Sparse Key := [(key351, -1), (key353, -1), (key351, -1), (key370, -1), (key353, -1), (key370, -1), (key353, 2), (key353, 2), (key370, 2), (key508, 1), (key510, 1), (key508, 1), (key542, 1), (key510, 1), (key542, 1), (key510, -1), (key521, -1), (key510, -1), (key542, -1), (key521, -1), (key542, -1), (key628, -2), (key628, -2), (key641, -2), (key628, 1), (key630, 1), (key628, 1), (key641, 1), (key630, 1), (key641, 1)]

def rawRow4795 : Integer.Sparse Key := [(key353, -1), (key351, -1), (key370, -1), (key351, -1), (key370, -1), (key353, -1), (key353, 2), (key370, 2), (key353, 2), (key510, 1), (key508, 1), (key542, 1), (key508, 1), (key542, 1), (key510, 1), (key521, -1), (key510, -1), (key542, -1), (key510, -1), (key542, -1), (key521, -1), (key628, -2), (key641, -2), (key628, -2), (key630, 1), (key628, 1), (key641, 1), (key628, 1), (key641, 1), (key630, 1)]

def rawRow4796 : Integer.Sparse Key := [(key370, -1), (key370, -1), (key353, -1), (key353, -1), (key351, -1), (key351, -1), (key370, 2), (key353, 2), (key353, 2), (key542, 1), (key542, 1), (key510, 1), (key510, 1), (key508, 1), (key508, 1), (key542, -1), (key542, -1), (key521, -1), (key521, -1), (key510, -1), (key510, -1), (key641, -2), (key628, -2), (key628, -2), (key641, 1), (key641, 1), (key630, 1), (key630, 1), (key628, 1), (key628, 1)]

def rawRow4798 : Integer.Sparse Key := [(key508, -1), (key510, -1), (key508, -1), (key542, -1), (key510, -1), (key542, -1), (key628, 2), (key628, 2), (key641, 2), (key351, 1), (key353, 1), (key351, 1), (key370, 1), (key353, 1), (key370, 1), (key628, -1), (key630, -1), (key628, -1), (key641, -1), (key630, -1), (key641, -1), (key353, -2), (key353, -2), (key370, -2), (key510, 1), (key521, 1), (key510, 1), (key542, 1), (key521, 1), (key542, 1)]

def rawRow4799 : Integer.Sparse Key := [(key510, -1), (key508, -1), (key542, -1), (key508, -1), (key542, -1), (key510, -1), (key628, 2), (key641, 2), (key628, 2), (key353, 1), (key351, 1), (key370, 1), (key351, 1), (key370, 1), (key353, 1), (key630, -1), (key628, -1), (key641, -1), (key628, -1), (key641, -1), (key630, -1), (key353, -2), (key370, -2), (key353, -2), (key521, 1), (key510, 1), (key542, 1), (key510, 1), (key542, 1), (key521, 1)]

def rawRow4800 : Integer.Sparse Key := [(key542, -1), (key542, -1), (key510, -1), (key510, -1), (key508, -1), (key508, -1), (key641, 2), (key628, 2), (key628, 2), (key370, 1), (key370, 1), (key353, 1), (key353, 1), (key351, 1), (key351, 1), (key641, -1), (key641, -1), (key630, -1), (key630, -1), (key628, -1), (key628, -1), (key370, -2), (key353, -2), (key353, -2), (key542, 1), (key542, 1), (key521, 1), (key521, 1), (key510, 1), (key510, 1)]

def rawRow4801 : Integer.Sparse Key := [(key284, -1), (key284, -1), (key510, -1), (key510, -1), (key628, -1), (key628, -1), (key282, 2), (key508, 2), (key508, 2), (key293, 1), (key293, 1), (key521, 1), (key521, 1), (key630, 1), (key630, 1), (key282, -1), (key282, -1), (key351, -1), (key351, -1), (key508, -1), (key508, -1), (key293, -2), (key521, -2), (key521, -2), (key284, 1), (key284, 1), (key353, 1), (key353, 1), (key510, 1), (key510, 1)]

def rawRow4802 : Integer.Sparse Key := [(key510, -1), (key628, -1), (key284, -1), (key628, -1), (key284, -1), (key510, -1), (key508, 2), (key282, 2), (key508, 2), (key521, 1), (key630, 1), (key293, 1), (key630, 1), (key293, 1), (key521, 1), (key351, -1), (key508, -1), (key282, -1), (key508, -1), (key282, -1), (key351, -1), (key521, -2), (key293, -2), (key521, -2), (key353, 1), (key510, 1), (key284, 1), (key510, 1), (key284, 1), (key353, 1)]

def rawRow4803 : Integer.Sparse Key := [(key628, -1), (key510, -1), (key628, -1), (key284, -1), (key510, -1), (key284, -1), (key508, 2), (key508, 2), (key282, 2), (key630, 1), (key521, 1), (key630, 1), (key293, 1), (key521, 1), (key293, 1), (key508, -1), (key351, -1), (key508, -1), (key282, -1), (key351, -1), (key282, -1), (key521, -2), (key521, -2), (key293, -2), (key510, 1), (key353, 1), (key510, 1), (key284, 1), (key353, 1), (key284, 1)]

def rawRow4805 : Integer.Sparse Key := [(key293, -1), (key293, -1), (key521, -1), (key521, -1), (key630, -1), (key630, -1), (key293, 2), (key521, 2), (key521, 2), (key284, 1), (key284, 1), (key510, 1), (key510, 1), (key628, 1), (key628, 1), (key284, -1), (key284, -1), (key353, -1), (key353, -1), (key510, -1), (key510, -1), (key282, -2), (key508, -2), (key508, -2), (key282, 1), (key282, 1), (key351, 1), (key351, 1), (key508, 1), (key508, 1)]

def rawRow4806 : Integer.Sparse Key := [(key521, -1), (key630, -1), (key293, -1), (key630, -1), (key293, -1), (key521, -1), (key521, 2), (key293, 2), (key521, 2), (key510, 1), (key628, 1), (key284, 1), (key628, 1), (key284, 1), (key510, 1), (key353, -1), (key510, -1), (key284, -1), (key510, -1), (key284, -1), (key353, -1), (key508, -2), (key282, -2), (key508, -2), (key351, 1), (key508, 1), (key282, 1), (key508, 1), (key282, 1), (key351, 1)]

def rawRow4807 : Integer.Sparse Key := [(key630, -1), (key521, -1), (key630, -1), (key293, -1), (key521, -1), (key293, -1), (key521, 2), (key521, 2), (key293, 2), (key628, 1), (key510, 1), (key628, 1), (key284, 1), (key510, 1), (key284, 1), (key510, -1), (key353, -1), (key510, -1), (key284, -1), (key353, -1), (key284, -1), (key508, -2), (key508, -2), (key282, -2), (key508, 1), (key351, 1), (key508, 1), (key282, 1), (key351, 1), (key282, 1)]

def rawRow4808 : Integer.Sparse Key := [(key1488, -1), (key1491, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1514, -1), (key1491, 2), (key1491, 2), (key1514, 2), (key1714, 1), (key1717, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1742, 1), (key1717, -1), (key1724, -1), (key1717, -1), (key1742, -1), (key1724, -1), (key1742, -1), (key1862, -2), (key1862, -2), (key1878, -2), (key1862, 1), (key1868, 1), (key1862, 1), (key1878, 1), (key1868, 1), (key1878, 1)]

def rawRow4809 : Integer.Sparse Key := [(key1491, -1), (key1488, -1), (key1514, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1491, 2), (key1514, 2), (key1491, 2), (key1717, 1), (key1714, 1), (key1742, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1724, -1), (key1717, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1724, -1), (key1862, -2), (key1878, -2), (key1862, -2), (key1868, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1878, 1), (key1868, 1)]

def rawRow4810 : Integer.Sparse Key := [(key1514, -1), (key1514, -1), (key1491, -1), (key1491, -1), (key1488, -1), (key1488, -1), (key1514, 2), (key1491, 2), (key1491, 2), (key1742, 1), (key1742, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1), (key1742, -1), (key1742, -1), (key1724, -1), (key1724, -1), (key1717, -1), (key1717, -1), (key1878, -2), (key1862, -2), (key1862, -2), (key1878, 1), (key1878, 1), (key1868, 1), (key1868, 1), (key1862, 1), (key1862, 1)]

def rawRow4812 : Integer.Sparse Key := [(key1714, -1), (key1717, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1488, 1), (key1491, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1514, 1), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1), (key1491, -2), (key1491, -2), (key1514, -2), (key1717, 1), (key1724, 1), (key1717, 1), (key1742, 1), (key1724, 1), (key1742, 1)]

def rawRow4813 : Integer.Sparse Key := [(key1717, -1), (key1714, -1), (key1742, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1491, 1), (key1488, 1), (key1514, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1491, -2), (key1514, -2), (key1491, -2), (key1724, 1), (key1717, 1), (key1742, 1), (key1717, 1), (key1742, 1), (key1724, 1)]

def rawRow4814 : Integer.Sparse Key := [(key1742, -1), (key1742, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1514, 1), (key1514, 1), (key1491, 1), (key1491, 1), (key1488, 1), (key1488, 1), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1), (key1514, -2), (key1491, -2), (key1491, -2), (key1742, 1), (key1742, 1), (key1724, 1), (key1724, 1), (key1717, 1), (key1717, 1)]

def rawRow4815 : Integer.Sparse Key := [(key1365, -1), (key1365, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1362, 2), (key1714, 2), (key1714, 2), (key1375, 1), (key1375, 1), (key1724, 1), (key1724, 1), (key1868, 1), (key1868, 1), (key1362, -1), (key1362, -1), (key1488, -1), (key1488, -1), (key1714, -1), (key1714, -1), (key1375, -2), (key1724, -2), (key1724, -2), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1)]

def rawRow4816 : Integer.Sparse Key := [(key1717, -1), (key1862, -1), (key1365, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1714, 2), (key1362, 2), (key1714, 2), (key1724, 1), (key1868, 1), (key1375, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1488, -1), (key1714, -1), (key1362, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1724, -2), (key1375, -2), (key1724, -2), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1)]

def rawRow4817 : Integer.Sparse Key := [(key1862, -1), (key1717, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1714, 2), (key1714, 2), (key1362, 2), (key1868, 1), (key1724, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1375, 1), (key1714, -1), (key1488, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1362, -1), (key1724, -2), (key1724, -2), (key1375, -2), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1)]

def rawRow4819 : Integer.Sparse Key := [(key1375, -1), (key1375, -1), (key1724, -1), (key1724, -1), (key1868, -1), (key1868, -1), (key1375, 2), (key1724, 2), (key1724, 2), (key1365, 1), (key1365, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1), (key1365, -1), (key1365, -1), (key1491, -1), (key1491, -1), (key1717, -1), (key1717, -1), (key1362, -2), (key1714, -2), (key1714, -2), (key1362, 1), (key1362, 1), (key1488, 1), (key1488, 1), (key1714, 1), (key1714, 1)]

def rawRow4820 : Integer.Sparse Key := [(key1724, -1), (key1868, -1), (key1375, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1724, 2), (key1375, 2), (key1724, 2), (key1717, 1), (key1862, 1), (key1365, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1491, -1), (key1717, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1491, -1), (key1714, -2), (key1362, -2), (key1714, -2), (key1488, 1), (key1714, 1), (key1362, 1), (key1714, 1), (key1362, 1), (key1488, 1)]

def rawRow4821 : Integer.Sparse Key := [(key1868, -1), (key1724, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1375, -1), (key1724, 2), (key1724, 2), (key1375, 2), (key1862, 1), (key1717, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1717, -1), (key1491, -1), (key1717, -1), (key1365, -1), (key1491, -1), (key1365, -1), (key1714, -2), (key1714, -2), (key1362, -2), (key1714, 1), (key1488, 1), (key1714, 1), (key1362, 1), (key1488, 1), (key1362, 1)]

def rawRow4822 : Integer.Sparse Key := [(key291, -2), (key294, -2), (key294, -2), (key294, 6), (key518, 2), (key522, 2), (key522, 2), (key522, -2), (key522, -2), (key553, -2), (key631, -6), (key631, 2), (key631, 2), (key647, 2)]

def rawRow4823 : Integer.Sparse Key := [(key294, -2), (key291, -2), (key294, -2), (key294, 6), (key522, 2), (key518, 2), (key522, 2), (key522, -2), (key553, -2), (key522, -2), (key631, -6), (key631, 2), (key647, 2), (key631, 2)]

def rawRow4824 : Integer.Sparse Key := [(key294, -2), (key294, -2), (key291, -2), (key294, 6), (key522, 2), (key522, 2), (key518, 2), (key553, -2), (key522, -2), (key522, -2), (key631, -6), (key647, 2), (key631, 2), (key631, 2)]

def rawRow4826 : Integer.Sparse Key := [(key518, -2), (key522, -2), (key522, -2), (key553, 6), (key291, 2), (key294, 2), (key294, 2), (key631, -2), (key631, -2), (key647, -2), (key294, -6), (key522, 2), (key522, 2), (key553, 2)]

def rawRow4827 : Integer.Sparse Key := [(key522, -2), (key518, -2), (key522, -2), (key553, 6), (key294, 2), (key291, 2), (key294, 2), (key631, -2), (key647, -2), (key631, -2), (key294, -6), (key522, 2), (key553, 2), (key522, 2)]

def rawRow4828 : Integer.Sparse Key := [(key522, -2), (key522, -2), (key518, -2), (key553, 6), (key294, 2), (key294, 2), (key291, 2), (key647, -2), (key631, -2), (key631, -2), (key294, -6), (key553, 2), (key522, 2), (key522, 2)]

def rawRow4829 : Integer.Sparse Key := [(key522, -2), (key522, -2), (key553, -2), (key518, 6), (key631, 2), (key631, 2), (key647, 2), (key291, -2), (key518, -2), (key518, -2), (key553, -6), (key294, 2), (key522, 2), (key522, 2)]

def rawRow4830 : Integer.Sparse Key := [(key522, -2), (key553, -2), (key522, -2), (key518, 6), (key631, 2), (key647, 2), (key631, 2), (key518, -2), (key291, -2), (key518, -2), (key553, -6), (key522, 2), (key294, 2), (key522, 2)]

def rawRow4831 : Integer.Sparse Key := [(key553, -2), (key522, -2), (key522, -2), (key518, 6), (key647, 2), (key631, 2), (key631, 2), (key518, -2), (key518, -2), (key291, -2), (key553, -6), (key522, 2), (key522, 2), (key294, 2)]

def rawRow4833 : Integer.Sparse Key := [(key631, -2), (key631, -2), (key647, -2), (key631, 6), (key522, 2), (key522, 2), (key553, 2), (key294, -2), (key522, -2), (key522, -2), (key518, -6), (key291, 2), (key518, 2), (key518, 2)]

def rawRow4834 : Integer.Sparse Key := [(key631, -2), (key647, -2), (key631, -2), (key631, 6), (key522, 2), (key553, 2), (key522, 2), (key522, -2), (key294, -2), (key522, -2), (key518, -6), (key518, 2), (key291, 2), (key518, 2)]

def rawRow4835 : Integer.Sparse Key := [(key647, -2), (key631, -2), (key631, -2), (key631, 6), (key553, 2), (key522, 2), (key522, 2), (key522, -2), (key522, -2), (key294, -2), (key518, -6), (key518, 2), (key518, 2), (key291, 2)]

def rawRow4836 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2739, 1), (key2739, 1), (key2749, 1), (key2749, 1), (key2751, 1), (key2751, 1), (key2810, 2), (key2833, 2), (key2833, 2), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, -1), (key2915, -1), (key2952, -1), (key2952, -1), (key2962, -1), (key2962, -1), (key2964, -1), (key2964, -1), (key2978, 1), (key2978, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1)]

def rawRow4837 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2749, 1), (key2751, 1), (key2739, 1), (key2751, 1), (key2739, 1), (key2749, 1), (key2833, 2), (key2810, 2), (key2833, 2), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2962, -1), (key2964, -1), (key2952, -1), (key2964, -1), (key2952, -1), (key2962, -1), (key2985, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2978, 1), (key2985, 1)]

def rawRow4838 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2751, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2749, 1), (key2739, 1), (key2833, 2), (key2833, 2), (key2810, 2), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2899, -1), (key2964, -1), (key2962, -1), (key2964, -1), (key2952, -1), (key2962, -1), (key2952, -1), (key2994, 1), (key2985, 1), (key2994, 1), (key2978, 1), (key2985, 1), (key2978, 1)]

def rawRow4839 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2952, 1), (key2952, 1), (key2962, 1), (key2962, 1), (key2964, 1), (key2964, 1), (key2707, 2), (key2730, 2), (key2730, 2), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, -1), (key2994, -1), (key2739, -1), (key2739, -1), (key2749, -1), (key2749, -1), (key2751, -1), (key2751, -1), (key2899, 1), (key2899, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1)]

def rawRow4840 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2962, 1), (key2964, 1), (key2952, 1), (key2964, 1), (key2952, 1), (key2962, 1), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2749, -1), (key2751, -1), (key2739, -1), (key2751, -1), (key2739, -1), (key2749, -1), (key2906, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2899, 1), (key2906, 1)]

def rawRow4841 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2964, 1), (key2962, 1), (key2964, 1), (key2952, 1), (key2962, 1), (key2952, 1), (key2730, 2), (key2730, 2), (key2707, 2), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2978, -1), (key2751, -1), (key2749, -1), (key2751, -1), (key2739, -1), (key2749, -1), (key2739, -1), (key2915, 1), (key2906, 1), (key2915, 1), (key2899, 1), (key2906, 1), (key2899, 1)]

def rawRow4842 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 2), (key1335, 2), (key1389, 6), (key1544, -2), (key1770, -2), (key1770, -2), (key1422, -2), (key1453, -2), (key1453, -2), (key1571, 2), (key1786, 2), (key1786, 2)]

def rawRow4843 : Integer.Sparse Key := [(key1294, -6), (key1335, 2), (key1314, 2), (key1335, 2), (key1389, 6), (key1770, -2), (key1544, -2), (key1770, -2), (key1453, -2), (key1422, -2), (key1453, -2), (key1786, 2), (key1571, 2), (key1786, 2)]

def rawRow4844 : Integer.Sparse Key := [(key1294, -6), (key1335, 2), (key1335, 2), (key1314, 2), (key1389, 6), (key1770, -2), (key1770, -2), (key1544, -2), (key1453, -2), (key1453, -2), (key1422, -2), (key1786, 2), (key1786, 2), (key1571, 2)]

def rawRow4845 : Integer.Sparse Key := [(key1389, -6), (key1422, 2), (key1453, 2), (key1453, 2), (key1294, 6), (key1571, -2), (key1786, -2), (key1786, -2), (key1314, -2), (key1335, -2), (key1335, -2), (key1544, 2), (key1770, 2), (key1770, 2)]

def rawRow4846 : Integer.Sparse Key := [(key1389, -6), (key1453, 2), (key1422, 2), (key1453, 2), (key1294, 6), (key1786, -2), (key1571, -2), (key1786, -2), (key1335, -2), (key1314, -2), (key1335, -2), (key1770, 2), (key1544, 2), (key1770, 2)]

def rawRow4847 : Integer.Sparse Key := [(key1389, -6), (key1453, 2), (key1453, 2), (key1422, 2), (key1294, 6), (key1786, -2), (key1786, -2), (key1571, -2), (key1335, -2), (key1335, -2), (key1314, -2), (key1770, 2), (key1770, 2), (key1544, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4866 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1006, -2), (key1019, 6), (key1033, 2), (key1033, 2), (key1041, 2), (key1127, -2), (key1199, -2), (key1199, -2), (key1076, -6), (key1155, 2), (key1212, 2), (key1212, 2)]

def rawRow4867 : Integer.Sparse Key := [(key998, -2), (key1006, -2), (key998, -2), (key1019, 6), (key1033, 2), (key1041, 2), (key1033, 2), (key1199, -2), (key1127, -2), (key1199, -2), (key1076, -6), (key1212, 2), (key1155, 2), (key1212, 2)]

def rawRow4868 : Integer.Sparse Key := [(key1006, -2), (key998, -2), (key998, -2), (key1019, 6), (key1041, 2), (key1033, 2), (key1033, 2), (key1199, -2), (key1199, -2), (key1127, -2), (key1076, -6), (key1212, 2), (key1212, 2), (key1155, 2)]

def rawRow4869 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1041, -2), (key1076, 6), (key998, 2), (key998, 2), (key1006, 2), (key1155, -2), (key1212, -2), (key1212, -2), (key1019, -6), (key1127, 2), (key1199, 2), (key1199, 2)]

def rawRow4870 : Integer.Sparse Key := [(key1033, -2), (key1041, -2), (key1033, -2), (key1076, 6), (key998, 2), (key1006, 2), (key998, 2), (key1212, -2), (key1155, -2), (key1212, -2), (key1019, -6), (key1199, 2), (key1127, 2), (key1199, 2)]

def rawRow4871 : Integer.Sparse Key := [(key1041, -2), (key1033, -2), (key1033, -2), (key1076, 6), (key1006, 2), (key998, 2), (key998, 2), (key1212, -2), (key1212, -2), (key1155, -2), (key1019, -6), (key1199, 2), (key1199, 2), (key1127, 2)]

def rawRow4878 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 2), (key2639, 2), (key2670, 6), (key2705, -2), (key2725, -2), (key2725, -2), (key2785, -2), (key2793, -2), (key2793, -2), (key2808, 2), (key2828, 2), (key2828, 2)]

def rawRow4879 : Integer.Sparse Key := [(key2615, -6), (key2639, 2), (key2631, 2), (key2639, 2), (key2670, 6), (key2725, -2), (key2705, -2), (key2725, -2), (key2793, -2), (key2785, -2), (key2793, -2), (key2828, 2), (key2808, 2), (key2828, 2)]

def rawRow4880 : Integer.Sparse Key := [(key2615, -6), (key2639, 2), (key2639, 2), (key2631, 2), (key2670, 6), (key2725, -2), (key2725, -2), (key2705, -2), (key2793, -2), (key2793, -2), (key2785, -2), (key2828, 2), (key2828, 2), (key2808, 2)]

def rawRow4881 : Integer.Sparse Key := [(key2670, -6), (key2785, 2), (key2793, 2), (key2793, 2), (key2615, 6), (key2808, -2), (key2828, -2), (key2828, -2), (key2631, -2), (key2639, -2), (key2639, -2), (key2705, 2), (key2725, 2), (key2725, 2)]

def rawRow4882 : Integer.Sparse Key := [(key2670, -6), (key2793, 2), (key2785, 2), (key2793, 2), (key2615, 6), (key2828, -2), (key2808, -2), (key2828, -2), (key2639, -2), (key2631, -2), (key2639, -2), (key2725, 2), (key2705, 2), (key2725, 2)]

def rawRow4883 : Integer.Sparse Key := [(key2670, -6), (key2793, 2), (key2793, 2), (key2785, 2), (key2615, 6), (key2828, -2), (key2828, -2), (key2808, -2), (key2639, -2), (key2639, -2), (key2631, -2), (key2725, 2), (key2725, 2), (key2705, 2)]

def rawRow4890 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1775, -1), (key1775, -1), (key1560, 2), (key1781, 2), (key1781, 2), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1791, 1), (key1791, 1), (key1660, -1), (key1660, -1), (key1818, -1), (key1818, -1), (key1842, -1), (key1842, -1), (key1597, -2), (key1799, -2), (key1799, -2), (key1668, 1), (key1668, 1), (key1826, 1), (key1826, 1), (key1845, 1), (key1845, 1)]

def rawRow4891 : Integer.Sparse Key := [(key1772, -1), (key1775, -1), (key1546, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1781, 2), (key1560, 2), (key1781, 2), (key1788, 1), (key1791, 1), (key1573, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1818, -1), (key1842, -1), (key1660, -1), (key1842, -1), (key1660, -1), (key1818, -1), (key1799, -2), (key1597, -2), (key1799, -2), (key1826, 1), (key1845, 1), (key1668, 1), (key1845, 1), (key1668, 1), (key1826, 1)]

def rawRow4892 : Integer.Sparse Key := [(key1775, -1), (key1772, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1781, 2), (key1781, 2), (key1560, 2), (key1791, 1), (key1788, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1573, 1), (key1842, -1), (key1818, -1), (key1842, -1), (key1660, -1), (key1818, -1), (key1660, -1), (key1799, -2), (key1799, -2), (key1597, -2), (key1845, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1826, 1), (key1668, 1)]

def rawRow4893 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1791, -1), (key1791, -1), (key1597, 2), (key1799, 2), (key1799, 2), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1), (key1668, -1), (key1668, -1), (key1826, -1), (key1826, -1), (key1845, -1), (key1845, -1), (key1560, -2), (key1781, -2), (key1781, -2), (key1660, 1), (key1660, 1), (key1818, 1), (key1818, 1), (key1842, 1), (key1842, 1)]

def rawRow4894 : Integer.Sparse Key := [(key1788, -1), (key1791, -1), (key1573, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1799, 2), (key1597, 2), (key1799, 2), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1826, -1), (key1845, -1), (key1668, -1), (key1845, -1), (key1668, -1), (key1826, -1), (key1781, -2), (key1560, -2), (key1781, -2), (key1818, 1), (key1842, 1), (key1660, 1), (key1842, 1), (key1660, 1), (key1818, 1)]

def rawRow4895 : Integer.Sparse Key := [(key1791, -1), (key1788, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1799, 2), (key1799, 2), (key1597, 2), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1845, -1), (key1826, -1), (key1845, -1), (key1668, -1), (key1826, -1), (key1668, -1), (key1781, -2), (key1781, -2), (key1560, -2), (key1842, 1), (key1818, 1), (key1842, 1), (key1660, 1), (key1818, 1), (key1660, 1)]

def rawRow4908 : Integer.Sparse Key := [(key2693, -2), (key2693, -2), (key3018, -2), (key2695, 2), (key2695, 2), (key2836, 2), (key2719, 2), (key2719, 2), (key3027, 2), (key2733, -6), (key2756, -2), (key2756, -2), (key2924, -2), (key2759, 6)]

def rawRow4909 : Integer.Sparse Key := [(key3055, -2), (key3117, -2), (key2693, -2), (key2695, 2), (key2836, 2), (key2695, 2), (key2719, 2), (key3027, 2), (key2719, 2), (key2733, -6), (key2756, -2), (key2924, -2), (key2756, -2), (key2759, 6)]

def rawRow4910 : Integer.Sparse Key := [(key3117, -2), (key3055, -2), (key2693, -2), (key2836, 2), (key2695, 2), (key2695, 2), (key3027, 2), (key2719, 2), (key2719, 2), (key2733, -6), (key2924, -2), (key2756, -2), (key2756, -2), (key2759, 6)]

def rawRow4911 : Integer.Sparse Key := [(key3070, -2), (key3070, -2), (key3147, -2), (key3074, 2), (key3074, 2), (key3146, 2), (key2693, 2), (key2693, 2), (key3018, 2), (key2759, -6), (key2695, -2), (key2695, -2), (key2836, -2), (key2733, 6)]

def rawRow4912 : Integer.Sparse Key := [(key3070, -2), (key3147, -2), (key3070, -2), (key3074, 2), (key3146, 2), (key3074, 2), (key3055, 2), (key3117, 2), (key2693, 2), (key2759, -6), (key2695, -2), (key2836, -2), (key2695, -2), (key2733, 6)]

def rawRow4913 : Integer.Sparse Key := [(key3147, -2), (key3070, -2), (key3070, -2), (key3146, 2), (key3074, 2), (key3074, 2), (key3117, 2), (key3055, 2), (key2693, 2), (key2759, -6), (key2836, -2), (key2695, -2), (key2695, -2), (key2733, 6)]

def rawRow4914 : Integer.Sparse Key := [(key1296, -2), (key1296, -2), (key1303, -2), (key1316, 1), (key1316, 1), (key1337, 1), (key1337, 1), (key1340, 1), (key1340, 1), (key1391, 2), (key1391, 2), (key1398, 2), (key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1775, -1), (key1775, -1), (key1424, -1), (key1424, -1), (key1455, -1), (key1455, -1), (key1458, -1), (key1458, -1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1791, 1), (key1791, 1)]

def rawRow4915 : Integer.Sparse Key := [(key1296, -2), (key1303, -2), (key1296, -2), (key1337, 1), (key1340, 1), (key1316, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1391, 2), (key1398, 2), (key1391, 2), (key1772, -1), (key1775, -1), (key1546, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1455, -1), (key1458, -1), (key1424, -1), (key1458, -1), (key1424, -1), (key1455, -1), (key1788, 1), (key1791, 1), (key1573, 1), (key1791, 1), (key1573, 1), (key1788, 1)]

def rawRow4916 : Integer.Sparse Key := [(key1303, -2), (key1296, -2), (key1296, -2), (key1340, 1), (key1337, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1316, 1), (key1398, 2), (key1391, 2), (key1391, 2), (key1775, -1), (key1772, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1458, -1), (key1455, -1), (key1458, -1), (key1424, -1), (key1455, -1), (key1424, -1), (key1791, 1), (key1788, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1573, 1)]

def rawRow4917 : Integer.Sparse Key := [(key1391, -2), (key1391, -2), (key1398, -2), (key1424, 1), (key1424, 1), (key1455, 1), (key1455, 1), (key1458, 1), (key1458, 1), (key1296, 2), (key1296, 2), (key1303, 2), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1791, -1), (key1791, -1), (key1316, -1), (key1316, -1), (key1337, -1), (key1337, -1), (key1340, -1), (key1340, -1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1)]

def rawRow4918 : Integer.Sparse Key := [(key1391, -2), (key1398, -2), (key1391, -2), (key1455, 1), (key1458, 1), (key1424, 1), (key1458, 1), (key1424, 1), (key1455, 1), (key1296, 2), (key1303, 2), (key1296, 2), (key1788, -1), (key1791, -1), (key1573, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1337, -1), (key1340, -1), (key1316, -1), (key1340, -1), (key1316, -1), (key1337, -1), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1)]

def rawRow4919 : Integer.Sparse Key := [(key1398, -2), (key1391, -2), (key1391, -2), (key1458, 1), (key1455, 1), (key1458, 1), (key1424, 1), (key1455, 1), (key1424, 1), (key1303, 2), (key1296, 2), (key1296, 2), (key1791, -1), (key1788, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1340, -1), (key1337, -1), (key1340, -1), (key1316, -1), (key1337, -1), (key1316, -1), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1)]

def rawRow4920 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1391, 1), (key1391, 1), (key1455, 1), (key1455, 1), (key1467, 1), (key1467, 1), (key1573, 2), (key1573, 2), (key1597, 2), (key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1799, -1), (key1799, -1), (key1546, -1), (key1546, -1), (key1655, -1), (key1655, -1), (key1668, -1), (key1668, -1), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1)]

def rawRow4921 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1455, 1), (key1467, 1), (key1391, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1573, 2), (key1597, 2), (key1573, 2), (key1788, -1), (key1799, -1), (key1296, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1655, -1), (key1668, -1), (key1546, -1), (key1668, -1), (key1546, -1), (key1655, -1), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1)]

def rawRow4922 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1467, 1), (key1455, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1391, 1), (key1597, 2), (key1573, 2), (key1573, 2), (key1799, -1), (key1788, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1668, -1), (key1655, -1), (key1668, -1), (key1546, -1), (key1655, -1), (key1546, -1), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1)]

def rawRow4923 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1546, 1), (key1546, 1), (key1655, 1), (key1655, 1), (key1668, 1), (key1668, 1), (key1424, 2), (key1424, 2), (key1448, 2), (key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1826, -1), (key1826, -1), (key1391, -1), (key1391, -1), (key1455, -1), (key1455, -1), (key1467, -1), (key1467, -1), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1)]

def rawRow4924 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1655, 1), (key1668, 1), (key1546, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1424, 2), (key1448, 2), (key1424, 2), (key1813, -1), (key1826, -1), (key1316, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1455, -1), (key1467, -1), (key1391, -1), (key1467, -1), (key1391, -1), (key1455, -1), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1)]

def rawRow4925 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1668, 1), (key1655, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1546, 1), (key1448, 2), (key1424, 2), (key1424, 2), (key1826, -1), (key1813, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1467, -1), (key1455, -1), (key1467, -1), (key1391, -1), (key1455, -1), (key1391, -1), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1)]

def rawRow4926 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1005, -2), (key1018, 6), (key1033, 2), (key1033, 2), (key1040, 2), (key1126, -2), (key1198, -2), (key1198, -2), (key1075, -6), (key1154, 2), (key1211, 2), (key1211, 2)]

def rawRow4927 : Integer.Sparse Key := [(key998, -2), (key1005, -2), (key998, -2), (key1018, 6), (key1033, 2), (key1040, 2), (key1033, 2), (key1198, -2), (key1126, -2), (key1198, -2), (key1075, -6), (key1211, 2), (key1154, 2), (key1211, 2)]

def rawRow4928 : Integer.Sparse Key := [(key1005, -2), (key998, -2), (key998, -2), (key1018, 6), (key1040, 2), (key1033, 2), (key1033, 2), (key1198, -2), (key1198, -2), (key1126, -2), (key1075, -6), (key1211, 2), (key1211, 2), (key1154, 2)]

def rawRow4929 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1040, -2), (key1075, 6), (key998, 2), (key998, 2), (key1005, 2), (key1154, -2), (key1211, -2), (key1211, -2), (key1018, -6), (key1126, 2), (key1198, 2), (key1198, 2)]

def rawRow4930 : Integer.Sparse Key := [(key1033, -2), (key1040, -2), (key1033, -2), (key1075, 6), (key998, 2), (key1005, 2), (key998, 2), (key1211, -2), (key1154, -2), (key1211, -2), (key1018, -6), (key1198, 2), (key1126, 2), (key1198, 2)]

def rawRow4931 : Integer.Sparse Key := [(key1040, -2), (key1033, -2), (key1033, -2), (key1075, 6), (key1005, 2), (key998, 2), (key998, 2), (key1211, -2), (key1211, -2), (key1154, -2), (key1018, -6), (key1198, 2), (key1198, 2), (key1126, 2)]

def rawRow4932 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1040, 6), (key1111, 2), (key1111, 2), (key1154, 2), (key1005, -2), (key1192, -2), (key1192, -2), (key1126, -6), (key1018, 2), (key1198, 2), (key1198, 2)]

def rawRow4933 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 6), (key1111, 2), (key1154, 2), (key1111, 2), (key1192, -2), (key1005, -2), (key1192, -2), (key1126, -6), (key1198, 2), (key1018, 2), (key1198, 2)]

def rawRow4934 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1040, 6), (key1154, 2), (key1111, 2), (key1111, 2), (key1192, -2), (key1192, -2), (key1005, -2), (key1126, -6), (key1198, 2), (key1198, 2), (key1018, 2)]

def rawRow4935 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1126, 6), (key1033, 2), (key1033, 2), (key1075, 2), (key1018, -2), (key1198, -2), (key1198, -2), (key1040, -6), (key1005, 2), (key1192, 2), (key1192, 2)]

def rawRow4936 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1126, 6), (key1033, 2), (key1075, 2), (key1033, 2), (key1198, -2), (key1018, -2), (key1198, -2), (key1040, -6), (key1192, 2), (key1005, 2), (key1192, 2)]

def rawRow4937 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1126, 6), (key1075, 2), (key1033, 2), (key1033, 2), (key1198, -2), (key1198, -2), (key1018, -2), (key1040, -6), (key1192, 2), (key1192, 2), (key1005, 2)]

def rawRow4938 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2650, 1), (key2650, 1), (key2655, 1), (key2655, 1), (key2656, 1), (key2656, 1), (key2787, 2), (key2797, 2), (key2797, 2), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, -1), (key2915, -1), (key2940, -1), (key2940, -1), (key2945, -1), (key2945, -1), (key2946, -1), (key2946, -1), (key2978, 1), (key2978, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1)]

def rawRow4939 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2655, 1), (key2656, 1), (key2650, 1), (key2656, 1), (key2650, 1), (key2655, 1), (key2797, 2), (key2787, 2), (key2797, 2), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2945, -1), (key2946, -1), (key2940, -1), (key2946, -1), (key2940, -1), (key2945, -1), (key2985, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2978, 1), (key2985, 1)]

def rawRow4940 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2656, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2655, 1), (key2650, 1), (key2797, 2), (key2797, 2), (key2787, 2), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2899, -1), (key2946, -1), (key2945, -1), (key2946, -1), (key2940, -1), (key2945, -1), (key2940, -1), (key2994, 1), (key2985, 1), (key2994, 1), (key2978, 1), (key2985, 1), (key2978, 1)]

def rawRow4941 : Integer.Sparse Key := [(key2707, -2), (key2739, -2), (key2739, -2), (key2730, 1), (key2730, 1), (key2749, 1), (key2749, 1), (key2751, 1), (key2751, 1), (key2633, 2), (key2643, 2), (key2643, 2), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, -1), (key2994, -1), (key2650, -1), (key2650, -1), (key2655, -1), (key2655, -1), (key2656, -1), (key2656, -1), (key2899, 1), (key2899, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1)]

def rawRow4942 : Integer.Sparse Key := [(key2739, -2), (key2707, -2), (key2739, -2), (key2749, 1), (key2751, 1), (key2730, 1), (key2751, 1), (key2730, 1), (key2749, 1), (key2643, 2), (key2633, 2), (key2643, 2), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2655, -1), (key2656, -1), (key2650, -1), (key2656, -1), (key2650, -1), (key2655, -1), (key2906, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2899, 1), (key2906, 1)]

def rawRow4943 : Integer.Sparse Key := [(key2739, -2), (key2739, -2), (key2707, -2), (key2751, 1), (key2749, 1), (key2751, 1), (key2730, 1), (key2749, 1), (key2730, 1), (key2643, 2), (key2643, 2), (key2633, 2), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2656, -1), (key2650, -1), (key2655, -1), (key2650, -1), (key2915, 1), (key2906, 1), (key2915, 1), (key2899, 1), (key2906, 1), (key2899, 1)]

def rawRow4944 : Integer.Sparse Key := [(key2672, -2), (key2749, -2), (key2749, -2), (key2675, 1), (key2675, 1), (key2739, 1), (key2739, 1), (key2751, 1), (key2751, 1), (key2707, 2), (key2978, 2), (key2978, 2), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2739, -1), (key2739, -1), (key2899, -1), (key2899, -1), (key2999, -1), (key2999, -1), (key2655, 1), (key2655, 1), (key2749, 1), (key2749, 1), (key3004, 1), (key3004, 1)]

def rawRow4945 : Integer.Sparse Key := [(key2749, -2), (key2672, -2), (key2749, -2), (key2739, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, 1), (key2739, 1), (key2978, 2), (key2707, 2), (key2978, 2), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2739, -1), (key2999, -1), (key2739, -1), (key2899, -1), (key2749, 1), (key3004, 1), (key2655, 1), (key3004, 1), (key2655, 1), (key2749, 1)]

def rawRow4946 : Integer.Sparse Key := [(key2749, -2), (key2749, -2), (key2672, -2), (key2751, 1), (key2739, 1), (key2751, 1), (key2675, 1), (key2739, 1), (key2675, 1), (key2978, 2), (key2978, 2), (key2707, 2), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key2999, -1), (key2739, -1), (key2899, -1), (key2739, -1), (key3004, 1), (key2749, 1), (key3004, 1), (key2655, 1), (key2749, 1), (key2655, 1)]

def rawRow4947 : Integer.Sparse Key := [(key2787, -2), (key2906, -2), (key2906, -2), (key2797, 1), (key2797, 1), (key2899, 1), (key2899, 1), (key2915, 1), (key2915, 1), (key2672, 2), (key2749, 2), (key2749, 2), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2675, -1), (key2675, -1), (key2797, -1), (key2797, -1), (key2946, -1), (key2946, -1), (key2643, 1), (key2643, 1), (key2730, 1), (key2730, 1), (key2994, 1), (key2994, 1)]

def rawRow4948 : Integer.Sparse Key := [(key2906, -2), (key2787, -2), (key2906, -2), (key2899, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2899, 1), (key2749, 2), (key2672, 2), (key2749, 2), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2675, -1), (key2946, -1), (key2675, -1), (key2797, -1), (key2730, 1), (key2994, 1), (key2643, 1), (key2994, 1), (key2643, 1), (key2730, 1)]

def rawRow4949 : Integer.Sparse Key := [(key2906, -2), (key2906, -2), (key2787, -2), (key2915, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2899, 1), (key2797, 1), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2946, -1), (key2675, -1), (key2797, -1), (key2675, -1), (key2994, 1), (key2730, 1), (key2994, 1), (key2643, 1), (key2730, 1), (key2643, 1)]

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

def rawRow5188 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1299, 2), (key1311, -1), (key1319, -1), (key1311, 2), (key1327, 2), (key1319, -1), (key1327, -1), (key1352, 2), (key1352, -1), (key1355, -1), (key1386, 1), (key1394, 1), (key1394, -2), (key1419, 1), (key1427, 1), (key1419, -2), (key1445, -2), (key1427, 1), (key1445, 1), (key1473, -2), (key1473, 1), (key1481, 1), (key1541, -1), (key1557, -1), (key1549, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1576, -1), (key1594, -1), (key1617, -1), (key1625, -1), (key1617, 1), (key1634, 1), (key1682, 1), (key1684, 1), (key1682, -1), (key1690, -1)]

def rawRow5189 : Integer.Sparse Key := [(key1299, -1), (key1291, -1), (key1299, 2), (key1319, -1), (key1311, -1), (key1327, 2), (key1311, 2), (key1327, -1), (key1319, -1), (key1352, 2), (key1355, -1), (key1352, -1), (key1394, 1), (key1386, 1), (key1394, -2), (key1427, 1), (key1419, 1), (key1445, -2), (key1419, -2), (key1445, 1), (key1427, 1), (key1473, -2), (key1481, 1), (key1473, 1), (key1557, -1), (key1541, -1), (key1557, 1), (key1549, 1), (key1594, 1), (key1568, 1), (key1594, -1), (key1576, -1), (key1625, -1), (key1617, -1), (key1634, 1), (key1617, 1), (key1684, 1), (key1682, 1), (key1690, -1), (key1682, -1)]

def rawRow5190 : Integer.Sparse Key := [(key1299, -1), (key1299, -1), (key1291, 2), (key1327, -1), (key1327, -1), (key1319, 2), (key1319, 2), (key1311, -1), (key1311, -1), (key1355, 2), (key1352, -1), (key1352, -1), (key1394, 1), (key1394, 1), (key1386, -2), (key1445, 1), (key1445, 1), (key1427, -2), (key1427, -2), (key1419, 1), (key1419, 1), (key1481, -2), (key1473, 1), (key1473, 1), (key1549, -1), (key1549, -1), (key1541, 1), (key1541, 1), (key1576, 1), (key1576, 1), (key1568, -1), (key1568, -1), (key1634, -1), (key1634, -1), (key1625, 1), (key1625, 1), (key1690, 1), (key1690, 1), (key1684, -1), (key1684, -1)]

def rawRow5191 : Integer.Sparse Key := [(key1311, -1), (key1319, -1), (key1352, 2), (key1291, -1), (key1299, -1), (key1311, 2), (key1327, 2), (key1352, -1), (key1355, -1), (key1299, 2), (key1319, -1), (key1327, -1), (key1419, 1), (key1427, 1), (key1473, -2), (key1386, 1), (key1394, 1), (key1419, -2), (key1445, -2), (key1473, 1), (key1481, 1), (key1394, -2), (key1427, 1), (key1445, 1), (key1617, -1), (key1625, -1), (key1682, 1), (key1684, 1), (key1617, 1), (key1634, 1), (key1682, -1), (key1690, -1), (key1541, -1), (key1557, -1), (key1568, 1), (key1594, 1), (key1549, 1), (key1557, 1), (key1576, -1), (key1594, -1)]

def rawRow5192 : Integer.Sparse Key := [(key1319, -1), (key1311, -1), (key1352, 2), (key1299, -1), (key1291, -1), (key1327, 2), (key1311, 2), (key1355, -1), (key1352, -1), (key1299, 2), (key1327, -1), (key1319, -1), (key1427, 1), (key1419, 1), (key1473, -2), (key1394, 1), (key1386, 1), (key1445, -2), (key1419, -2), (key1481, 1), (key1473, 1), (key1394, -2), (key1445, 1), (key1427, 1), (key1625, -1), (key1617, -1), (key1684, 1), (key1682, 1), (key1634, 1), (key1617, 1), (key1690, -1), (key1682, -1), (key1557, -1), (key1541, -1), (key1594, 1), (key1568, 1), (key1557, 1), (key1549, 1), (key1594, -1), (key1576, -1)]

def rawRow5193 : Integer.Sparse Key := [(key1311, -1), (key1352, -1), (key1319, 2), (key1311, -1), (key1352, -1), (key1291, 2), (key1355, 2), (key1299, -1), (key1327, -1), (key1319, 2), (key1299, -1), (key1327, -1), (key1419, 1), (key1473, 1), (key1427, -2), (key1419, 1), (key1473, 1), (key1386, -2), (key1481, -2), (key1394, 1), (key1445, 1), (key1427, -2), (key1394, 1), (key1445, 1), (key1568, -1), (key1684, -1), (key1576, 1), (key1625, 1), (key1541, 1), (key1690, 1), (key1549, -1), (key1634, -1), (key1568, -1), (key1684, -1), (key1541, 1), (key1690, 1), (key1576, 1), (key1625, 1), (key1549, -1), (key1634, -1)]

def rawRow5194 : Integer.Sparse Key := [(key1352, -1), (key1311, -1), (key1319, 2), (key1352, -1), (key1311, -1), (key1355, 2), (key1291, 2), (key1327, -1), (key1299, -1), (key1319, 2), (key1327, -1), (key1299, -1), (key1473, 1), (key1419, 1), (key1427, -2), (key1473, 1), (key1419, 1), (key1481, -2), (key1386, -2), (key1445, 1), (key1394, 1), (key1427, -2), (key1445, 1), (key1394, 1), (key1684, -1), (key1568, -1), (key1625, 1), (key1576, 1), (key1690, 1), (key1541, 1), (key1634, -1), (key1549, -1), (key1684, -1), (key1568, -1), (key1690, 1), (key1541, 1), (key1625, 1), (key1576, 1), (key1634, -1), (key1549, -1)]

def rawRow5195 : Integer.Sparse Key := [(key1319, -1), (key1352, -1), (key1311, 2), (key1327, -1), (key1355, -1), (key1299, 2), (key1352, 2), (key1291, -1), (key1311, -1), (key1327, 2), (key1299, -1), (key1319, -1), (key1427, 1), (key1473, 1), (key1419, -2), (key1445, 1), (key1481, 1), (key1394, -2), (key1473, -2), (key1386, 1), (key1419, 1), (key1445, -2), (key1394, 1), (key1427, 1), (key1576, -1), (key1682, -1), (key1568, 1), (key1617, 1), (key1549, 1), (key1682, 1), (key1541, -1), (key1617, -1), (key1594, -1), (key1690, -1), (key1557, 1), (key1684, 1), (key1594, 1), (key1634, 1), (key1557, -1), (key1625, -1)]

def rawRow5196 : Integer.Sparse Key := [(key1352, -1), (key1319, -1), (key1311, 2), (key1355, -1), (key1327, -1), (key1352, 2), (key1299, 2), (key1311, -1), (key1291, -1), (key1327, 2), (key1319, -1), (key1299, -1), (key1473, 1), (key1427, 1), (key1419, -2), (key1481, 1), (key1445, 1), (key1473, -2), (key1394, -2), (key1419, 1), (key1386, 1), (key1445, -2), (key1427, 1), (key1394, 1), (key1682, -1), (key1576, -1), (key1617, 1), (key1568, 1), (key1682, 1), (key1549, 1), (key1617, -1), (key1541, -1), (key1690, -1), (key1594, -1), (key1684, 1), (key1557, 1), (key1634, 1), (key1594, 1), (key1625, -1), (key1557, -1)]

def rawRow5197 : Integer.Sparse Key := [(key1327, -1), (key1327, -1), (key1355, 2), (key1299, -1), (key1299, -1), (key1319, 2), (key1319, 2), (key1352, -1), (key1352, -1), (key1291, 2), (key1311, -1), (key1311, -1), (key1445, 1), (key1445, 1), (key1481, -2), (key1394, 1), (key1394, 1), (key1427, -2), (key1427, -2), (key1473, 1), (key1473, 1), (key1386, -2), (key1419, 1), (key1419, 1), (key1634, -1), (key1634, -1), (key1690, 1), (key1690, 1), (key1625, 1), (key1625, 1), (key1684, -1), (key1684, -1), (key1549, -1), (key1549, -1), (key1576, 1), (key1576, 1), (key1541, 1), (key1541, 1), (key1568, -1), (key1568, -1)]

def rawRow5198 : Integer.Sparse Key := [(key1327, -1), (key1355, -1), (key1327, 2), (key1319, -1), (key1352, -1), (key1299, 2), (key1352, 2), (key1299, -1), (key1319, -1), (key1311, 2), (key1291, -1), (key1311, -1), (key1445, 1), (key1481, 1), (key1445, -2), (key1427, 1), (key1473, 1), (key1394, -2), (key1473, -2), (key1394, 1), (key1427, 1), (key1419, -2), (key1386, 1), (key1419, 1), (key1594, -1), (key1690, -1), (key1594, 1), (key1634, 1), (key1557, 1), (key1684, 1), (key1557, -1), (key1625, -1), (key1576, -1), (key1682, -1), (key1549, 1), (key1682, 1), (key1568, 1), (key1617, 1), (key1541, -1), (key1617, -1)]

def rawRow5199 : Integer.Sparse Key := [(key1355, -1), (key1327, -1), (key1327, 2), (key1352, -1), (key1319, -1), (key1352, 2), (key1299, 2), (key1319, -1), (key1299, -1), (key1311, 2), (key1311, -1), (key1291, -1), (key1481, 1), (key1445, 1), (key1445, -2), (key1473, 1), (key1427, 1), (key1473, -2), (key1394, -2), (key1427, 1), (key1394, 1), (key1419, -2), (key1419, 1), (key1386, 1), (key1690, -1), (key1594, -1), (key1634, 1), (key1594, 1), (key1684, 1), (key1557, 1), (key1625, -1), (key1557, -1), (key1682, -1), (key1576, -1), (key1682, 1), (key1549, 1), (key1617, 1), (key1568, 1), (key1617, -1), (key1541, -1)]

def rawRow5200 : Integer.Sparse Key := [(key1386, -1), (key1394, -1), (key1394, 2), (key1541, -1), (key1549, -1), (key1541, 2), (key1557, 2), (key1549, -1), (key1557, -1), (key1897, 2), (key1897, -1), (key1900, -1), (key1291, 1), (key1299, 1), (key1299, -2), (key1568, 1), (key1576, 1), (key1568, -2), (key1594, -2), (key1576, 1), (key1594, 1), (key1904, -2), (key1904, 1), (key1912, 1), (key1311, -1), (key1327, -1), (key1319, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1427, -1), (key1445, -1), (key1617, -1), (key1625, -1), (key1617, 1), (key1634, 1), (key1919, 1), (key1921, 1), (key1919, -1), (key1927, -1)]

def rawRow5201 : Integer.Sparse Key := [(key1394, -1), (key1386, -1), (key1394, 2), (key1549, -1), (key1541, -1), (key1557, 2), (key1541, 2), (key1557, -1), (key1549, -1), (key1897, 2), (key1900, -1), (key1897, -1), (key1299, 1), (key1291, 1), (key1299, -2), (key1576, 1), (key1568, 1), (key1594, -2), (key1568, -2), (key1594, 1), (key1576, 1), (key1904, -2), (key1912, 1), (key1904, 1), (key1327, -1), (key1311, -1), (key1327, 1), (key1319, 1), (key1445, 1), (key1419, 1), (key1445, -1), (key1427, -1), (key1625, -1), (key1617, -1), (key1634, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1927, -1), (key1919, -1)]

def rawRow5202 : Integer.Sparse Key := [(key1394, -1), (key1394, -1), (key1386, 2), (key1557, -1), (key1557, -1), (key1549, 2), (key1549, 2), (key1541, -1), (key1541, -1), (key1900, 2), (key1897, -1), (key1897, -1), (key1299, 1), (key1299, 1), (key1291, -2), (key1594, 1), (key1594, 1), (key1576, -2), (key1576, -2), (key1568, 1), (key1568, 1), (key1912, -2), (key1904, 1), (key1904, 1), (key1319, -1), (key1319, -1), (key1311, 1), (key1311, 1), (key1427, 1), (key1427, 1), (key1419, -1), (key1419, -1), (key1634, -1), (key1634, -1), (key1625, 1), (key1625, 1), (key1927, 1), (key1927, 1), (key1921, -1), (key1921, -1)]

def rawRow5203 : Integer.Sparse Key := [(key1541, -1), (key1549, -1), (key1897, 2), (key1386, -1), (key1394, -1), (key1541, 2), (key1557, 2), (key1897, -1), (key1900, -1), (key1394, 2), (key1549, -1), (key1557, -1), (key1568, 1), (key1576, 1), (key1904, -2), (key1291, 1), (key1299, 1), (key1568, -2), (key1594, -2), (key1904, 1), (key1912, 1), (key1299, -2), (key1576, 1), (key1594, 1), (key1617, -1), (key1625, -1), (key1919, 1), (key1921, 1), (key1617, 1), (key1634, 1), (key1919, -1), (key1927, -1), (key1311, -1), (key1327, -1), (key1419, 1), (key1445, 1), (key1319, 1), (key1327, 1), (key1427, -1), (key1445, -1)]

def rawRow5204 : Integer.Sparse Key := [(key1549, -1), (key1541, -1), (key1897, 2), (key1394, -1), (key1386, -1), (key1557, 2), (key1541, 2), (key1900, -1), (key1897, -1), (key1394, 2), (key1557, -1), (key1549, -1), (key1576, 1), (key1568, 1), (key1904, -2), (key1299, 1), (key1291, 1), (key1594, -2), (key1568, -2), (key1912, 1), (key1904, 1), (key1299, -2), (key1594, 1), (key1576, 1), (key1625, -1), (key1617, -1), (key1921, 1), (key1919, 1), (key1634, 1), (key1617, 1), (key1927, -1), (key1919, -1), (key1327, -1), (key1311, -1), (key1445, 1), (key1419, 1), (key1327, 1), (key1319, 1), (key1445, -1), (key1427, -1)]

def rawRow5205 : Integer.Sparse Key := [(key1541, -1), (key1897, -1), (key1549, 2), (key1541, -1), (key1897, -1), (key1386, 2), (key1900, 2), (key1394, -1), (key1557, -1), (key1549, 2), (key1394, -1), (key1557, -1), (key1568, 1), (key1904, 1), (key1576, -2), (key1568, 1), (key1904, 1), (key1291, -2), (key1912, -2), (key1299, 1), (key1594, 1), (key1576, -2), (key1299, 1), (key1594, 1), (key1419, -1), (key1921, -1), (key1427, 1), (key1625, 1), (key1311, 1), (key1927, 1), (key1319, -1), (key1634, -1), (key1419, -1), (key1921, -1), (key1311, 1), (key1927, 1), (key1427, 1), (key1625, 1), (key1319, -1), (key1634, -1)]

def rawRow5206 : Integer.Sparse Key := [(key1897, -1), (key1541, -1), (key1549, 2), (key1897, -1), (key1541, -1), (key1900, 2), (key1386, 2), (key1557, -1), (key1394, -1), (key1549, 2), (key1557, -1), (key1394, -1), (key1904, 1), (key1568, 1), (key1576, -2), (key1904, 1), (key1568, 1), (key1912, -2), (key1291, -2), (key1594, 1), (key1299, 1), (key1576, -2), (key1594, 1), (key1299, 1), (key1921, -1), (key1419, -1), (key1625, 1), (key1427, 1), (key1927, 1), (key1311, 1), (key1634, -1), (key1319, -1), (key1921, -1), (key1419, -1), (key1927, 1), (key1311, 1), (key1625, 1), (key1427, 1), (key1634, -1), (key1319, -1)]

def rawRow5207 : Integer.Sparse Key := [(key1549, -1), (key1897, -1), (key1541, 2), (key1557, -1), (key1900, -1), (key1394, 2), (key1897, 2), (key1386, -1), (key1541, -1), (key1557, 2), (key1394, -1), (key1549, -1), (key1576, 1), (key1904, 1), (key1568, -2), (key1594, 1), (key1912, 1), (key1299, -2), (key1904, -2), (key1291, 1), (key1568, 1), (key1594, -2), (key1299, 1), (key1576, 1), (key1427, -1), (key1919, -1), (key1419, 1), (key1617, 1), (key1319, 1), (key1919, 1), (key1311, -1), (key1617, -1), (key1445, -1), (key1927, -1), (key1327, 1), (key1921, 1), (key1445, 1), (key1634, 1), (key1327, -1), (key1625, -1)]

def rawRow5208 : Integer.Sparse Key := [(key1897, -1), (key1549, -1), (key1541, 2), (key1900, -1), (key1557, -1), (key1897, 2), (key1394, 2), (key1541, -1), (key1386, -1), (key1557, 2), (key1549, -1), (key1394, -1), (key1904, 1), (key1576, 1), (key1568, -2), (key1912, 1), (key1594, 1), (key1904, -2), (key1299, -2), (key1568, 1), (key1291, 1), (key1594, -2), (key1576, 1), (key1299, 1), (key1919, -1), (key1427, -1), (key1617, 1), (key1419, 1), (key1919, 1), (key1319, 1), (key1617, -1), (key1311, -1), (key1927, -1), (key1445, -1), (key1921, 1), (key1327, 1), (key1634, 1), (key1445, 1), (key1625, -1), (key1327, -1)]

def rawRow5209 : Integer.Sparse Key := [(key1557, -1), (key1557, -1), (key1900, 2), (key1394, -1), (key1394, -1), (key1549, 2), (key1549, 2), (key1897, -1), (key1897, -1), (key1386, 2), (key1541, -1), (key1541, -1), (key1594, 1), (key1594, 1), (key1912, -2), (key1299, 1), (key1299, 1), (key1576, -2), (key1576, -2), (key1904, 1), (key1904, 1), (key1291, -2), (key1568, 1), (key1568, 1), (key1634, -1), (key1634, -1), (key1927, 1), (key1927, 1), (key1625, 1), (key1625, 1), (key1921, -1), (key1921, -1), (key1319, -1), (key1319, -1), (key1427, 1), (key1427, 1), (key1311, 1), (key1311, 1), (key1419, -1), (key1419, -1)]

def rawRow5210 : Integer.Sparse Key := [(key1557, -1), (key1900, -1), (key1557, 2), (key1549, -1), (key1897, -1), (key1394, 2), (key1897, 2), (key1394, -1), (key1549, -1), (key1541, 2), (key1386, -1), (key1541, -1), (key1594, 1), (key1912, 1), (key1594, -2), (key1576, 1), (key1904, 1), (key1299, -2), (key1904, -2), (key1299, 1), (key1576, 1), (key1568, -2), (key1291, 1), (key1568, 1), (key1445, -1), (key1927, -1), (key1445, 1), (key1634, 1), (key1327, 1), (key1921, 1), (key1327, -1), (key1625, -1), (key1427, -1), (key1919, -1), (key1319, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

def rawRow5211 : Integer.Sparse Key := [(key1900, -1), (key1557, -1), (key1557, 2), (key1897, -1), (key1549, -1), (key1897, 2), (key1394, 2), (key1549, -1), (key1394, -1), (key1541, 2), (key1541, -1), (key1386, -1), (key1912, 1), (key1594, 1), (key1594, -2), (key1904, 1), (key1576, 1), (key1904, -2), (key1299, -2), (key1576, 1), (key1299, 1), (key1568, -2), (key1568, 1), (key1291, 1), (key1927, -1), (key1445, -1), (key1634, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1625, -1), (key1327, -1), (key1919, -1), (key1427, -1), (key1919, 1), (key1319, 1), (key1617, 1), (key1419, 1), (key1617, -1), (key1311, -1)]

def rawRow5212 : Integer.Sparse Key := [(key1419, -1), (key1473, -1), (key1427, 2), (key1617, -1), (key1682, -1), (key1568, 2), (key1684, 2), (key1576, -1), (key1625, -1), (key1919, 2), (key1904, -1), (key1921, -1), (key1311, 1), (key1352, 1), (key1319, -2), (key1617, 1), (key1682, 1), (key1541, -2), (key1690, -2), (key1549, 1), (key1634, 1), (key1919, -2), (key1897, 1), (key1927, 1), (key1291, -1), (key1355, -1), (key1299, 1), (key1327, 1), (key1386, 1), (key1481, 1), (key1394, -1), (key1445, -1), (key1568, -1), (key1684, -1), (key1541, 1), (key1690, 1), (key1904, 1), (key1921, 1), (key1897, -1), (key1927, -1)]

def rawRow5213 : Integer.Sparse Key := [(key1473, -1), (key1419, -1), (key1427, 2), (key1682, -1), (key1617, -1), (key1684, 2), (key1568, 2), (key1625, -1), (key1576, -1), (key1919, 2), (key1921, -1), (key1904, -1), (key1352, 1), (key1311, 1), (key1319, -2), (key1682, 1), (key1617, 1), (key1690, -2), (key1541, -2), (key1634, 1), (key1549, 1), (key1919, -2), (key1927, 1), (key1897, 1), (key1355, -1), (key1291, -1), (key1327, 1), (key1299, 1), (key1481, 1), (key1386, 1), (key1445, -1), (key1394, -1), (key1684, -1), (key1568, -1), (key1690, 1), (key1541, 1), (key1921, 1), (key1904, 1), (key1927, -1), (key1897, -1)]

def rawRow5214 : Integer.Sparse Key := [(key1427, -1), (key1473, -1), (key1419, 2), (key1625, -1), (key1684, -1), (key1576, 2), (key1682, 2), (key1568, -1), (key1617, -1), (key1921, 2), (key1904, -1), (key1919, -1), (key1319, 1), (key1352, 1), (key1311, -2), (key1634, 1), (key1690, 1), (key1549, -2), (key1682, -2), (key1541, 1), (key1617, 1), (key1927, -2), (key1897, 1), (key1919, 1), (key1299, -1), (key1352, -1), (key1291, 1), (key1311, 1), (key1394, 1), (key1473, 1), (key1386, -1), (key1419, -1), (key1594, -1), (key1690, -1), (key1557, 1), (key1684, 1), (key1912, 1), (key1927, 1), (key1900, -1), (key1921, -1)]

def rawRow5215 : Integer.Sparse Key := [(key1473, -1), (key1427, -1), (key1419, 2), (key1684, -1), (key1625, -1), (key1682, 2), (key1576, 2), (key1617, -1), (key1568, -1), (key1921, 2), (key1919, -1), (key1904, -1), (key1352, 1), (key1319, 1), (key1311, -2), (key1690, 1), (key1634, 1), (key1682, -2), (key1549, -2), (key1617, 1), (key1541, 1), (key1927, -2), (key1919, 1), (key1897, 1), (key1352, -1), (key1299, -1), (key1311, 1), (key1291, 1), (key1473, 1), (key1394, 1), (key1419, -1), (key1386, -1), (key1690, -1), (key1594, -1), (key1684, 1), (key1557, 1), (key1927, 1), (key1912, 1), (key1921, -1), (key1900, -1)]

def rawRow5216 : Integer.Sparse Key := [(key1568, -1), (key1904, -1), (key1576, 2), (key1617, -1), (key1919, -1), (key1419, 2), (key1921, 2), (key1427, -1), (key1625, -1), (key1682, 2), (key1473, -1), (key1684, -1), (key1541, 1), (key1897, 1), (key1549, -2), (key1617, 1), (key1919, 1), (key1311, -2), (key1927, -2), (key1319, 1), (key1634, 1), (key1682, -2), (key1352, 1), (key1690, 1), (key1386, -1), (key1900, -1), (key1394, 1), (key1557, 1), (key1291, 1), (key1912, 1), (key1299, -1), (key1594, -1), (key1419, -1), (key1921, -1), (key1311, 1), (key1927, 1), (key1473, 1), (key1684, 1), (key1352, -1), (key1690, -1)]

def rawRow5217 : Integer.Sparse Key := [(key1904, -1), (key1568, -1), (key1576, 2), (key1919, -1), (key1617, -1), (key1921, 2), (key1419, 2), (key1625, -1), (key1427, -1), (key1682, 2), (key1684, -1), (key1473, -1), (key1897, 1), (key1541, 1), (key1549, -2), (key1919, 1), (key1617, 1), (key1927, -2), (key1311, -2), (key1634, 1), (key1319, 1), (key1682, -2), (key1690, 1), (key1352, 1), (key1900, -1), (key1386, -1), (key1557, 1), (key1394, 1), (key1912, 1), (key1291, 1), (key1594, -1), (key1299, -1), (key1921, -1), (key1419, -1), (key1927, 1), (key1311, 1), (key1684, 1), (key1473, 1), (key1690, -1), (key1352, -1)]

def rawRow5218 : Integer.Sparse Key := [(key1576, -1), (key1904, -1), (key1568, 2), (key1625, -1), (key1921, -1), (key1427, 2), (key1919, 2), (key1419, -1), (key1617, -1), (key1684, 2), (key1473, -1), (key1682, -1), (key1549, 1), (key1897, 1), (key1541, -2), (key1634, 1), (key1927, 1), (key1319, -2), (key1919, -2), (key1311, 1), (key1617, 1), (key1690, -2), (key1352, 1), (key1682, 1), (key1394, -1), (key1897, -1), (key1386, 1), (key1541, 1), (key1299, 1), (key1904, 1), (key1291, -1), (key1568, -1), (key1445, -1), (key1927, -1), (key1327, 1), (key1921, 1), (key1481, 1), (key1690, 1), (key1355, -1), (key1684, -1)]

def rawRow5219 : Integer.Sparse Key := [(key1904, -1), (key1576, -1), (key1568, 2), (key1921, -1), (key1625, -1), (key1919, 2), (key1427, 2), (key1617, -1), (key1419, -1), (key1684, 2), (key1682, -1), (key1473, -1), (key1897, 1), (key1549, 1), (key1541, -2), (key1927, 1), (key1634, 1), (key1919, -2), (key1319, -2), (key1617, 1), (key1311, 1), (key1690, -2), (key1682, 1), (key1352, 1), (key1897, -1), (key1394, -1), (key1541, 1), (key1386, 1), (key1904, 1), (key1299, 1), (key1568, -1), (key1291, -1), (key1927, -1), (key1445, -1), (key1921, 1), (key1327, 1), (key1690, 1), (key1481, 1), (key1684, -1), (key1355, -1)]

def rawRow5220 : Integer.Sparse Key := [(key1617, -1), (key1682, -1), (key1919, 2), (key1419, -1), (key1473, -1), (key1568, 2), (key1684, 2), (key1904, -1), (key1921, -1), (key1427, 2), (key1576, -1), (key1625, -1), (key1617, 1), (key1682, 1), (key1919, -2), (key1311, 1), (key1352, 1), (key1541, -2), (key1690, -2), (key1897, 1), (key1927, 1), (key1319, -2), (key1549, 1), (key1634, 1), (key1568, -1), (key1684, -1), (key1904, 1), (key1921, 1), (key1541, 1), (key1690, 1), (key1897, -1), (key1927, -1), (key1291, -1), (key1355, -1), (key1386, 1), (key1481, 1), (key1299, 1), (key1327, 1), (key1394, -1), (key1445, -1)]

def rawRow5221 : Integer.Sparse Key := [(key1682, -1), (key1617, -1), (key1919, 2), (key1473, -1), (key1419, -1), (key1684, 2), (key1568, 2), (key1921, -1), (key1904, -1), (key1427, 2), (key1625, -1), (key1576, -1), (key1682, 1), (key1617, 1), (key1919, -2), (key1352, 1), (key1311, 1), (key1690, -2), (key1541, -2), (key1927, 1), (key1897, 1), (key1319, -2), (key1634, 1), (key1549, 1), (key1684, -1), (key1568, -1), (key1921, 1), (key1904, 1), (key1690, 1), (key1541, 1), (key1927, -1), (key1897, -1), (key1355, -1), (key1291, -1), (key1481, 1), (key1386, 1), (key1327, 1), (key1299, 1), (key1445, -1), (key1394, -1)]

def rawRow5222 : Integer.Sparse Key := [(key1617, -1), (key1919, -1), (key1682, 2), (key1568, -1), (key1904, -1), (key1419, 2), (key1921, 2), (key1473, -1), (key1684, -1), (key1576, 2), (key1427, -1), (key1625, -1), (key1617, 1), (key1919, 1), (key1682, -2), (key1541, 1), (key1897, 1), (key1311, -2), (key1927, -2), (key1352, 1), (key1690, 1), (key1549, -2), (key1319, 1), (key1634, 1), (key1419, -1), (key1921, -1), (key1473, 1), (key1684, 1), (key1311, 1), (key1927, 1), (key1352, -1), (key1690, -1), (key1386, -1), (key1900, -1), (key1291, 1), (key1912, 1), (key1394, 1), (key1557, 1), (key1299, -1), (key1594, -1)]

def rawRow5223 : Integer.Sparse Key := [(key1919, -1), (key1617, -1), (key1682, 2), (key1904, -1), (key1568, -1), (key1921, 2), (key1419, 2), (key1684, -1), (key1473, -1), (key1576, 2), (key1625, -1), (key1427, -1), (key1919, 1), (key1617, 1), (key1682, -2), (key1897, 1), (key1541, 1), (key1927, -2), (key1311, -2), (key1690, 1), (key1352, 1), (key1549, -2), (key1634, 1), (key1319, 1), (key1921, -1), (key1419, -1), (key1684, 1), (key1473, 1), (key1927, 1), (key1311, 1), (key1690, -1), (key1352, -1), (key1900, -1), (key1386, -1), (key1912, 1), (key1291, 1), (key1557, 1), (key1394, 1), (key1594, -1), (key1299, -1)]

def rawRow5224 : Integer.Sparse Key := [(key1625, -1), (key1684, -1), (key1921, 2), (key1427, -1), (key1473, -1), (key1576, 2), (key1682, 2), (key1904, -1), (key1919, -1), (key1419, 2), (key1568, -1), (key1617, -1), (key1634, 1), (key1690, 1), (key1927, -2), (key1319, 1), (key1352, 1), (key1549, -2), (key1682, -2), (key1897, 1), (key1919, 1), (key1311, -2), (key1541, 1), (key1617, 1), (key1594, -1), (key1690, -1), (key1912, 1), (key1927, 1), (key1557, 1), (key1684, 1), (key1900, -1), (key1921, -1), (key1299, -1), (key1352, -1), (key1394, 1), (key1473, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1419, -1)]

def rawRow5225 : Integer.Sparse Key := [(key1684, -1), (key1625, -1), (key1921, 2), (key1473, -1), (key1427, -1), (key1682, 2), (key1576, 2), (key1919, -1), (key1904, -1), (key1419, 2), (key1617, -1), (key1568, -1), (key1690, 1), (key1634, 1), (key1927, -2), (key1352, 1), (key1319, 1), (key1682, -2), (key1549, -2), (key1919, 1), (key1897, 1), (key1311, -2), (key1617, 1), (key1541, 1), (key1690, -1), (key1594, -1), (key1927, 1), (key1912, 1), (key1684, 1), (key1557, 1), (key1921, -1), (key1900, -1), (key1352, -1), (key1299, -1), (key1473, 1), (key1394, 1), (key1311, 1), (key1291, 1), (key1419, -1), (key1386, -1)]

def rawRow5226 : Integer.Sparse Key := [(key1625, -1), (key1921, -1), (key1684, 2), (key1576, -1), (key1904, -1), (key1427, 2), (key1919, 2), (key1473, -1), (key1682, -1), (key1568, 2), (key1419, -1), (key1617, -1), (key1634, 1), (key1927, 1), (key1690, -2), (key1549, 1), (key1897, 1), (key1319, -2), (key1919, -2), (key1352, 1), (key1682, 1), (key1541, -2), (key1311, 1), (key1617, 1), (key1445, -1), (key1927, -1), (key1481, 1), (key1690, 1), (key1327, 1), (key1921, 1), (key1355, -1), (key1684, -1), (key1394, -1), (key1897, -1), (key1299, 1), (key1904, 1), (key1386, 1), (key1541, 1), (key1291, -1), (key1568, -1)]

def rawRow5227 : Integer.Sparse Key := [(key1921, -1), (key1625, -1), (key1684, 2), (key1904, -1), (key1576, -1), (key1919, 2), (key1427, 2), (key1682, -1), (key1473, -1), (key1568, 2), (key1617, -1), (key1419, -1), (key1927, 1), (key1634, 1), (key1690, -2), (key1897, 1), (key1549, 1), (key1919, -2), (key1319, -2), (key1682, 1), (key1352, 1), (key1541, -2), (key1617, 1), (key1311, 1), (key1927, -1), (key1445, -1), (key1690, 1), (key1481, 1), (key1921, 1), (key1327, 1), (key1684, -1), (key1355, -1), (key1897, -1), (key1394, -1), (key1904, 1), (key1299, 1), (key1541, 1), (key1386, 1), (key1568, -1), (key1291, -1)]

def rawRow5228 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key241, 2), (key248, -1), (key253, -1), (key248, 2), (key263, 2), (key253, -1), (key263, -1), (key277, 2), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key307, -2), (key316, 1), (key321, 1), (key316, -2), (key331, -2), (key321, 1), (key331, 1), (key346, -2), (key346, 1), (key347, 1), (key385, -1), (key400, -1), (key390, 1), (key400, 1), (key406, 1), (key421, 1), (key411, -1), (key421, -1), (key435, -1), (key445, -1), (key435, 1), (key453, 1), (key487, 1), (key488, 1), (key487, -1), (key489, -1)]

def rawRow5229 : Integer.Sparse Key := [(key241, -1), (key236, -1), (key241, 2), (key253, -1), (key248, -1), (key263, 2), (key248, 2), (key263, -1), (key253, -1), (key277, 2), (key278, -1), (key277, -1), (key307, 1), (key302, 1), (key307, -2), (key321, 1), (key316, 1), (key331, -2), (key316, -2), (key331, 1), (key321, 1), (key346, -2), (key347, 1), (key346, 1), (key400, -1), (key385, -1), (key400, 1), (key390, 1), (key421, 1), (key406, 1), (key421, -1), (key411, -1), (key445, -1), (key435, -1), (key453, 1), (key435, 1), (key488, 1), (key487, 1), (key489, -1), (key487, -1)]

def rawRow5230 : Integer.Sparse Key := [(key241, -1), (key241, -1), (key236, 2), (key263, -1), (key263, -1), (key253, 2), (key253, 2), (key248, -1), (key248, -1), (key278, 2), (key277, -1), (key277, -1), (key307, 1), (key307, 1), (key302, -2), (key331, 1), (key331, 1), (key321, -2), (key321, -2), (key316, 1), (key316, 1), (key347, -2), (key346, 1), (key346, 1), (key390, -1), (key390, -1), (key385, 1), (key385, 1), (key411, 1), (key411, 1), (key406, -1), (key406, -1), (key453, -1), (key453, -1), (key445, 1), (key445, 1), (key489, 1), (key489, 1), (key488, -1), (key488, -1)]

def rawRow5231 : Integer.Sparse Key := [(key248, -1), (key253, -1), (key263, 2), (key236, -1), (key241, -1), (key248, 2), (key263, 2), (key277, -1), (key278, -1), (key241, 2), (key253, -1), (key263, -1), (key316, 1), (key321, 1), (key346, -2), (key302, 1), (key307, 1), (key316, -2), (key331, -2), (key346, 1), (key347, 1), (key307, -2), (key321, 1), (key331, 1), (key435, -1), (key445, -1), (key487, 1), (key488, 1), (key435, 1), (key453, 1), (key487, -1), (key489, -1), (key385, -1), (key400, -1), (key406, 1), (key421, 1), (key390, 1), (key400, 1), (key411, -1), (key421, -1)]

def rawRow5232 : Integer.Sparse Key := [(key253, -1), (key248, -1), (key263, 2), (key241, -1), (key236, -1), (key263, 2), (key248, 2), (key278, -1), (key277, -1), (key241, 2), (key263, -1), (key253, -1), (key321, 1), (key316, 1), (key346, -2), (key307, 1), (key302, 1), (key331, -2), (key316, -2), (key347, 1), (key346, 1), (key307, -2), (key331, 1), (key321, 1), (key445, -1), (key435, -1), (key488, 1), (key487, 1), (key453, 1), (key435, 1), (key489, -1), (key487, -1), (key400, -1), (key385, -1), (key421, 1), (key406, 1), (key400, 1), (key390, 1), (key421, -1), (key411, -1)]

def rawRow5233 : Integer.Sparse Key := [(key248, -1), (key263, -1), (key253, 2), (key248, -1), (key263, -1), (key236, 2), (key278, 2), (key241, -1), (key263, -1), (key253, 2), (key241, -1), (key263, -1), (key316, 1), (key346, 1), (key321, -2), (key316, 1), (key346, 1), (key302, -2), (key347, -2), (key307, 1), (key331, 1), (key321, -2), (key307, 1), (key331, 1), (key406, -1), (key488, -1), (key411, 1), (key445, 1), (key385, 1), (key489, 1), (key390, -1), (key453, -1), (key406, -1), (key488, -1), (key385, 1), (key489, 1), (key411, 1), (key445, 1), (key390, -1), (key453, -1)]

def rawRow5234 : Integer.Sparse Key := [(key263, -1), (key248, -1), (key253, 2), (key263, -1), (key248, -1), (key278, 2), (key236, 2), (key263, -1), (key241, -1), (key253, 2), (key263, -1), (key241, -1), (key346, 1), (key316, 1), (key321, -2), (key346, 1), (key316, 1), (key347, -2), (key302, -2), (key331, 1), (key307, 1), (key321, -2), (key331, 1), (key307, 1), (key488, -1), (key406, -1), (key445, 1), (key411, 1), (key489, 1), (key385, 1), (key453, -1), (key390, -1), (key488, -1), (key406, -1), (key489, 1), (key385, 1), (key445, 1), (key411, 1), (key453, -1), (key390, -1)]

def rawRow5235 : Integer.Sparse Key := [(key253, -1), (key263, -1), (key248, 2), (key277, -1), (key278, -1), (key241, 2), (key263, 2), (key236, -1), (key248, -1), (key263, 2), (key241, -1), (key253, -1), (key321, 1), (key346, 1), (key316, -2), (key331, 1), (key347, 1), (key307, -2), (key346, -2), (key302, 1), (key316, 1), (key331, -2), (key307, 1), (key321, 1), (key411, -1), (key487, -1), (key406, 1), (key435, 1), (key390, 1), (key487, 1), (key385, -1), (key435, -1), (key421, -1), (key489, -1), (key400, 1), (key488, 1), (key421, 1), (key453, 1), (key400, -1), (key445, -1)]

def rawRow5236 : Integer.Sparse Key := [(key263, -1), (key253, -1), (key248, 2), (key278, -1), (key277, -1), (key263, 2), (key241, 2), (key248, -1), (key236, -1), (key263, 2), (key253, -1), (key241, -1), (key346, 1), (key321, 1), (key316, -2), (key347, 1), (key331, 1), (key346, -2), (key307, -2), (key316, 1), (key302, 1), (key331, -2), (key321, 1), (key307, 1), (key487, -1), (key411, -1), (key435, 1), (key406, 1), (key487, 1), (key390, 1), (key435, -1), (key385, -1), (key489, -1), (key421, -1), (key488, 1), (key400, 1), (key453, 1), (key421, 1), (key445, -1), (key400, -1)]

def rawRow5237 : Integer.Sparse Key := [(key277, -1), (key277, -1), (key278, 2), (key241, -1), (key241, -1), (key253, 2), (key253, 2), (key263, -1), (key263, -1), (key236, 2), (key248, -1), (key248, -1), (key331, 1), (key331, 1), (key347, -2), (key307, 1), (key307, 1), (key321, -2), (key321, -2), (key346, 1), (key346, 1), (key302, -2), (key316, 1), (key316, 1), (key453, -1), (key453, -1), (key489, 1), (key489, 1), (key445, 1), (key445, 1), (key488, -1), (key488, -1), (key390, -1), (key390, -1), (key411, 1), (key411, 1), (key385, 1), (key385, 1), (key406, -1), (key406, -1)]

def rawRow5238 : Integer.Sparse Key := [(key277, -1), (key278, -1), (key277, 2), (key253, -1), (key263, -1), (key241, 2), (key263, 2), (key241, -1), (key253, -1), (key248, 2), (key236, -1), (key248, -1), (key331, 1), (key347, 1), (key331, -2), (key321, 1), (key346, 1), (key307, -2), (key346, -2), (key307, 1), (key321, 1), (key316, -2), (key302, 1), (key316, 1), (key421, -1), (key489, -1), (key421, 1), (key453, 1), (key400, 1), (key488, 1), (key400, -1), (key445, -1), (key411, -1), (key487, -1), (key390, 1), (key487, 1), (key406, 1), (key435, 1), (key385, -1), (key435, -1)]

def rawRow5239 : Integer.Sparse Key := [(key278, -1), (key277, -1), (key277, 2), (key263, -1), (key253, -1), (key263, 2), (key241, 2), (key253, -1), (key241, -1), (key248, 2), (key248, -1), (key236, -1), (key347, 1), (key331, 1), (key331, -2), (key346, 1), (key321, 1), (key346, -2), (key307, -2), (key321, 1), (key307, 1), (key316, -2), (key316, 1), (key302, 1), (key489, -1), (key421, -1), (key453, 1), (key421, 1), (key488, 1), (key400, 1), (key445, -1), (key400, -1), (key487, -1), (key411, -1), (key487, 1), (key390, 1), (key435, 1), (key406, 1), (key435, -1), (key385, -1)]

def rawRow5240 : Integer.Sparse Key := [(key302, -1), (key307, -1), (key307, 2), (key316, -1), (key321, -1), (key316, 2), (key346, 2), (key321, -1), (key346, -1), (key331, 2), (key331, -1), (key347, -1), (key236, 1), (key241, 1), (key241, -2), (key406, 1), (key411, 1), (key406, -2), (key421, -2), (key411, 1), (key421, 1), (key657, -2), (key657, 1), (key658, 1), (key248, -1), (key263, -1), (key253, 1), (key263, 1), (key316, 1), (key331, 1), (key321, -1), (key331, -1), (key435, -1), (key445, -1), (key435, 1), (key453, 1), (key660, 1), (key661, 1), (key660, -1), (key662, -1)]

def rawRow5241 : Integer.Sparse Key := [(key307, -1), (key302, -1), (key307, 2), (key321, -1), (key316, -1), (key346, 2), (key316, 2), (key346, -1), (key321, -1), (key331, 2), (key347, -1), (key331, -1), (key241, 1), (key236, 1), (key241, -2), (key411, 1), (key406, 1), (key421, -2), (key406, -2), (key421, 1), (key411, 1), (key657, -2), (key658, 1), (key657, 1), (key263, -1), (key248, -1), (key263, 1), (key253, 1), (key331, 1), (key316, 1), (key331, -1), (key321, -1), (key445, -1), (key435, -1), (key453, 1), (key435, 1), (key661, 1), (key660, 1), (key662, -1), (key660, -1)]

def rawRow5242 : Integer.Sparse Key := [(key307, -1), (key307, -1), (key302, 2), (key346, -1), (key346, -1), (key321, 2), (key321, 2), (key316, -1), (key316, -1), (key347, 2), (key331, -1), (key331, -1), (key241, 1), (key241, 1), (key236, -2), (key421, 1), (key421, 1), (key411, -2), (key411, -2), (key406, 1), (key406, 1), (key658, -2), (key657, 1), (key657, 1), (key253, -1), (key253, -1), (key248, 1), (key248, 1), (key321, 1), (key321, 1), (key316, -1), (key316, -1), (key453, -1), (key453, -1), (key445, 1), (key445, 1), (key662, 1), (key662, 1), (key661, -1), (key661, -1)]

def rawRow5243 : Integer.Sparse Key := [(key316, -1), (key321, -1), (key331, 2), (key302, -1), (key307, -1), (key316, 2), (key346, 2), (key331, -1), (key347, -1), (key307, 2), (key321, -1), (key346, -1), (key406, 1), (key411, 1), (key421, -2), (key236, 1), (key241, 1), (key406, -2), (key421, -2), (key657, 1), (key658, 1), (key241, -2), (key411, 1), (key421, 1), (key435, -1), (key445, -1), (key660, 1), (key661, 1), (key435, 1), (key453, 1), (key660, -1), (key662, -1), (key248, -1), (key263, -1), (key316, 1), (key331, 1), (key253, 1), (key263, 1), (key321, -1), (key331, -1)]

def rawRow5244 : Integer.Sparse Key := [(key321, -1), (key316, -1), (key331, 2), (key307, -1), (key302, -1), (key346, 2), (key316, 2), (key347, -1), (key331, -1), (key307, 2), (key346, -1), (key321, -1), (key411, 1), (key406, 1), (key421, -2), (key241, 1), (key236, 1), (key421, -2), (key406, -2), (key658, 1), (key657, 1), (key241, -2), (key421, 1), (key411, 1), (key445, -1), (key435, -1), (key661, 1), (key660, 1), (key453, 1), (key435, 1), (key662, -1), (key660, -1), (key263, -1), (key248, -1), (key331, 1), (key316, 1), (key263, 1), (key253, 1), (key331, -1), (key321, -1)]

def rawRow5245 : Integer.Sparse Key := [(key316, -1), (key331, -1), (key321, 2), (key316, -1), (key331, -1), (key302, 2), (key347, 2), (key307, -1), (key346, -1), (key321, 2), (key307, -1), (key346, -1), (key406, 1), (key421, 1), (key411, -2), (key406, 1), (key421, 1), (key236, -2), (key658, -2), (key241, 1), (key421, 1), (key411, -2), (key241, 1), (key421, 1), (key316, -1), (key661, -1), (key321, 1), (key445, 1), (key248, 1), (key662, 1), (key253, -1), (key453, -1), (key316, -1), (key661, -1), (key248, 1), (key662, 1), (key321, 1), (key445, 1), (key253, -1), (key453, -1)]

def rawRow5246 : Integer.Sparse Key := [(key331, -1), (key316, -1), (key321, 2), (key331, -1), (key316, -1), (key347, 2), (key302, 2), (key346, -1), (key307, -1), (key321, 2), (key346, -1), (key307, -1), (key421, 1), (key406, 1), (key411, -2), (key421, 1), (key406, 1), (key658, -2), (key236, -2), (key421, 1), (key241, 1), (key411, -2), (key421, 1), (key241, 1), (key661, -1), (key316, -1), (key445, 1), (key321, 1), (key662, 1), (key248, 1), (key453, -1), (key253, -1), (key661, -1), (key316, -1), (key662, 1), (key248, 1), (key445, 1), (key321, 1), (key453, -1), (key253, -1)]

def rawRow5247 : Integer.Sparse Key := [(key321, -1), (key331, -1), (key316, 2), (key346, -1), (key347, -1), (key307, 2), (key331, 2), (key302, -1), (key316, -1), (key346, 2), (key307, -1), (key321, -1), (key411, 1), (key421, 1), (key406, -2), (key657, 1), (key658, 1), (key241, -2), (key421, -2), (key236, 1), (key406, 1), (key421, -2), (key241, 1), (key411, 1), (key321, -1), (key660, -1), (key316, 1), (key435, 1), (key253, 1), (key660, 1), (key248, -1), (key435, -1), (key331, -1), (key662, -1), (key263, 1), (key661, 1), (key331, 1), (key453, 1), (key263, -1), (key445, -1)]

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

def rawRow5248 : Integer.Sparse Key := [(key331, -1), (key321, -1), (key316, 2), (key347, -1), (key346, -1), (key331, 2), (key307, 2), (key316, -1), (key302, -1), (key346, 2), (key321, -1), (key307, -1), (key421, 1), (key411, 1), (key406, -2), (key658, 1), (key657, 1), (key421, -2), (key241, -2), (key406, 1), (key236, 1), (key421, -2), (key411, 1), (key241, 1), (key660, -1), (key321, -1), (key435, 1), (key316, 1), (key660, 1), (key253, 1), (key435, -1), (key248, -1), (key662, -1), (key331, -1), (key661, 1), (key263, 1), (key453, 1), (key331, 1), (key445, -1), (key263, -1)]

def rawRow5249 : Integer.Sparse Key := [(key346, -1), (key346, -1), (key347, 2), (key307, -1), (key307, -1), (key321, 2), (key321, 2), (key331, -1), (key331, -1), (key302, 2), (key316, -1), (key316, -1), (key657, 1), (key657, 1), (key658, -2), (key241, 1), (key241, 1), (key411, -2), (key411, -2), (key421, 1), (key421, 1), (key236, -2), (key406, 1), (key406, 1), (key453, -1), (key453, -1), (key662, 1), (key662, 1), (key445, 1), (key445, 1), (key661, -1), (key661, -1), (key253, -1), (key253, -1), (key321, 1), (key321, 1), (key248, 1), (key248, 1), (key316, -1), (key316, -1)]

def rawRow5250 : Integer.Sparse Key := [(key346, -1), (key347, -1), (key346, 2), (key321, -1), (key331, -1), (key307, 2), (key331, 2), (key307, -1), (key321, -1), (key316, 2), (key302, -1), (key316, -1), (key657, 1), (key658, 1), (key657, -2), (key411, 1), (key421, 1), (key241, -2), (key421, -2), (key241, 1), (key411, 1), (key406, -2), (key236, 1), (key406, 1), (key331, -1), (key662, -1), (key331, 1), (key453, 1), (key263, 1), (key661, 1), (key263, -1), (key445, -1), (key321, -1), (key660, -1), (key253, 1), (key660, 1), (key316, 1), (key435, 1), (key248, -1), (key435, -1)]

def rawRow5251 : Integer.Sparse Key := [(key347, -1), (key346, -1), (key346, 2), (key331, -1), (key321, -1), (key331, 2), (key307, 2), (key321, -1), (key307, -1), (key316, 2), (key316, -1), (key302, -1), (key658, 1), (key657, 1), (key657, -2), (key421, 1), (key411, 1), (key421, -2), (key241, -2), (key411, 1), (key241, 1), (key406, -2), (key406, 1), (key236, 1), (key662, -1), (key331, -1), (key453, 1), (key331, 1), (key661, 1), (key263, 1), (key445, -1), (key263, -1), (key660, -1), (key321, -1), (key660, 1), (key253, 1), (key435, 1), (key316, 1), (key435, -1), (key248, -1)]

def rawRow5252 : Integer.Sparse Key := [(key385, -1), (key400, -1), (key390, 2), (key435, -1), (key445, -1), (key406, 2), (key488, 2), (key411, -1), (key487, -1), (key453, 2), (key421, -1), (key489, -1), (key248, 1), (key263, 1), (key253, -2), (key435, 1), (key445, 1), (key316, -2), (key661, -2), (key321, 1), (key660, 1), (key453, -2), (key331, 1), (key662, 1), (key236, -1), (key278, -1), (key241, 1), (key263, 1), (key302, 1), (key347, 1), (key307, -1), (key331, -1), (key406, -1), (key488, -1), (key385, 1), (key489, 1), (key657, 1), (key661, 1), (key655, -1), (key662, -1)]

def rawRow5253 : Integer.Sparse Key := [(key400, -1), (key385, -1), (key390, 2), (key445, -1), (key435, -1), (key488, 2), (key406, 2), (key487, -1), (key411, -1), (key453, 2), (key489, -1), (key421, -1), (key263, 1), (key248, 1), (key253, -2), (key445, 1), (key435, 1), (key661, -2), (key316, -2), (key660, 1), (key321, 1), (key453, -2), (key662, 1), (key331, 1), (key278, -1), (key236, -1), (key263, 1), (key241, 1), (key347, 1), (key302, 1), (key331, -1), (key307, -1), (key488, -1), (key406, -1), (key489, 1), (key385, 1), (key661, 1), (key657, 1), (key662, -1), (key655, -1)]

def rawRow5254 : Integer.Sparse Key := [(key390, -1), (key400, -1), (key385, 2), (key487, -1), (key488, -1), (key411, 2), (key445, 2), (key406, -1), (key435, -1), (key489, 2), (key421, -1), (key453, -1), (key253, 1), (key263, 1), (key248, -2), (key660, 1), (key661, 1), (key321, -2), (key445, -2), (key316, 1), (key435, 1), (key662, -2), (key331, 1), (key453, 1), (key241, -1), (key263, -1), (key236, 1), (key248, 1), (key307, 1), (key346, 1), (key302, -1), (key316, -1), (key421, -1), (key489, -1), (key400, 1), (key488, 1), (key658, 1), (key662, 1), (key656, -1), (key661, -1)]

def rawRow5255 : Integer.Sparse Key := [(key400, -1), (key390, -1), (key385, 2), (key488, -1), (key487, -1), (key445, 2), (key411, 2), (key435, -1), (key406, -1), (key489, 2), (key453, -1), (key421, -1), (key263, 1), (key253, 1), (key248, -2), (key661, 1), (key660, 1), (key445, -2), (key321, -2), (key435, 1), (key316, 1), (key662, -2), (key453, 1), (key331, 1), (key263, -1), (key241, -1), (key248, 1), (key236, 1), (key346, 1), (key307, 1), (key316, -1), (key302, -1), (key489, -1), (key421, -1), (key488, 1), (key400, 1), (key662, 1), (key658, 1), (key661, -1), (key656, -1)]

def rawRow5256 : Integer.Sparse Key := [(key406, -1), (key421, -1), (key411, 2), (key435, -1), (key453, -1), (key385, 2), (key489, 2), (key390, -1), (key487, -1), (key445, 2), (key400, -1), (key488, -1), (key316, 1), (key331, 1), (key321, -2), (key435, 1), (key453, 1), (key248, -2), (key662, -2), (key253, 1), (key660, 1), (key445, -2), (key263, 1), (key661, 1), (key302, -1), (key347, -1), (key307, 1), (key346, 1), (key236, 1), (key658, 1), (key241, -1), (key421, -1), (key316, -1), (key661, -1), (key248, 1), (key662, 1), (key346, 1), (key488, 1), (key277, -1), (key489, -1)]

def rawRow5257 : Integer.Sparse Key := [(key421, -1), (key406, -1), (key411, 2), (key453, -1), (key435, -1), (key489, 2), (key385, 2), (key487, -1), (key390, -1), (key445, 2), (key488, -1), (key400, -1), (key331, 1), (key316, 1), (key321, -2), (key453, 1), (key435, 1), (key662, -2), (key248, -2), (key660, 1), (key253, 1), (key445, -2), (key661, 1), (key263, 1), (key347, -1), (key302, -1), (key346, 1), (key307, 1), (key658, 1), (key236, 1), (key421, -1), (key241, -1), (key661, -1), (key316, -1), (key662, 1), (key248, 1), (key488, 1), (key346, 1), (key489, -1), (key277, -1)]

def rawRow5258 : Integer.Sparse Key := [(key411, -1), (key421, -1), (key406, 2), (key487, -1), (key489, -1), (key390, 2), (key453, 2), (key385, -1), (key435, -1), (key488, 2), (key400, -1), (key445, -1), (key321, 1), (key331, 1), (key316, -2), (key660, 1), (key662, 1), (key253, -2), (key453, -2), (key248, 1), (key435, 1), (key661, -2), (key263, 1), (key445, 1), (key307, -1), (key331, -1), (key302, 1), (key316, 1), (key241, 1), (key421, 1), (key236, -1), (key406, -1), (key331, -1), (key662, -1), (key263, 1), (key661, 1), (key347, 1), (key489, 1), (key278, -1), (key488, -1)]

def rawRow5259 : Integer.Sparse Key := [(key421, -1), (key411, -1), (key406, 2), (key489, -1), (key487, -1), (key453, 2), (key390, 2), (key435, -1), (key385, -1), (key488, 2), (key445, -1), (key400, -1), (key331, 1), (key321, 1), (key316, -2), (key662, 1), (key660, 1), (key453, -2), (key253, -2), (key435, 1), (key248, 1), (key661, -2), (key445, 1), (key263, 1), (key331, -1), (key307, -1), (key316, 1), (key302, 1), (key421, 1), (key241, 1), (key406, -1), (key236, -1), (key662, -1), (key331, -1), (key661, 1), (key263, 1), (key489, 1), (key347, 1), (key488, -1), (key278, -1)]

def rawRow5260 : Integer.Sparse Key := [(key435, -1), (key445, -1), (key453, 2), (key385, -1), (key400, -1), (key406, 2), (key488, 2), (key421, -1), (key489, -1), (key390, 2), (key411, -1), (key487, -1), (key435, 1), (key445, 1), (key453, -2), (key248, 1), (key263, 1), (key316, -2), (key661, -2), (key331, 1), (key662, 1), (key253, -2), (key321, 1), (key660, 1), (key406, -1), (key488, -1), (key421, 1), (key489, 1), (key316, 1), (key661, 1), (key331, -1), (key662, -1), (key236, -1), (key278, -1), (key302, 1), (key347, 1), (key241, 1), (key263, 1), (key307, -1), (key331, -1)]

def rawRow5261 : Integer.Sparse Key := [(key445, -1), (key435, -1), (key453, 2), (key400, -1), (key385, -1), (key488, 2), (key406, 2), (key489, -1), (key421, -1), (key390, 2), (key487, -1), (key411, -1), (key445, 1), (key435, 1), (key453, -2), (key263, 1), (key248, 1), (key661, -2), (key316, -2), (key662, 1), (key331, 1), (key253, -2), (key660, 1), (key321, 1), (key488, -1), (key406, -1), (key489, 1), (key421, 1), (key661, 1), (key316, 1), (key662, -1), (key331, -1), (key278, -1), (key236, -1), (key347, 1), (key302, 1), (key263, 1), (key241, 1), (key331, -1), (key307, -1)]

def rawRow5262 : Integer.Sparse Key := [(key435, -1), (key453, -1), (key445, 2), (key406, -1), (key421, -1), (key385, 2), (key489, 2), (key400, -1), (key488, -1), (key411, 2), (key390, -1), (key487, -1), (key435, 1), (key453, 1), (key445, -2), (key316, 1), (key331, 1), (key248, -2), (key662, -2), (key263, 1), (key661, 1), (key321, -2), (key253, 1), (key660, 1), (key385, -1), (key489, -1), (key400, 1), (key488, 1), (key248, 1), (key662, 1), (key263, -1), (key661, -1), (key302, -1), (key347, -1), (key236, 1), (key658, 1), (key307, 1), (key400, 1), (key241, -1), (key421, -1)]

def rawRow5263 : Integer.Sparse Key := [(key453, -1), (key435, -1), (key445, 2), (key421, -1), (key406, -1), (key489, 2), (key385, 2), (key488, -1), (key400, -1), (key411, 2), (key487, -1), (key390, -1), (key453, 1), (key435, 1), (key445, -2), (key331, 1), (key316, 1), (key662, -2), (key248, -2), (key661, 1), (key263, 1), (key321, -2), (key660, 1), (key253, 1), (key489, -1), (key385, -1), (key488, 1), (key400, 1), (key662, 1), (key248, 1), (key661, -1), (key263, -1), (key347, -1), (key302, -1), (key658, 1), (key236, 1), (key400, 1), (key307, 1), (key421, -1), (key241, -1)]

def rawRow5264 : Integer.Sparse Key := [(key487, -1), (key488, -1), (key489, 2), (key390, -1), (key400, -1), (key411, 2), (key445, 2), (key421, -1), (key453, -1), (key385, 2), (key406, -1), (key435, -1), (key660, 1), (key661, 1), (key662, -2), (key253, 1), (key263, 1), (key321, -2), (key445, -2), (key331, 1), (key453, 1), (key248, -2), (key316, 1), (key435, 1), (key657, -1), (key661, -1), (key658, 1), (key662, 1), (key346, 1), (key488, 1), (key347, -1), (key489, -1), (key241, -1), (key263, -1), (key307, 1), (key400, 1), (key236, 1), (key248, 1), (key302, -1), (key316, -1)]

def rawRow5265 : Integer.Sparse Key := [(key488, -1), (key487, -1), (key489, 2), (key400, -1), (key390, -1), (key445, 2), (key411, 2), (key453, -1), (key421, -1), (key385, 2), (key435, -1), (key406, -1), (key661, 1), (key660, 1), (key662, -2), (key263, 1), (key253, 1), (key445, -2), (key321, -2), (key453, 1), (key331, 1), (key248, -2), (key435, 1), (key316, 1), (key661, -1), (key657, -1), (key662, 1), (key658, 1), (key488, 1), (key346, 1), (key489, -1), (key347, -1), (key263, -1), (key241, -1), (key400, 1), (key307, 1), (key248, 1), (key236, 1), (key316, -1), (key302, -1)]

def rawRow5266 : Integer.Sparse Key := [(key487, -1), (key489, -1), (key488, 2), (key411, -1), (key421, -1), (key390, 2), (key453, 2), (key400, -1), (key445, -1), (key406, 2), (key385, -1), (key435, -1), (key660, 1), (key662, 1), (key661, -2), (key321, 1), (key331, 1), (key253, -2), (key453, -2), (key263, 1), (key445, 1), (key316, -2), (key248, 1), (key435, 1), (key655, -1), (key662, -1), (key656, 1), (key661, 1), (key277, 1), (key489, 1), (key278, -1), (key488, -1), (key307, -1), (key331, -1), (key241, 1), (key421, 1), (key302, 1), (key316, 1), (key236, -1), (key406, -1)]

def rawRow5267 : Integer.Sparse Key := [(key489, -1), (key487, -1), (key488, 2), (key421, -1), (key411, -1), (key453, 2), (key390, 2), (key445, -1), (key400, -1), (key406, 2), (key435, -1), (key385, -1), (key662, 1), (key660, 1), (key661, -2), (key331, 1), (key321, 1), (key453, -2), (key253, -2), (key445, 1), (key263, 1), (key316, -2), (key435, 1), (key248, 1), (key662, -1), (key655, -1), (key661, 1), (key656, 1), (key489, 1), (key277, 1), (key488, -1), (key278, -1), (key331, -1), (key307, -1), (key421, 1), (key241, 1), (key316, 1), (key302, 1), (key406, -1), (key236, -1)]

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

def rawRow5388 : Integer.Sparse Key := [(key1003, -1), (key1003, -1), (key1009, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1017, 2), (key1022, -1), (key1022, -1), (key1009, 2), (key1022, -1), (key1022, -1), (key1038, 1), (key1038, 1), (key1044, -2), (key1038, 1), (key1038, 1), (key1073, -2), (key1073, -2), (key1080, 1), (key1080, 1), (key1044, -2), (key1080, 1), (key1080, 1), (key1125, -1), (key1125, -1), (key1130, 1), (key1130, 1), (key1152, 1), (key1152, 1), (key1159, -1), (key1159, -1), (key1125, -1), (key1125, -1), (key1152, 1), (key1152, 1), (key1130, 1), (key1130, 1), (key1159, -1), (key1159, -1)]

def rawRow5389 : Integer.Sparse Key := [(key1003, -1), (key1009, -1), (key1003, 2), (key1017, -1), (key1022, -1), (key1003, 2), (key1022, 2), (key1003, -1), (key1017, -1), (key1022, 2), (key1009, -1), (key1022, -1), (key1038, 1), (key1044, 1), (key1038, -2), (key1073, 1), (key1080, 1), (key1038, -2), (key1080, -2), (key1038, 1), (key1073, 1), (key1080, -2), (key1044, 1), (key1080, 1), (key1116, -1), (key1130, -1), (key1116, 1), (key1125, 1), (key1116, 1), (key1159, 1), (key1116, -1), (key1152, -1), (key1152, -1), (key1174, -1), (key1125, 1), (key1174, 1), (key1159, 1), (key1174, 1), (key1130, -1), (key1174, -1)]

def rawRow5390 : Integer.Sparse Key := [(key1009, -1), (key1003, -1), (key1003, 2), (key1022, -1), (key1017, -1), (key1022, 2), (key1003, 2), (key1017, -1), (key1003, -1), (key1022, 2), (key1022, -1), (key1009, -1), (key1044, 1), (key1038, 1), (key1038, -2), (key1080, 1), (key1073, 1), (key1080, -2), (key1038, -2), (key1073, 1), (key1038, 1), (key1080, -2), (key1080, 1), (key1044, 1), (key1130, -1), (key1116, -1), (key1125, 1), (key1116, 1), (key1159, 1), (key1116, 1), (key1152, -1), (key1116, -1), (key1174, -1), (key1152, -1), (key1174, 1), (key1125, 1), (key1174, 1), (key1159, 1), (key1174, -1), (key1130, -1)]

def rawRow5391 : Integer.Sparse Key := [(key1017, -1), (key1022, -1), (key1022, 2), (key1003, -1), (key1009, -1), (key1003, 2), (key1022, 2), (key1009, -1), (key1022, -1), (key1003, 2), (key1003, -1), (key1017, -1), (key1073, 1), (key1080, 1), (key1080, -2), (key1038, 1), (key1044, 1), (key1038, -2), (key1080, -2), (key1044, 1), (key1080, 1), (key1038, -2), (key1038, 1), (key1073, 1), (key1152, -1), (key1174, -1), (key1159, 1), (key1174, 1), (key1125, 1), (key1174, 1), (key1130, -1), (key1174, -1), (key1116, -1), (key1130, -1), (key1116, 1), (key1159, 1), (key1116, 1), (key1125, 1), (key1116, -1), (key1152, -1)]

def rawRow5392 : Integer.Sparse Key := [(key1022, -1), (key1017, -1), (key1022, 2), (key1009, -1), (key1003, -1), (key1022, 2), (key1003, 2), (key1022, -1), (key1009, -1), (key1003, 2), (key1017, -1), (key1003, -1), (key1080, 1), (key1073, 1), (key1080, -2), (key1044, 1), (key1038, 1), (key1080, -2), (key1038, -2), (key1080, 1), (key1044, 1), (key1038, -2), (key1073, 1), (key1038, 1), (key1174, -1), (key1152, -1), (key1174, 1), (key1159, 1), (key1174, 1), (key1125, 1), (key1174, -1), (key1130, -1), (key1130, -1), (key1116, -1), (key1159, 1), (key1116, 1), (key1125, 1), (key1116, 1), (key1152, -1), (key1116, -1)]

def rawRow5393 : Integer.Sparse Key := [(key1022, -1), (key1022, -1), (key1017, 2), (key1022, -1), (key1022, -1), (key1009, 2), (key1009, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1003, -1), (key1003, -1), (key1080, 1), (key1080, 1), (key1073, -2), (key1080, 1), (key1080, 1), (key1044, -2), (key1044, -2), (key1038, 1), (key1038, 1), (key1073, -2), (key1038, 1), (key1038, 1), (key1159, -1), (key1159, -1), (key1152, 1), (key1152, 1), (key1130, 1), (key1130, 1), (key1125, -1), (key1125, -1), (key1159, -1), (key1159, -1), (key1130, 1), (key1130, 1), (key1152, 1), (key1152, 1), (key1125, -1), (key1125, -1)]

def rawRow5394 : Integer.Sparse Key := [(key1038, -1), (key1038, -1), (key1044, 2), (key1116, -1), (key1116, -1), (key1125, 2), (key1125, 2), (key1130, -1), (key1130, -1), (key1233, 2), (key1236, -1), (key1236, -1), (key1003, 1), (key1003, 1), (key1009, -2), (key1116, 1), (key1116, 1), (key1152, -2), (key1152, -2), (key1159, 1), (key1159, 1), (key1233, -2), (key1243, 1), (key1243, 1), (key1017, -1), (key1017, -1), (key1022, 1), (key1022, 1), (key1073, 1), (key1073, 1), (key1080, -1), (key1080, -1), (key1125, -1), (key1125, -1), (key1152, 1), (key1152, 1), (key1236, 1), (key1236, 1), (key1243, -1), (key1243, -1)]

def rawRow5395 : Integer.Sparse Key := [(key1038, -1), (key1044, -1), (key1038, 2), (key1125, -1), (key1130, -1), (key1116, 2), (key1130, 2), (key1116, -1), (key1125, -1), (key1236, 2), (key1233, -1), (key1236, -1), (key1003, 1), (key1009, 1), (key1003, -2), (key1152, 1), (key1159, 1), (key1116, -2), (key1159, -2), (key1116, 1), (key1152, 1), (key1243, -2), (key1233, 1), (key1243, 1), (key1003, -1), (key1022, -1), (key1003, 1), (key1017, 1), (key1038, 1), (key1080, 1), (key1038, -1), (key1073, -1), (key1152, -1), (key1174, -1), (key1125, 1), (key1174, 1), (key1243, 1), (key1247, 1), (key1236, -1), (key1247, -1)]

def rawRow5396 : Integer.Sparse Key := [(key1044, -1), (key1038, -1), (key1038, 2), (key1130, -1), (key1125, -1), (key1130, 2), (key1116, 2), (key1125, -1), (key1116, -1), (key1236, 2), (key1236, -1), (key1233, -1), (key1009, 1), (key1003, 1), (key1003, -2), (key1159, 1), (key1152, 1), (key1159, -2), (key1116, -2), (key1152, 1), (key1116, 1), (key1243, -2), (key1243, 1), (key1233, 1), (key1022, -1), (key1003, -1), (key1017, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1073, -1), (key1038, -1), (key1174, -1), (key1152, -1), (key1174, 1), (key1125, 1), (key1247, 1), (key1243, 1), (key1247, -1), (key1236, -1)]

def rawRow5397 : Integer.Sparse Key := [(key1116, -1), (key1116, -1), (key1233, 2), (key1038, -1), (key1038, -1), (key1125, 2), (key1125, 2), (key1236, -1), (key1236, -1), (key1044, 2), (key1130, -1), (key1130, -1), (key1116, 1), (key1116, 1), (key1233, -2), (key1003, 1), (key1003, 1), (key1152, -2), (key1152, -2), (key1243, 1), (key1243, 1), (key1009, -2), (key1159, 1), (key1159, 1), (key1125, -1), (key1125, -1), (key1236, 1), (key1236, 1), (key1152, 1), (key1152, 1), (key1243, -1), (key1243, -1), (key1017, -1), (key1017, -1), (key1073, 1), (key1073, 1), (key1022, 1), (key1022, 1), (key1080, -1), (key1080, -1)]

def rawRow5398 : Integer.Sparse Key := [(key1116, -1), (key1233, -1), (key1116, 2), (key1125, -1), (key1236, -1), (key1038, 2), (key1236, 2), (key1038, -1), (key1125, -1), (key1130, 2), (key1044, -1), (key1130, -1), (key1116, 1), (key1233, 1), (key1116, -2), (key1152, 1), (key1243, 1), (key1003, -2), (key1243, -2), (key1003, 1), (key1152, 1), (key1159, -2), (key1009, 1), (key1159, 1), (key1038, -1), (key1236, -1), (key1038, 1), (key1125, 1), (key1003, 1), (key1243, 1), (key1003, -1), (key1152, -1), (key1073, -1), (key1247, -1), (key1017, 1), (key1247, 1), (key1080, 1), (key1174, 1), (key1022, -1), (key1174, -1)]

def rawRow5399 : Integer.Sparse Key := [(key1233, -1), (key1116, -1), (key1116, 2), (key1236, -1), (key1125, -1), (key1236, 2), (key1038, 2), (key1125, -1), (key1038, -1), (key1130, 2), (key1130, -1), (key1044, -1), (key1233, 1), (key1116, 1), (key1116, -2), (key1243, 1), (key1152, 1), (key1243, -2), (key1003, -2), (key1152, 1), (key1003, 1), (key1159, -2), (key1159, 1), (key1009, 1), (key1236, -1), (key1038, -1), (key1125, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1152, -1), (key1003, -1), (key1247, -1), (key1073, -1), (key1247, 1), (key1017, 1), (key1174, 1), (key1080, 1), (key1174, -1), (key1022, -1)]

def rawRow5400 : Integer.Sparse Key := [(key1125, -1), (key1130, -1), (key1236, 2), (key1038, -1), (key1044, -1), (key1116, 2), (key1130, 2), (key1233, -1), (key1236, -1), (key1038, 2), (key1116, -1), (key1125, -1), (key1152, 1), (key1159, 1), (key1243, -2), (key1003, 1), (key1009, 1), (key1116, -2), (key1159, -2), (key1233, 1), (key1243, 1), (key1003, -2), (key1116, 1), (key1152, 1), (key1152, -1), (key1174, -1), (key1243, 1), (key1247, 1), (key1125, 1), (key1174, 1), (key1236, -1), (key1247, -1), (key1003, -1), (key1022, -1), (key1038, 1), (key1080, 1), (key1003, 1), (key1017, 1), (key1038, -1), (key1073, -1)]

def rawRow5401 : Integer.Sparse Key := [(key1130, -1), (key1125, -1), (key1236, 2), (key1044, -1), (key1038, -1), (key1130, 2), (key1116, 2), (key1236, -1), (key1233, -1), (key1038, 2), (key1125, -1), (key1116, -1), (key1159, 1), (key1152, 1), (key1243, -2), (key1009, 1), (key1003, 1), (key1159, -2), (key1116, -2), (key1243, 1), (key1233, 1), (key1003, -2), (key1152, 1), (key1116, 1), (key1174, -1), (key1152, -1), (key1247, 1), (key1243, 1), (key1174, 1), (key1125, 1), (key1247, -1), (key1236, -1), (key1022, -1), (key1003, -1), (key1080, 1), (key1038, 1), (key1017, 1), (key1003, 1), (key1073, -1), (key1038, -1)]

def rawRow5402 : Integer.Sparse Key := [(key1125, -1), (key1236, -1), (key1130, 2), (key1116, -1), (key1233, -1), (key1038, 2), (key1236, 2), (key1044, -1), (key1130, -1), (key1116, 2), (key1038, -1), (key1125, -1), (key1152, 1), (key1243, 1), (key1159, -2), (key1116, 1), (key1233, 1), (key1003, -2), (key1243, -2), (key1009, 1), (key1159, 1), (key1116, -2), (key1003, 1), (key1152, 1), (key1073, -1), (key1247, -1), (key1080, 1), (key1174, 1), (key1017, 1), (key1247, 1), (key1022, -1), (key1174, -1), (key1038, -1), (key1236, -1), (key1003, 1), (key1243, 1), (key1038, 1), (key1125, 1), (key1003, -1), (key1152, -1)]

def rawRow5403 : Integer.Sparse Key := [(key1236, -1), (key1125, -1), (key1130, 2), (key1233, -1), (key1116, -1), (key1236, 2), (key1038, 2), (key1130, -1), (key1044, -1), (key1116, 2), (key1125, -1), (key1038, -1), (key1243, 1), (key1152, 1), (key1159, -2), (key1233, 1), (key1116, 1), (key1243, -2), (key1003, -2), (key1159, 1), (key1009, 1), (key1116, -2), (key1152, 1), (key1003, 1), (key1247, -1), (key1073, -1), (key1174, 1), (key1080, 1), (key1247, 1), (key1017, 1), (key1174, -1), (key1022, -1), (key1236, -1), (key1038, -1), (key1243, 1), (key1003, 1), (key1125, 1), (key1038, 1), (key1152, -1), (key1003, -1)]

def rawRow5404 : Integer.Sparse Key := [(key1130, -1), (key1236, -1), (key1125, 2), (key1130, -1), (key1236, -1), (key1044, 2), (key1233, 2), (key1038, -1), (key1116, -1), (key1125, 2), (key1038, -1), (key1116, -1), (key1159, 1), (key1243, 1), (key1152, -2), (key1159, 1), (key1243, 1), (key1009, -2), (key1233, -2), (key1003, 1), (key1116, 1), (key1152, -2), (key1003, 1), (key1116, 1), (key1080, -1), (key1243, -1), (key1073, 1), (key1152, 1), (key1022, 1), (key1236, 1), (key1017, -1), (key1125, -1), (key1080, -1), (key1243, -1), (key1022, 1), (key1236, 1), (key1073, 1), (key1152, 1), (key1017, -1), (key1125, -1)]

def rawRow5405 : Integer.Sparse Key := [(key1236, -1), (key1130, -1), (key1125, 2), (key1236, -1), (key1130, -1), (key1233, 2), (key1044, 2), (key1116, -1), (key1038, -1), (key1125, 2), (key1116, -1), (key1038, -1), (key1243, 1), (key1159, 1), (key1152, -2), (key1243, 1), (key1159, 1), (key1233, -2), (key1009, -2), (key1116, 1), (key1003, 1), (key1152, -2), (key1116, 1), (key1003, 1), (key1243, -1), (key1080, -1), (key1152, 1), (key1073, 1), (key1236, 1), (key1022, 1), (key1125, -1), (key1017, -1), (key1243, -1), (key1080, -1), (key1236, 1), (key1022, 1), (key1152, 1), (key1073, 1), (key1125, -1), (key1017, -1)]

def rawRow5406 : Integer.Sparse Key := [(key1073, -1), (key1080, -1), (key1080, 2), (key1152, -1), (key1159, -1), (key1152, 2), (key1174, 2), (key1159, -1), (key1174, -1), (key1243, 2), (key1243, -1), (key1247, -1), (key1017, 1), (key1022, 1), (key1022, -2), (key1125, 1), (key1130, 1), (key1125, -2), (key1174, -2), (key1130, 1), (key1174, 1), (key1236, -2), (key1236, 1), (key1247, 1), (key1003, -1), (key1022, -1), (key1009, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1044, -1), (key1080, -1), (key1116, -1), (key1130, -1), (key1116, 1), (key1159, 1), (key1233, 1), (key1236, 1), (key1233, -1), (key1243, -1)]

def rawRow5407 : Integer.Sparse Key := [(key1080, -1), (key1073, -1), (key1080, 2), (key1159, -1), (key1152, -1), (key1174, 2), (key1152, 2), (key1174, -1), (key1159, -1), (key1243, 2), (key1247, -1), (key1243, -1), (key1022, 1), (key1017, 1), (key1022, -2), (key1130, 1), (key1125, 1), (key1174, -2), (key1125, -2), (key1174, 1), (key1130, 1), (key1236, -2), (key1247, 1), (key1236, 1), (key1022, -1), (key1003, -1), (key1022, 1), (key1009, 1), (key1080, 1), (key1038, 1), (key1080, -1), (key1044, -1), (key1130, -1), (key1116, -1), (key1159, 1), (key1116, 1), (key1236, 1), (key1233, 1), (key1243, -1), (key1233, -1)]

def rawRow5408 : Integer.Sparse Key := [(key1080, -1), (key1080, -1), (key1073, 2), (key1174, -1), (key1174, -1), (key1159, 2), (key1159, 2), (key1152, -1), (key1152, -1), (key1247, 2), (key1243, -1), (key1243, -1), (key1022, 1), (key1022, 1), (key1017, -2), (key1174, 1), (key1174, 1), (key1130, -2), (key1130, -2), (key1125, 1), (key1125, 1), (key1247, -2), (key1236, 1), (key1236, 1), (key1009, -1), (key1009, -1), (key1003, 1), (key1003, 1), (key1044, 1), (key1044, 1), (key1038, -1), (key1038, -1), (key1159, -1), (key1159, -1), (key1130, 1), (key1130, 1), (key1243, 1), (key1243, 1), (key1236, -1), (key1236, -1)]

def rawRow5409 : Integer.Sparse Key := [(key1152, -1), (key1159, -1), (key1243, 2), (key1073, -1), (key1080, -1), (key1152, 2), (key1174, 2), (key1243, -1), (key1247, -1), (key1080, 2), (key1159, -1), (key1174, -1), (key1125, 1), (key1130, 1), (key1236, -2), (key1017, 1), (key1022, 1), (key1125, -2), (key1174, -2), (key1236, 1), (key1247, 1), (key1022, -2), (key1130, 1), (key1174, 1), (key1116, -1), (key1130, -1), (key1233, 1), (key1236, 1), (key1116, 1), (key1159, 1), (key1233, -1), (key1243, -1), (key1003, -1), (key1022, -1), (key1038, 1), (key1080, 1), (key1009, 1), (key1022, 1), (key1044, -1), (key1080, -1)]

def rawRow5410 : Integer.Sparse Key := [(key1159, -1), (key1152, -1), (key1243, 2), (key1080, -1), (key1073, -1), (key1174, 2), (key1152, 2), (key1247, -1), (key1243, -1), (key1080, 2), (key1174, -1), (key1159, -1), (key1130, 1), (key1125, 1), (key1236, -2), (key1022, 1), (key1017, 1), (key1174, -2), (key1125, -2), (key1247, 1), (key1236, 1), (key1022, -2), (key1174, 1), (key1130, 1), (key1130, -1), (key1116, -1), (key1236, 1), (key1233, 1), (key1159, 1), (key1116, 1), (key1243, -1), (key1233, -1), (key1022, -1), (key1003, -1), (key1080, 1), (key1038, 1), (key1022, 1), (key1009, 1), (key1080, -1), (key1044, -1)]

def rawRow5411 : Integer.Sparse Key := [(key1152, -1), (key1243, -1), (key1159, 2), (key1152, -1), (key1243, -1), (key1073, 2), (key1247, 2), (key1080, -1), (key1174, -1), (key1159, 2), (key1080, -1), (key1174, -1), (key1125, 1), (key1236, 1), (key1130, -2), (key1125, 1), (key1236, 1), (key1017, -2), (key1247, -2), (key1022, 1), (key1174, 1), (key1130, -2), (key1022, 1), (key1174, 1), (key1038, -1), (key1236, -1), (key1044, 1), (key1130, 1), (key1003, 1), (key1243, 1), (key1009, -1), (key1159, -1), (key1038, -1), (key1236, -1), (key1003, 1), (key1243, 1), (key1044, 1), (key1130, 1), (key1009, -1), (key1159, -1)]

def rawRow5412 : Integer.Sparse Key := [(key1243, -1), (key1152, -1), (key1159, 2), (key1243, -1), (key1152, -1), (key1247, 2), (key1073, 2), (key1174, -1), (key1080, -1), (key1159, 2), (key1174, -1), (key1080, -1), (key1236, 1), (key1125, 1), (key1130, -2), (key1236, 1), (key1125, 1), (key1247, -2), (key1017, -2), (key1174, 1), (key1022, 1), (key1130, -2), (key1174, 1), (key1022, 1), (key1236, -1), (key1038, -1), (key1130, 1), (key1044, 1), (key1243, 1), (key1003, 1), (key1159, -1), (key1009, -1), (key1236, -1), (key1038, -1), (key1243, 1), (key1003, 1), (key1130, 1), (key1044, 1), (key1159, -1), (key1009, -1)]

def rawRow5413 : Integer.Sparse Key := [(key1159, -1), (key1243, -1), (key1152, 2), (key1174, -1), (key1247, -1), (key1080, 2), (key1243, 2), (key1073, -1), (key1152, -1), (key1174, 2), (key1080, -1), (key1159, -1), (key1130, 1), (key1236, 1), (key1125, -2), (key1174, 1), (key1247, 1), (key1022, -2), (key1236, -2), (key1017, 1), (key1125, 1), (key1174, -2), (key1022, 1), (key1130, 1), (key1044, -1), (key1233, -1), (key1038, 1), (key1116, 1), (key1009, 1), (key1233, 1), (key1003, -1), (key1116, -1), (key1080, -1), (key1243, -1), (key1022, 1), (key1236, 1), (key1080, 1), (key1159, 1), (key1022, -1), (key1130, -1)]

def rawRow5414 : Integer.Sparse Key := [(key1243, -1), (key1159, -1), (key1152, 2), (key1247, -1), (key1174, -1), (key1243, 2), (key1080, 2), (key1152, -1), (key1073, -1), (key1174, 2), (key1159, -1), (key1080, -1), (key1236, 1), (key1130, 1), (key1125, -2), (key1247, 1), (key1174, 1), (key1236, -2), (key1022, -2), (key1125, 1), (key1017, 1), (key1174, -2), (key1130, 1), (key1022, 1), (key1233, -1), (key1044, -1), (key1116, 1), (key1038, 1), (key1233, 1), (key1009, 1), (key1116, -1), (key1003, -1), (key1243, -1), (key1080, -1), (key1236, 1), (key1022, 1), (key1159, 1), (key1080, 1), (key1130, -1), (key1022, -1)]

def rawRow5415 : Integer.Sparse Key := [(key1174, -1), (key1174, -1), (key1247, 2), (key1080, -1), (key1080, -1), (key1159, 2), (key1159, 2), (key1243, -1), (key1243, -1), (key1073, 2), (key1152, -1), (key1152, -1), (key1174, 1), (key1174, 1), (key1247, -2), (key1022, 1), (key1022, 1), (key1130, -2), (key1130, -2), (key1236, 1), (key1236, 1), (key1017, -2), (key1125, 1), (key1125, 1), (key1159, -1), (key1159, -1), (key1243, 1), (key1243, 1), (key1130, 1), (key1130, 1), (key1236, -1), (key1236, -1), (key1009, -1), (key1009, -1), (key1044, 1), (key1044, 1), (key1003, 1), (key1003, 1), (key1038, -1), (key1038, -1)]

def rawRow5416 : Integer.Sparse Key := [(key1174, -1), (key1247, -1), (key1174, 2), (key1159, -1), (key1243, -1), (key1080, 2), (key1243, 2), (key1080, -1), (key1159, -1), (key1152, 2), (key1073, -1), (key1152, -1), (key1174, 1), (key1247, 1), (key1174, -2), (key1130, 1), (key1236, 1), (key1022, -2), (key1236, -2), (key1022, 1), (key1130, 1), (key1125, -2), (key1017, 1), (key1125, 1), (key1080, -1), (key1243, -1), (key1080, 1), (key1159, 1), (key1022, 1), (key1236, 1), (key1022, -1), (key1130, -1), (key1044, -1), (key1233, -1), (key1009, 1), (key1233, 1), (key1038, 1), (key1116, 1), (key1003, -1), (key1116, -1)]

def rawRow5417 : Integer.Sparse Key := [(key1247, -1), (key1174, -1), (key1174, 2), (key1243, -1), (key1159, -1), (key1243, 2), (key1080, 2), (key1159, -1), (key1080, -1), (key1152, 2), (key1152, -1), (key1073, -1), (key1247, 1), (key1174, 1), (key1174, -2), (key1236, 1), (key1130, 1), (key1236, -2), (key1022, -2), (key1130, 1), (key1022, 1), (key1125, -2), (key1125, 1), (key1017, 1), (key1243, -1), (key1080, -1), (key1159, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1130, -1), (key1022, -1), (key1233, -1), (key1044, -1), (key1233, 1), (key1009, 1), (key1116, 1), (key1038, 1), (key1116, -1), (key1003, -1)]

def rawRow5418 : Integer.Sparse Key := [(key25, -1), (key25, -1), (key27, 2), (key25, -1), (key25, -1), (key37, 2), (key37, 2), (key40, -1), (key40, -1), (key27, 2), (key40, -1), (key40, -1), (key50, 1), (key50, 1), (key52, -2), (key50, 1), (key50, 1), (key76, -2), (key76, -2), (key81, 1), (key81, 1), (key52, -2), (key81, 1), (key81, 1), (key117, -1), (key117, -1), (key120, 1), (key120, 1), (key139, 1), (key139, 1), (key144, -1), (key144, -1), (key117, -1), (key117, -1), (key139, 1), (key139, 1), (key120, 1), (key120, 1), (key144, -1), (key144, -1)]

def rawRow5419 : Integer.Sparse Key := [(key25, -1), (key27, -1), (key25, 2), (key37, -1), (key40, -1), (key25, 2), (key40, 2), (key25, -1), (key37, -1), (key40, 2), (key27, -1), (key40, -1), (key50, 1), (key52, 1), (key50, -2), (key76, 1), (key81, 1), (key50, -2), (key81, -2), (key50, 1), (key76, 1), (key81, -2), (key52, 1), (key81, 1), (key107, -1), (key120, -1), (key107, 1), (key117, 1), (key107, 1), (key144, 1), (key107, -1), (key139, -1), (key139, -1), (key162, -1), (key117, 1), (key162, 1), (key144, 1), (key162, 1), (key120, -1), (key162, -1)]

def rawRow5420 : Integer.Sparse Key := [(key27, -1), (key25, -1), (key25, 2), (key40, -1), (key37, -1), (key40, 2), (key25, 2), (key37, -1), (key25, -1), (key40, 2), (key40, -1), (key27, -1), (key52, 1), (key50, 1), (key50, -2), (key81, 1), (key76, 1), (key81, -2), (key50, -2), (key76, 1), (key50, 1), (key81, -2), (key81, 1), (key52, 1), (key120, -1), (key107, -1), (key117, 1), (key107, 1), (key144, 1), (key107, 1), (key139, -1), (key107, -1), (key162, -1), (key139, -1), (key162, 1), (key117, 1), (key162, 1), (key144, 1), (key162, -1), (key120, -1)]

def rawRow5421 : Integer.Sparse Key := [(key37, -1), (key40, -1), (key40, 2), (key25, -1), (key27, -1), (key25, 2), (key40, 2), (key27, -1), (key40, -1), (key25, 2), (key25, -1), (key37, -1), (key76, 1), (key81, 1), (key81, -2), (key50, 1), (key52, 1), (key50, -2), (key81, -2), (key52, 1), (key81, 1), (key50, -2), (key50, 1), (key76, 1), (key139, -1), (key162, -1), (key144, 1), (key162, 1), (key117, 1), (key162, 1), (key120, -1), (key162, -1), (key107, -1), (key120, -1), (key107, 1), (key144, 1), (key107, 1), (key117, 1), (key107, -1), (key139, -1)]

def rawRow5422 : Integer.Sparse Key := [(key40, -1), (key37, -1), (key40, 2), (key27, -1), (key25, -1), (key40, 2), (key25, 2), (key40, -1), (key27, -1), (key25, 2), (key37, -1), (key25, -1), (key81, 1), (key76, 1), (key81, -2), (key52, 1), (key50, 1), (key81, -2), (key50, -2), (key81, 1), (key52, 1), (key50, -2), (key76, 1), (key50, 1), (key162, -1), (key139, -1), (key162, 1), (key144, 1), (key162, 1), (key117, 1), (key162, -1), (key120, -1), (key120, -1), (key107, -1), (key144, 1), (key107, 1), (key117, 1), (key107, 1), (key139, -1), (key107, -1)]

def rawRow5423 : Integer.Sparse Key := [(key40, -1), (key40, -1), (key37, 2), (key40, -1), (key40, -1), (key27, 2), (key27, 2), (key25, -1), (key25, -1), (key37, 2), (key25, -1), (key25, -1), (key81, 1), (key81, 1), (key76, -2), (key81, 1), (key81, 1), (key52, -2), (key52, -2), (key50, 1), (key50, 1), (key76, -2), (key50, 1), (key50, 1), (key144, -1), (key144, -1), (key139, 1), (key139, 1), (key120, 1), (key120, 1), (key117, -1), (key117, -1), (key144, -1), (key144, -1), (key120, 1), (key120, 1), (key139, 1), (key139, 1), (key117, -1), (key117, -1)]

def rawRow5424 : Integer.Sparse Key := [(key379, -1), (key379, -1), (key382, 2), (key430, -1), (key430, -1), (key464, 2), (key464, 2), (key466, -1), (key466, -1), (key461, 2), (key483, -1), (key483, -1), (key210, 1), (key210, 1), (key213, -2), (key430, 1), (key430, 1), (key590, -2), (key590, -2), (key592, 1), (key592, 1), (key461, -2), (key609, 1), (key609, 1), (key37, -1), (key37, -1), (key40, 1), (key40, 1), (key76, 1), (key76, 1), (key81, -1), (key81, -1), (key117, -1), (key117, -1), (key139, 1), (key139, 1), (key197, 1), (key197, 1), (key201, -1), (key201, -1)]

def rawRow5425 : Integer.Sparse Key := [(key379, -1), (key382, -1), (key379, 2), (key464, -1), (key466, -1), (key430, 2), (key466, 2), (key430, -1), (key464, -1), (key483, 2), (key461, -1), (key483, -1), (key210, 1), (key213, 1), (key210, -2), (key590, 1), (key592, 1), (key430, -2), (key592, -2), (key430, 1), (key590, 1), (key609, -2), (key461, 1), (key609, 1), (key25, -1), (key40, -1), (key25, 1), (key37, 1), (key50, 1), (key81, 1), (key50, -1), (key76, -1), (key139, -1), (key162, -1), (key117, 1), (key162, 1), (key201, 1), (key204, 1), (key197, -1), (key204, -1)]

def rawRow5426 : Integer.Sparse Key := [(key382, -1), (key379, -1), (key379, 2), (key466, -1), (key464, -1), (key466, 2), (key430, 2), (key464, -1), (key430, -1), (key483, 2), (key483, -1), (key461, -1), (key213, 1), (key210, 1), (key210, -2), (key592, 1), (key590, 1), (key592, -2), (key430, -2), (key590, 1), (key430, 1), (key609, -2), (key609, 1), (key461, 1), (key40, -1), (key25, -1), (key37, 1), (key25, 1), (key81, 1), (key50, 1), (key76, -1), (key50, -1), (key162, -1), (key139, -1), (key162, 1), (key117, 1), (key204, 1), (key201, 1), (key204, -1), (key197, -1)]

def rawRow5427 : Integer.Sparse Key := [(key430, -1), (key430, -1), (key461, 2), (key379, -1), (key379, -1), (key464, 2), (key464, 2), (key483, -1), (key483, -1), (key382, 2), (key466, -1), (key466, -1), (key430, 1), (key430, 1), (key461, -2), (key210, 1), (key210, 1), (key590, -2), (key590, -2), (key609, 1), (key609, 1), (key213, -2), (key592, 1), (key592, 1), (key464, -1), (key464, -1), (key483, 1), (key483, 1), (key590, 1), (key590, 1), (key609, -1), (key609, -1), (key37, -1), (key37, -1), (key76, 1), (key76, 1), (key40, 1), (key40, 1), (key81, -1), (key81, -1)]

def rawRow5428 : Integer.Sparse Key := [(key430, -1), (key461, -1), (key430, 2), (key464, -1), (key483, -1), (key379, 2), (key483, 2), (key379, -1), (key464, -1), (key466, 2), (key382, -1), (key466, -1), (key430, 1), (key461, 1), (key430, -2), (key590, 1), (key609, 1), (key210, -2), (key609, -2), (key210, 1), (key590, 1), (key592, -2), (key213, 1), (key592, 1), (key379, -1), (key483, -1), (key379, 1), (key464, 1), (key210, 1), (key609, 1), (key210, -1), (key590, -1), (key565, -1), (key615, -1), (key215, 1), (key615, 1), (key81, 1), (key162, 1), (key40, -1), (key162, -1)]

def rawRow5429 : Integer.Sparse Key := [(key461, -1), (key430, -1), (key430, 2), (key483, -1), (key464, -1), (key483, 2), (key379, 2), (key464, -1), (key379, -1), (key466, 2), (key466, -1), (key382, -1), (key461, 1), (key430, 1), (key430, -2), (key609, 1), (key590, 1), (key609, -2), (key210, -2), (key590, 1), (key210, 1), (key592, -2), (key592, 1), (key213, 1), (key483, -1), (key379, -1), (key464, 1), (key379, 1), (key609, 1), (key210, 1), (key590, -1), (key210, -1), (key615, -1), (key565, -1), (key615, 1), (key215, 1), (key162, 1), (key81, 1), (key162, -1), (key40, -1)]

def rawRow5430 : Integer.Sparse Key := [(key464, -1), (key466, -1), (key483, 2), (key379, -1), (key382, -1), (key430, 2), (key466, 2), (key461, -1), (key483, -1), (key379, 2), (key430, -1), (key464, -1), (key590, 1), (key592, 1), (key609, -2), (key210, 1), (key213, 1), (key430, -2), (key592, -2), (key461, 1), (key609, 1), (key210, -2), (key430, 1), (key590, 1), (key590, -1), (key612, -1), (key609, 1), (key615, 1), (key464, 1), (key612, 1), (key483, -1), (key615, -1), (key210, -1), (key217, -1), (key379, 1), (key567, 1), (key25, 1), (key37, 1), (key50, -1), (key76, -1)]

def rawRow5478 : Integer.Sparse Key := [(key10, -4), (key13, 2), (key13, 2), (key13, 2), (key13, 2), (key15, -4), (key93, 2), (key96, -1), (key96, -1), (key93, 2), (key158, -1), (key158, -1), (key96, -1), (key96, -1), (key158, -1), (key158, -1), (key163, 2), (key163, 2), (key169, -1), (key169, -1), (key170, 2), (key169, -1), (key169, -1), (key189, 2), (key189, 2), (key192, -1), (key192, -1), (key170, 2), (key192, -1), (key192, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined289_part2 : Sparse := [([1, 2, 0, -1, -1, 0, 0], -9)]

end MUB6.TaoCertificate

end OAI
end


