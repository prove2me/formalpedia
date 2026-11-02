-- Prove2me | Definitions.Def_OAIQ106D177
-- name    : OAIQ106D177
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:40:27.629754+00:00
-- url     : https://prove2.me/theorems/40825b46-15b0-4f56-929a-6f3bcc2fb037
-- title:
--   Definitions bundle OAIQ106D177 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 103 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow6596`, `OAI.MUB6.Certificate.GramRows.rawRow6597`, `OAI.MUB6.Certificate.GramRows.rawRow6598`, `OAI.MUB6.Certificate.GramRows.rawRow6599`, `OAI.MUB6.Certificate.GramRows.rawRow66`, `OAI.MUB6.Certificate.GramRows.rawRow6600`, `OAI.MUB6.Certificate.GramRows.rawRow6601`, `OAI.MUB6.Certificate.GramRows.rawRow6602`, `OAI.MUB6.Certificate.GramRows.rawRow6603`, `OAI.MUB6.Certificate.GramRows.rawRow6604`, `OAI.MUB6.Certificate.GramRows.rawRow6605`, `OAI.MUB6.Certificate.GramRows.rawRow6606`, `OAI.MUB6.Certificate.GramRows.rawRow6607`, `OAI.MUB6.Certificate.GramRows.rawRow6608`, `OAI.MUB6.Certificate.GramRows.rawRow6609`, `OAI.MUB6.Certificate.GramRows.rawRow6610`, `OAI.MUB6.Certificate.GramRows.rawRow6611`, `OAI.MUB6.Certificate.GramRows.rawRow6612`, `OAI.MUB6.Certificate.GramRows.rawRow6613`, `OAI.MUB6.Certificate.GramRows.rawRow6614`, `OAI.MUB6.Certificate.GramRows.rawRow6615`, `OAI.MUB6.Certificate.GramRows.rawRow6616`, `OAI.MUB6.Certificate.GramRows.rawRow6617`, `OAI.MUB6.Certificate.GramRows.rawRow6618`, `OAI.MUB6.Certificate.GramRows.rawRow6619`, `OAI.MUB6.Certificate.GramRows.rawRow662`, `OAI.MUB6.Certificate.GramRows.rawRow6620`, `OAI.MUB6.Certificate.GramRows.rawRow6621`, `OAI.MUB6.Certificate.GramRows.rawRow6622`, `OAI.MUB6.Certificate.GramRows.rawRow6623`, `OAI.MUB6.Certificate.GramRows.rawRow6624`, `OAI.MUB6.Certificate.GramRows.rawRow6625`, `OAI.MUB6.Certificate.GramRows.rawRow6626`, `OAI.MUB6.Certificate.GramRows.rawRow6627`, `OAI.MUB6.Certificate.GramRows.rawRow6628`, `OAI.MUB6.Certificate.GramRows.rawRow6629`, `OAI.MUB6.Certificate.GramRows.rawRow663`, `OAI.MUB6.Certificate.GramRows.rawRow6630`, `OAI.MUB6.Certificate.GramRows.rawRow6631`, `OAI.MUB6.Certificate.GramRows.rawRow6632` and 63 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block17.lean), [`MutuallyUnbiased_GramRows_Block18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block18.lean), [`MutuallyUnbiased_GramRows_Block75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block75.lean), [`MutuallyUnbiased_GramRows_Block76`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block76.lean), [`MutuallyUnbiased_GramRows_Block81`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block81.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D087`, `OAIQ106D089` and `OAIQ106D090` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow8` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow66 : Integer.Sparse Key := [(key1573, -1), (key1596, -1), (key1573, 2), (key1655, 1), (key1667, 1), (key1546, -1), (key1655, -1), (key1659, -2), (key1559, 1), (key1659, 1), (key1424, 1), (key1447, 1), (key1424, -2), (key1813, -1), (key1825, -1), (key1316, 1), (key1813, 1), (key1817, 2), (key1329, -1), (key1817, -1), (key1455, -1), (key1466, -1), (key1391, 1), (key1455, 1), (key1788, 1), (key1798, 1), (key1296, -1), (key1788, -1), (key1780, -1), (key1841, -1), (key1345, 1), (key1841, 1), (key1457, 2), (key1397, -1), (key1457, -1), (key1790, -2), (key1302, 1), (key1790, 1), (key1774, 1), (key1839, 1), (key1339, -1), (key1839, -1)]

def rawRow67 : Integer.Sparse Key := [(key1596, -1), (key1573, -1), (key1573, 2), (key1667, 1), (key1655, 1), (key1655, -1), (key1546, -1), (key1659, -2), (key1659, 1), (key1559, 1), (key1447, 1), (key1424, 1), (key1424, -2), (key1825, -1), (key1813, -1), (key1813, 1), (key1316, 1), (key1817, 2), (key1817, -1), (key1329, -1), (key1466, -1), (key1455, -1), (key1455, 1), (key1391, 1), (key1798, 1), (key1788, 1), (key1788, -1), (key1296, -1), (key1841, -1), (key1780, -1), (key1841, 1), (key1345, 1), (key1457, 2), (key1457, -1), (key1397, -1), (key1790, -2), (key1790, 1), (key1302, 1), (key1839, 1), (key1774, 1), (key1839, -1), (key1339, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow662 : Integer.Sparse Key := [(key1453, -2), (key1389, -2), (key1453, -2), (key1422, 1), (key1453, 1), (key1389, 1), (key1453, 1), (key1389, 1), (key1422, 1), (key1653, 2), (key1544, 2), (key1653, 2), (key1571, -1), (key1653, -1), (key1544, -1), (key1653, -1), (key1544, -1), (key1571, -1), (key1811, -1), (key1838, -1), (key1770, -1), (key1838, -1), (key1770, -1), (key1811, -1), (key1786, 1), (key1838, 1), (key1770, 1), (key1838, 1), (key1770, 1), (key1786, 1)]

def rawRow663 : Integer.Sparse Key := [(key1453, -2), (key1453, -2), (key1389, -2), (key1453, 1), (key1422, 1), (key1453, 1), (key1389, 1), (key1422, 1), (key1389, 1), (key1653, 2), (key1653, 2), (key1544, 2), (key1653, -1), (key1571, -1), (key1653, -1), (key1544, -1), (key1571, -1), (key1544, -1), (key1838, -1), (key1811, -1), (key1838, -1), (key1770, -1), (key1811, -1), (key1770, -1), (key1838, 1), (key1786, 1), (key1838, 1), (key1770, 1), (key1786, 1), (key1770, 1)]

def rawRow665 : Integer.Sparse Key := [(key1294, -2), (key1786, -2), (key1786, -2), (key1294, 1), (key1294, 1), (key1571, 1), (key1571, 1), (key1786, 1), (key1786, 1), (key1314, 2), (key1811, 2), (key1811, 2), (key1314, -1), (key1314, -1), (key1422, -1), (key1422, -1), (key1811, -1), (key1811, -1), (key1335, -1), (key1335, -1), (key1653, -1), (key1653, -1), (key1838, -1), (key1838, -1), (key1335, 1), (key1335, 1), (key1453, 1), (key1453, 1), (key1838, 1), (key1838, 1)]

def rawRow666 : Integer.Sparse Key := [(key1786, -2), (key1294, -2), (key1786, -2), (key1571, 1), (key1786, 1), (key1294, 1), (key1786, 1), (key1294, 1), (key1571, 1), (key1811, 2), (key1314, 2), (key1811, 2), (key1422, -1), (key1811, -1), (key1314, -1), (key1811, -1), (key1314, -1), (key1422, -1), (key1653, -1), (key1838, -1), (key1335, -1), (key1838, -1), (key1335, -1), (key1653, -1), (key1453, 1), (key1838, 1), (key1335, 1), (key1838, 1), (key1335, 1), (key1453, 1)]

def rawRow667 : Integer.Sparse Key := [(key1786, -2), (key1786, -2), (key1294, -2), (key1786, 1), (key1571, 1), (key1786, 1), (key1294, 1), (key1571, 1), (key1294, 1), (key1811, 2), (key1811, 2), (key1314, 2), (key1811, -1), (key1422, -1), (key1811, -1), (key1314, -1), (key1422, -1), (key1314, -1), (key1838, -1), (key1653, -1), (key1838, -1), (key1335, -1), (key1653, -1), (key1335, -1), (key1838, 1), (key1453, 1), (key1838, 1), (key1335, 1), (key1453, 1), (key1335, 1)]

def rawRow668 : Integer.Sparse Key := [(key1544, -2), (key1653, -2), (key1653, -2), (key1770, 1), (key1770, 1), (key1811, 1), (key1811, 1), (key1838, 1), (key1838, 1), (key1389, 2), (key1453, 2), (key1453, 2), (key1770, -1), (key1770, -1), (key1786, -1), (key1786, -1), (key1838, -1), (key1838, -1), (key1389, -1), (key1389, -1), (key1422, -1), (key1422, -1), (key1453, -1), (key1453, -1), (key1544, 1), (key1544, 1), (key1571, 1), (key1571, 1), (key1653, 1), (key1653, 1)]

def rawRow669 : Integer.Sparse Key := [(key1653, -2), (key1544, -2), (key1653, -2), (key1811, 1), (key1838, 1), (key1770, 1), (key1838, 1), (key1770, 1), (key1811, 1), (key1453, 2), (key1389, 2), (key1453, 2), (key1786, -1), (key1838, -1), (key1770, -1), (key1838, -1), (key1770, -1), (key1786, -1), (key1422, -1), (key1453, -1), (key1389, -1), (key1453, -1), (key1389, -1), (key1422, -1), (key1571, 1), (key1653, 1), (key1544, 1), (key1653, 1), (key1544, 1), (key1571, 1)]

def rawRow670 : Integer.Sparse Key := [(key1653, -2), (key1653, -2), (key1544, -2), (key1838, 1), (key1811, 1), (key1838, 1), (key1770, 1), (key1811, 1), (key1770, 1), (key1453, 2), (key1453, 2), (key1389, 2), (key1838, -1), (key1786, -1), (key1838, -1), (key1770, -1), (key1786, -1), (key1770, -1), (key1453, -1), (key1422, -1), (key1453, -1), (key1389, -1), (key1422, -1), (key1389, -1), (key1653, 1), (key1571, 1), (key1653, 1), (key1544, 1), (key1571, 1), (key1544, 1)]

def rawRow671 : Integer.Sparse Key := [(key1314, -2), (key1811, -2), (key1811, -2), (key1335, 1), (key1335, 1), (key1653, 1), (key1653, 1), (key1838, 1), (key1838, 1), (key1294, 2), (key1786, 2), (key1786, 2), (key1335, -1), (key1335, -1), (key1453, -1), (key1453, -1), (key1838, -1), (key1838, -1), (key1294, -1), (key1294, -1), (key1571, -1), (key1571, -1), (key1786, -1), (key1786, -1), (key1314, 1), (key1314, 1), (key1422, 1), (key1422, 1), (key1811, 1), (key1811, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow673 : Integer.Sparse Key := [(key1811, -2), (key1811, -2), (key1314, -2), (key1838, 1), (key1653, 1), (key1838, 1), (key1335, 1), (key1653, 1), (key1335, 1), (key1786, 2), (key1786, 2), (key1294, 2), (key1838, -1), (key1453, -1), (key1838, -1), (key1335, -1), (key1453, -1), (key1335, -1), (key1786, -1), (key1571, -1), (key1786, -1), (key1294, -1), (key1571, -1), (key1294, -1), (key1811, 1), (key1422, 1), (key1811, 1), (key1314, 1), (key1422, 1), (key1314, 1)]

def rawRow676 : Integer.Sparse Key := [(key246, -6), (key246, 2), (key234, 2), (key246, 2), (key314, 6), (key314, -2), (key300, -2), (key314, -2), (key433, -2), (key404, -2), (key433, -2), (key433, 2), (key383, 2), (key433, 2)]

def rawRow677 : Integer.Sparse Key := [(key246, -6), (key246, 2), (key246, 2), (key234, 2), (key314, 6), (key314, -2), (key314, -2), (key300, -2), (key433, -2), (key433, -2), (key404, -2), (key433, 2), (key433, 2), (key383, 2)]

def rawRow679 : Integer.Sparse Key := [(key314, -6), (key300, 2), (key314, 2), (key314, 2), (key404, 6), (key234, -2), (key404, -2), (key404, -2), (key314, -2), (key433, -2), (key433, -2), (key246, 2), (key433, 2), (key433, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6596 : Integer.Sparse Key := [(key2999, -2), (key3001, 1), (key3004, 1), (key2656, -2), (key2751, 1), (key2915, 1), (key2650, 1), (key2655, 1), (key2739, 1), (key2899, 1), (key2749, -2), (key2906, -2), (key2946, 2), (key2964, -1), (key2994, -1), (key2656, 2), (key2751, -1), (key2915, -1), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, 2), (key2833, 2), (key2940, -1), (key2945, -1), (key2952, 1), (key2978, 1), (key2650, -1), (key2655, -1), (key2749, 1), (key2906, 1), (key2620, 1), (key2643, 1), (key2730, -1), (key2833, -1), (key2672, 1), (key2707, 1), (key2787, -1), (key2810, -1)]

def rawRow6597 : Integer.Sparse Key := [(key2999, -2), (key3004, 1), (key3001, 1), (key2656, -2), (key2915, 1), (key2751, 1), (key2655, 1), (key2650, 1), (key2899, 1), (key2739, 1), (key2906, -2), (key2749, -2), (key2946, 2), (key2994, -1), (key2964, -1), (key2656, 2), (key2915, -1), (key2751, -1), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, 2), (key2730, 2), (key2945, -1), (key2940, -1), (key2978, 1), (key2952, 1), (key2655, -1), (key2650, -1), (key2906, 1), (key2749, 1), (key2643, 1), (key2620, 1), (key2833, -1), (key2730, -1), (key2707, 1), (key2672, 1), (key2810, -1), (key2787, -1)]

def rawRow6598 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1302, 2), (key1316, -1), (key1316, -1), (key1337, 2), (key1337, 2), (key1339, -1), (key1339, -1), (key1329, 2), (key1345, -1), (key1345, -1), (key1391, 1), (key1391, 1), (key1397, -2), (key1546, 1), (key1546, 1), (key1772, -2), (key1772, -2), (key1774, 1), (key1774, 1), (key1559, -2), (key1780, 1), (key1780, 1), (key1455, -1), (key1455, -1), (key1457, 1), (key1457, 1), (key1788, 1), (key1788, 1), (key1790, -1), (key1790, -1), (key1655, -1), (key1655, -1), (key1813, 1), (key1813, 1), (key1659, 1), (key1659, 1), (key1817, -1), (key1817, -1)]

def rawRow6599 : Integer.Sparse Key := [(key1296, -1), (key1302, -1), (key1296, 2), (key1337, -1), (key1339, -1), (key1316, 2), (key1339, 2), (key1316, -1), (key1337, -1), (key1345, 2), (key1329, -1), (key1345, -1), (key1391, 1), (key1397, 1), (key1391, -2), (key1772, 1), (key1774, 1), (key1546, -2), (key1774, -2), (key1546, 1), (key1772, 1), (key1780, -2), (key1559, 1), (key1780, 1), (key1424, -1), (key1457, -1), (key1424, 1), (key1455, 1), (key1573, 1), (key1790, 1), (key1573, -1), (key1788, -1), (key1813, -1), (key1839, -1), (key1655, 1), (key1839, 1), (key1817, 1), (key1841, 1), (key1659, -1), (key1841, -1)]

def rawRow6600 : Integer.Sparse Key := [(key1302, -1), (key1296, -1), (key1296, 2), (key1339, -1), (key1337, -1), (key1339, 2), (key1316, 2), (key1337, -1), (key1316, -1), (key1345, 2), (key1345, -1), (key1329, -1), (key1397, 1), (key1391, 1), (key1391, -2), (key1774, 1), (key1772, 1), (key1774, -2), (key1546, -2), (key1772, 1), (key1546, 1), (key1780, -2), (key1780, 1), (key1559, 1), (key1457, -1), (key1424, -1), (key1455, 1), (key1424, 1), (key1790, 1), (key1573, 1), (key1788, -1), (key1573, -1), (key1839, -1), (key1813, -1), (key1839, 1), (key1655, 1), (key1841, 1), (key1817, 1), (key1841, -1), (key1659, -1)]

def rawRow6601 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1329, 2), (key1296, -1), (key1296, -1), (key1337, 2), (key1337, 2), (key1345, -1), (key1345, -1), (key1302, 2), (key1339, -1), (key1339, -1), (key1546, 1), (key1546, 1), (key1559, -2), (key1391, 1), (key1391, 1), (key1772, -2), (key1772, -2), (key1780, 1), (key1780, 1), (key1397, -2), (key1774, 1), (key1774, 1), (key1655, -1), (key1655, -1), (key1659, 1), (key1659, 1), (key1813, 1), (key1813, 1), (key1817, -1), (key1817, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1457, 1), (key1457, 1), (key1790, -1), (key1790, -1)]

def rawRow6602 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1316, 2), (key1337, -1), (key1345, -1), (key1296, 2), (key1345, 2), (key1296, -1), (key1337, -1), (key1339, 2), (key1302, -1), (key1339, -1), (key1546, 1), (key1559, 1), (key1546, -2), (key1772, 1), (key1780, 1), (key1391, -2), (key1780, -2), (key1391, 1), (key1772, 1), (key1774, -2), (key1397, 1), (key1774, 1), (key1573, -1), (key1659, -1), (key1573, 1), (key1655, 1), (key1424, 1), (key1817, 1), (key1424, -1), (key1813, -1), (key1788, -1), (key1841, -1), (key1455, 1), (key1841, 1), (key1790, 1), (key1839, 1), (key1457, -1), (key1839, -1)]

def rawRow6603 : Integer.Sparse Key := [(key1329, -1), (key1316, -1), (key1316, 2), (key1345, -1), (key1337, -1), (key1345, 2), (key1296, 2), (key1337, -1), (key1296, -1), (key1339, 2), (key1339, -1), (key1302, -1), (key1559, 1), (key1546, 1), (key1546, -2), (key1780, 1), (key1772, 1), (key1780, -2), (key1391, -2), (key1772, 1), (key1391, 1), (key1774, -2), (key1774, 1), (key1397, 1), (key1659, -1), (key1573, -1), (key1655, 1), (key1573, 1), (key1817, 1), (key1424, 1), (key1813, -1), (key1424, -1), (key1841, -1), (key1788, -1), (key1841, 1), (key1455, 1), (key1839, 1), (key1790, 1), (key1839, -1), (key1457, -1)]

def rawRow6604 : Integer.Sparse Key := [(key1337, -1), (key1339, -1), (key1345, 2), (key1296, -1), (key1302, -1), (key1316, 2), (key1339, 2), (key1329, -1), (key1345, -1), (key1296, 2), (key1316, -1), (key1337, -1), (key1772, 1), (key1774, 1), (key1780, -2), (key1391, 1), (key1397, 1), (key1546, -2), (key1774, -2), (key1559, 1), (key1780, 1), (key1391, -2), (key1546, 1), (key1772, 1), (key1813, -1), (key1839, -1), (key1817, 1), (key1841, 1), (key1655, 1), (key1839, 1), (key1659, -1), (key1841, -1), (key1424, -1), (key1457, -1), (key1573, 1), (key1790, 1), (key1424, 1), (key1455, 1), (key1573, -1), (key1788, -1)]

def rawRow6605 : Integer.Sparse Key := [(key1339, -1), (key1337, -1), (key1345, 2), (key1302, -1), (key1296, -1), (key1339, 2), (key1316, 2), (key1345, -1), (key1329, -1), (key1296, 2), (key1337, -1), (key1316, -1), (key1774, 1), (key1772, 1), (key1780, -2), (key1397, 1), (key1391, 1), (key1774, -2), (key1546, -2), (key1780, 1), (key1559, 1), (key1391, -2), (key1772, 1), (key1546, 1), (key1839, -1), (key1813, -1), (key1841, 1), (key1817, 1), (key1839, 1), (key1655, 1), (key1841, -1), (key1659, -1), (key1457, -1), (key1424, -1), (key1790, 1), (key1573, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

def rawRow6606 : Integer.Sparse Key := [(key1337, -1), (key1345, -1), (key1339, 2), (key1316, -1), (key1329, -1), (key1296, 2), (key1345, 2), (key1302, -1), (key1339, -1), (key1316, 2), (key1296, -1), (key1337, -1), (key1772, 1), (key1780, 1), (key1774, -2), (key1546, 1), (key1559, 1), (key1391, -2), (key1780, -2), (key1397, 1), (key1774, 1), (key1546, -2), (key1391, 1), (key1772, 1), (key1788, -1), (key1841, -1), (key1790, 1), (key1839, 1), (key1455, 1), (key1841, 1), (key1457, -1), (key1839, -1), (key1573, -1), (key1659, -1), (key1424, 1), (key1817, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

def rawRow6607 : Integer.Sparse Key := [(key1345, -1), (key1337, -1), (key1339, 2), (key1329, -1), (key1316, -1), (key1345, 2), (key1296, 2), (key1339, -1), (key1302, -1), (key1316, 2), (key1337, -1), (key1296, -1), (key1780, 1), (key1772, 1), (key1774, -2), (key1559, 1), (key1546, 1), (key1780, -2), (key1391, -2), (key1774, 1), (key1397, 1), (key1546, -2), (key1772, 1), (key1391, 1), (key1841, -1), (key1788, -1), (key1839, 1), (key1790, 1), (key1841, 1), (key1455, 1), (key1839, -1), (key1457, -1), (key1659, -1), (key1573, -1), (key1817, 1), (key1424, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

def rawRow6608 : Integer.Sparse Key := [(key1339, -1), (key1345, -1), (key1337, 2), (key1339, -1), (key1345, -1), (key1302, 2), (key1329, 2), (key1296, -1), (key1316, -1), (key1337, 2), (key1296, -1), (key1316, -1), (key1774, 1), (key1780, 1), (key1772, -2), (key1774, 1), (key1780, 1), (key1397, -2), (key1559, -2), (key1391, 1), (key1546, 1), (key1772, -2), (key1391, 1), (key1546, 1), (key1790, -1), (key1817, -1), (key1788, 1), (key1813, 1), (key1457, 1), (key1659, 1), (key1455, -1), (key1655, -1), (key1790, -1), (key1817, -1), (key1457, 1), (key1659, 1), (key1788, 1), (key1813, 1), (key1455, -1), (key1655, -1)]

def rawRow6609 : Integer.Sparse Key := [(key1345, -1), (key1339, -1), (key1337, 2), (key1345, -1), (key1339, -1), (key1329, 2), (key1302, 2), (key1316, -1), (key1296, -1), (key1337, 2), (key1316, -1), (key1296, -1), (key1780, 1), (key1774, 1), (key1772, -2), (key1780, 1), (key1774, 1), (key1559, -2), (key1397, -2), (key1546, 1), (key1391, 1), (key1772, -2), (key1546, 1), (key1391, 1), (key1817, -1), (key1790, -1), (key1813, 1), (key1788, 1), (key1659, 1), (key1457, 1), (key1655, -1), (key1455, -1), (key1817, -1), (key1790, -1), (key1659, 1), (key1457, 1), (key1813, 1), (key1788, 1), (key1655, -1), (key1455, -1)]

def rawRow6610 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1559, 2), (key1573, -1), (key1573, -1), (key1655, 2), (key1655, 2), (key1659, -1), (key1659, -1), (key1596, 2), (key1667, -1), (key1667, -1), (key1316, 1), (key1316, 1), (key1329, -2), (key1424, 1), (key1424, 1), (key1813, -2), (key1813, -2), (key1817, 1), (key1817, 1), (key1447, -2), (key1825, 1), (key1825, 1), (key1337, -1), (key1337, -1), (key1345, 1), (key1345, 1), (key1772, 1), (key1772, 1), (key1780, -1), (key1780, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1466, 1), (key1466, 1), (key1798, -1), (key1798, -1)]

def rawRow6611 : Integer.Sparse Key := [(key1546, -1), (key1559, -1), (key1546, 2), (key1655, -1), (key1659, -1), (key1573, 2), (key1659, 2), (key1573, -1), (key1655, -1), (key1667, 2), (key1596, -1), (key1667, -1), (key1316, 1), (key1329, 1), (key1316, -2), (key1813, 1), (key1817, 1), (key1424, -2), (key1817, -2), (key1424, 1), (key1813, 1), (key1825, -2), (key1447, 1), (key1825, 1), (key1296, -1), (key1345, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1780, 1), (key1391, -1), (key1772, -1), (key1788, -1), (key1841, -1), (key1455, 1), (key1841, 1), (key1798, 1), (key1844, 1), (key1466, -1), (key1844, -1)]

def rawRow6612 : Integer.Sparse Key := [(key1559, -1), (key1546, -1), (key1546, 2), (key1659, -1), (key1655, -1), (key1659, 2), (key1573, 2), (key1655, -1), (key1573, -1), (key1667, 2), (key1667, -1), (key1596, -1), (key1329, 1), (key1316, 1), (key1316, -2), (key1817, 1), (key1813, 1), (key1817, -2), (key1424, -2), (key1813, 1), (key1424, 1), (key1825, -2), (key1825, 1), (key1447, 1), (key1345, -1), (key1296, -1), (key1337, 1), (key1296, 1), (key1780, 1), (key1391, 1), (key1772, -1), (key1391, -1), (key1841, -1), (key1788, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1798, 1), (key1844, -1), (key1466, -1)]

def rawRow6613 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1596, 2), (key1546, -1), (key1546, -1), (key1655, 2), (key1655, 2), (key1667, -1), (key1667, -1), (key1559, 2), (key1659, -1), (key1659, -1), (key1424, 1), (key1424, 1), (key1447, -2), (key1316, 1), (key1316, 1), (key1813, -2), (key1813, -2), (key1825, 1), (key1825, 1), (key1329, -2), (key1817, 1), (key1817, 1), (key1455, -1), (key1455, -1), (key1466, 1), (key1466, 1), (key1788, 1), (key1788, 1), (key1798, -1), (key1798, -1), (key1337, -1), (key1337, -1), (key1772, 1), (key1772, 1), (key1345, 1), (key1345, 1), (key1780, -1), (key1780, -1)]

def rawRow6614 : Integer.Sparse Key := [(key1573, -1), (key1596, -1), (key1573, 2), (key1655, -1), (key1667, -1), (key1546, 2), (key1667, 2), (key1546, -1), (key1655, -1), (key1659, 2), (key1559, -1), (key1659, -1), (key1424, 1), (key1447, 1), (key1424, -2), (key1813, 1), (key1825, 1), (key1316, -2), (key1825, -2), (key1316, 1), (key1813, 1), (key1817, -2), (key1329, 1), (key1817, 1), (key1391, -1), (key1466, -1), (key1391, 1), (key1455, 1), (key1296, 1), (key1798, 1), (key1296, -1), (key1788, -1), (key1772, -1), (key1844, -1), (key1337, 1), (key1844, 1), (key1780, 1), (key1841, 1), (key1345, -1), (key1841, -1)]

def rawRow6615 : Integer.Sparse Key := [(key1596, -1), (key1573, -1), (key1573, 2), (key1667, -1), (key1655, -1), (key1667, 2), (key1546, 2), (key1655, -1), (key1546, -1), (key1659, 2), (key1659, -1), (key1559, -1), (key1447, 1), (key1424, 1), (key1424, -2), (key1825, 1), (key1813, 1), (key1825, -2), (key1316, -2), (key1813, 1), (key1316, 1), (key1817, -2), (key1817, 1), (key1329, 1), (key1466, -1), (key1391, -1), (key1455, 1), (key1391, 1), (key1798, 1), (key1296, 1), (key1788, -1), (key1296, -1), (key1844, -1), (key1772, -1), (key1844, 1), (key1337, 1), (key1841, 1), (key1780, 1), (key1841, -1), (key1345, -1)]

def rawRow6616 : Integer.Sparse Key := [(key1655, -1), (key1659, -1), (key1667, 2), (key1546, -1), (key1559, -1), (key1573, 2), (key1659, 2), (key1596, -1), (key1667, -1), (key1546, 2), (key1573, -1), (key1655, -1), (key1813, 1), (key1817, 1), (key1825, -2), (key1316, 1), (key1329, 1), (key1424, -2), (key1817, -2), (key1447, 1), (key1825, 1), (key1316, -2), (key1424, 1), (key1813, 1), (key1788, -1), (key1841, -1), (key1798, 1), (key1844, 1), (key1455, 1), (key1841, 1), (key1466, -1), (key1844, -1), (key1296, -1), (key1345, -1), (key1391, 1), (key1780, 1), (key1296, 1), (key1337, 1), (key1391, -1), (key1772, -1)]

def rawRow6617 : Integer.Sparse Key := [(key1659, -1), (key1655, -1), (key1667, 2), (key1559, -1), (key1546, -1), (key1659, 2), (key1573, 2), (key1667, -1), (key1596, -1), (key1546, 2), (key1655, -1), (key1573, -1), (key1817, 1), (key1813, 1), (key1825, -2), (key1329, 1), (key1316, 1), (key1817, -2), (key1424, -2), (key1825, 1), (key1447, 1), (key1316, -2), (key1813, 1), (key1424, 1), (key1841, -1), (key1788, -1), (key1844, 1), (key1798, 1), (key1841, 1), (key1455, 1), (key1844, -1), (key1466, -1), (key1345, -1), (key1296, -1), (key1780, 1), (key1391, 1), (key1337, 1), (key1296, 1), (key1772, -1), (key1391, -1)]

def rawRow6618 : Integer.Sparse Key := [(key1655, -1), (key1667, -1), (key1659, 2), (key1573, -1), (key1596, -1), (key1546, 2), (key1667, 2), (key1559, -1), (key1659, -1), (key1573, 2), (key1546, -1), (key1655, -1), (key1813, 1), (key1825, 1), (key1817, -2), (key1424, 1), (key1447, 1), (key1316, -2), (key1825, -2), (key1329, 1), (key1817, 1), (key1424, -2), (key1316, 1), (key1813, 1), (key1772, -1), (key1844, -1), (key1780, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, -1), (key1841, -1), (key1391, -1), (key1466, -1), (key1296, 1), (key1798, 1), (key1391, 1), (key1455, 1), (key1296, -1), (key1788, -1)]

def rawRow6619 : Integer.Sparse Key := [(key1667, -1), (key1655, -1), (key1659, 2), (key1596, -1), (key1573, -1), (key1667, 2), (key1546, 2), (key1659, -1), (key1559, -1), (key1573, 2), (key1655, -1), (key1546, -1), (key1825, 1), (key1813, 1), (key1817, -2), (key1447, 1), (key1424, 1), (key1825, -2), (key1316, -2), (key1817, 1), (key1329, 1), (key1424, -2), (key1813, 1), (key1316, 1), (key1844, -1), (key1772, -1), (key1841, 1), (key1780, 1), (key1844, 1), (key1337, 1), (key1841, -1), (key1345, -1), (key1466, -1), (key1391, -1), (key1798, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, -1), (key1296, -1)]

def rawRow6620 : Integer.Sparse Key := [(key1659, -1), (key1667, -1), (key1655, 2), (key1659, -1), (key1667, -1), (key1559, 2), (key1596, 2), (key1546, -1), (key1573, -1), (key1655, 2), (key1546, -1), (key1573, -1), (key1817, 1), (key1825, 1), (key1813, -2), (key1817, 1), (key1825, 1), (key1329, -2), (key1447, -2), (key1316, 1), (key1424, 1), (key1813, -2), (key1316, 1), (key1424, 1), (key1780, -1), (key1798, -1), (key1772, 1), (key1788, 1), (key1345, 1), (key1466, 1), (key1337, -1), (key1455, -1), (key1780, -1), (key1798, -1), (key1345, 1), (key1466, 1), (key1772, 1), (key1788, 1), (key1337, -1), (key1455, -1)]

def rawRow6621 : Integer.Sparse Key := [(key1667, -1), (key1659, -1), (key1655, 2), (key1667, -1), (key1659, -1), (key1596, 2), (key1559, 2), (key1573, -1), (key1546, -1), (key1655, 2), (key1573, -1), (key1546, -1), (key1825, 1), (key1817, 1), (key1813, -2), (key1825, 1), (key1817, 1), (key1447, -2), (key1329, -2), (key1424, 1), (key1316, 1), (key1813, -2), (key1424, 1), (key1316, 1), (key1798, -1), (key1780, -1), (key1788, 1), (key1772, 1), (key1466, 1), (key1345, 1), (key1455, -1), (key1337, -1), (key1798, -1), (key1780, -1), (key1466, 1), (key1345, 1), (key1788, 1), (key1772, 1), (key1455, -1), (key1337, -1)]

def rawRow6622 : Integer.Sparse Key := [(key1772, -1), (key1774, -1), (key1780, 2), (key1788, -1), (key1790, -1), (key1813, 2), (key1839, 2), (key1817, -1), (key1841, -1), (key1798, 2), (key1825, -1), (key1844, -1), (key1337, 1), (key1339, 1), (key1345, -2), (key1455, 1), (key1457, 1), (key1655, -2), (key1839, -2), (key1659, 1), (key1841, 1), (key1466, -2), (key1667, 1), (key1844, 1), (key1316, -1), (key1339, -1), (key1329, 1), (key1345, 1), (key1546, 1), (key1774, 1), (key1559, -1), (key1780, -1), (key1424, -1), (key1457, -1), (key1573, 1), (key1790, 1), (key1447, 1), (key1466, 1), (key1596, -1), (key1798, -1)]

def rawRow6623 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1780, 2), (key1790, -1), (key1788, -1), (key1839, 2), (key1813, 2), (key1841, -1), (key1817, -1), (key1798, 2), (key1844, -1), (key1825, -1), (key1339, 1), (key1337, 1), (key1345, -2), (key1457, 1), (key1455, 1), (key1839, -2), (key1655, -2), (key1841, 1), (key1659, 1), (key1466, -2), (key1844, 1), (key1667, 1), (key1339, -1), (key1316, -1), (key1345, 1), (key1329, 1), (key1774, 1), (key1546, 1), (key1780, -1), (key1559, -1), (key1457, -1), (key1424, -1), (key1790, 1), (key1573, 1), (key1466, 1), (key1447, 1), (key1798, -1), (key1596, -1)]

def rawRow6624 : Integer.Sparse Key := [(key1774, -1), (key1780, -1), (key1772, 2), (key1839, -1), (key1841, -1), (key1790, 2), (key1817, 2), (key1788, -1), (key1813, -1), (key1844, 2), (key1798, -1), (key1825, -1), (key1339, 1), (key1345, 1), (key1337, -2), (key1839, 1), (key1841, 1), (key1457, -2), (key1659, -2), (key1455, 1), (key1655, 1), (key1844, -2), (key1466, 1), (key1667, 1), (key1302, -1), (key1329, -1), (key1296, 1), (key1316, 1), (key1397, 1), (key1559, 1), (key1391, -1), (key1546, -1), (key1790, -1), (key1817, -1), (key1457, 1), (key1659, 1), (key1798, 1), (key1825, 1), (key1466, -1), (key1667, -1)]

def rawRow6625 : Integer.Sparse Key := [(key1780, -1), (key1774, -1), (key1772, 2), (key1841, -1), (key1839, -1), (key1817, 2), (key1790, 2), (key1813, -1), (key1788, -1), (key1844, 2), (key1825, -1), (key1798, -1), (key1345, 1), (key1339, 1), (key1337, -2), (key1841, 1), (key1839, 1), (key1659, -2), (key1457, -2), (key1655, 1), (key1455, 1), (key1844, -2), (key1667, 1), (key1466, 1), (key1329, -1), (key1302, -1), (key1316, 1), (key1296, 1), (key1559, 1), (key1397, 1), (key1546, -1), (key1391, -1), (key1817, -1), (key1790, -1), (key1659, 1), (key1457, 1), (key1825, 1), (key1798, 1), (key1667, -1), (key1466, -1)]

def rawRow6626 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1798, 2), (key1772, -1), (key1774, -1), (key1813, 2), (key1839, 2), (key1825, -1), (key1844, -1), (key1780, 2), (key1817, -1), (key1841, -1), (key1455, 1), (key1457, 1), (key1466, -2), (key1337, 1), (key1339, 1), (key1655, -2), (key1839, -2), (key1667, 1), (key1844, 1), (key1345, -2), (key1659, 1), (key1841, 1), (key1424, -1), (key1457, -1), (key1447, 1), (key1466, 1), (key1573, 1), (key1790, 1), (key1596, -1), (key1798, -1), (key1316, -1), (key1339, -1), (key1546, 1), (key1774, 1), (key1329, 1), (key1345, 1), (key1559, -1), (key1780, -1)]

def rawRow6627 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1798, 2), (key1774, -1), (key1772, -1), (key1839, 2), (key1813, 2), (key1844, -1), (key1825, -1), (key1780, 2), (key1841, -1), (key1817, -1), (key1457, 1), (key1455, 1), (key1466, -2), (key1339, 1), (key1337, 1), (key1839, -2), (key1655, -2), (key1844, 1), (key1667, 1), (key1345, -2), (key1841, 1), (key1659, 1), (key1457, -1), (key1424, -1), (key1466, 1), (key1447, 1), (key1790, 1), (key1573, 1), (key1798, -1), (key1596, -1), (key1339, -1), (key1316, -1), (key1774, 1), (key1546, 1), (key1345, 1), (key1329, 1), (key1780, -1), (key1559, -1)]

def rawRow6628 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1790, 2), (key1813, -1), (key1825, -1), (key1772, 2), (key1844, 2), (key1774, -1), (key1839, -1), (key1817, 2), (key1780, -1), (key1841, -1), (key1455, 1), (key1466, 1), (key1457, -2), (key1655, 1), (key1667, 1), (key1337, -2), (key1844, -2), (key1339, 1), (key1839, 1), (key1659, -2), (key1345, 1), (key1841, 1), (key1391, -1), (key1466, -1), (key1397, 1), (key1457, 1), (key1296, 1), (key1798, 1), (key1302, -1), (key1790, -1), (key1546, -1), (key1667, -1), (key1316, 1), (key1825, 1), (key1559, 1), (key1659, 1), (key1329, -1), (key1817, -1)]

def rawRow6629 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1790, 2), (key1825, -1), (key1813, -1), (key1844, 2), (key1772, 2), (key1839, -1), (key1774, -1), (key1817, 2), (key1841, -1), (key1780, -1), (key1466, 1), (key1455, 1), (key1457, -2), (key1667, 1), (key1655, 1), (key1844, -2), (key1337, -2), (key1839, 1), (key1339, 1), (key1659, -2), (key1841, 1), (key1345, 1), (key1466, -1), (key1391, -1), (key1457, 1), (key1397, 1), (key1798, 1), (key1296, 1), (key1790, -1), (key1302, -1), (key1667, -1), (key1546, -1), (key1825, 1), (key1316, 1), (key1659, 1), (key1559, 1), (key1817, -1), (key1329, -1)]

def rawRow6630 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1817, 2), (key1788, -1), (key1798, -1), (key1772, 2), (key1844, 2), (key1780, -1), (key1841, -1), (key1790, 2), (key1774, -1), (key1839, -1), (key1655, 1), (key1667, 1), (key1659, -2), (key1455, 1), (key1466, 1), (key1337, -2), (key1844, -2), (key1345, 1), (key1841, 1), (key1457, -2), (key1339, 1), (key1839, 1), (key1546, -1), (key1667, -1), (key1559, 1), (key1659, 1), (key1316, 1), (key1825, 1), (key1329, -1), (key1817, -1), (key1391, -1), (key1466, -1), (key1296, 1), (key1798, 1), (key1397, 1), (key1457, 1), (key1302, -1), (key1790, -1)]

def rawRow6631 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1817, 2), (key1798, -1), (key1788, -1), (key1844, 2), (key1772, 2), (key1841, -1), (key1780, -1), (key1790, 2), (key1839, -1), (key1774, -1), (key1667, 1), (key1655, 1), (key1659, -2), (key1466, 1), (key1455, 1), (key1844, -2), (key1337, -2), (key1841, 1), (key1345, 1), (key1457, -2), (key1839, 1), (key1339, 1), (key1667, -1), (key1546, -1), (key1659, 1), (key1559, 1), (key1825, 1), (key1316, 1), (key1817, -1), (key1329, -1), (key1466, -1), (key1391, -1), (key1798, 1), (key1296, 1), (key1457, 1), (key1397, 1), (key1790, -1), (key1302, -1)]

def rawRow6632 : Integer.Sparse Key := [(key1817, -1), (key1825, -1), (key1813, 2), (key1841, -1), (key1844, -1), (key1780, 2), (key1798, 2), (key1772, -1), (key1788, -1), (key1839, 2), (key1774, -1), (key1790, -1), (key1659, 1), (key1667, 1), (key1655, -2), (key1841, 1), (key1844, 1), (key1345, -2), (key1466, -2), (key1337, 1), (key1455, 1), (key1839, -2), (key1339, 1), (key1457, 1), (key1559, -1), (key1596, -1), (key1546, 1), (key1573, 1), (key1329, 1), (key1447, 1), (key1316, -1), (key1424, -1), (key1780, -1), (key1798, -1), (key1345, 1), (key1466, 1), (key1774, 1), (key1790, 1), (key1339, -1), (key1457, -1)]

def rawRow6633 : Integer.Sparse Key := [(key1825, -1), (key1817, -1), (key1813, 2), (key1844, -1), (key1841, -1), (key1798, 2), (key1780, 2), (key1788, -1), (key1772, -1), (key1839, 2), (key1790, -1), (key1774, -1), (key1667, 1), (key1659, 1), (key1655, -2), (key1844, 1), (key1841, 1), (key1466, -2), (key1345, -2), (key1455, 1), (key1337, 1), (key1839, -2), (key1457, 1), (key1339, 1), (key1596, -1), (key1559, -1), (key1573, 1), (key1546, 1), (key1447, 1), (key1329, 1), (key1424, -1), (key1316, -1), (key1798, -1), (key1780, -1), (key1466, 1), (key1345, 1), (key1790, 1), (key1774, 1), (key1457, -1), (key1339, -1)]

def rawRow6634 : Integer.Sparse Key := [(key1839, -1), (key1841, -1), (key1844, 2), (key1774, -1), (key1780, -1), (key1790, 2), (key1817, 2), (key1798, -1), (key1825, -1), (key1772, 2), (key1788, -1), (key1813, -1), (key1839, 1), (key1841, 1), (key1844, -2), (key1339, 1), (key1345, 1), (key1457, -2), (key1659, -2), (key1466, 1), (key1667, 1), (key1337, -2), (key1455, 1), (key1655, 1), (key1790, -1), (key1817, -1), (key1798, 1), (key1825, 1), (key1457, 1), (key1659, 1), (key1466, -1), (key1667, -1), (key1302, -1), (key1329, -1), (key1397, 1), (key1559, 1), (key1296, 1), (key1316, 1), (key1391, -1), (key1546, -1)]

def rawRow6635 : Integer.Sparse Key := [(key1841, -1), (key1839, -1), (key1844, 2), (key1780, -1), (key1774, -1), (key1817, 2), (key1790, 2), (key1825, -1), (key1798, -1), (key1772, 2), (key1813, -1), (key1788, -1), (key1841, 1), (key1839, 1), (key1844, -2), (key1345, 1), (key1339, 1), (key1659, -2), (key1457, -2), (key1667, 1), (key1466, 1), (key1337, -2), (key1655, 1), (key1455, 1), (key1817, -1), (key1790, -1), (key1825, 1), (key1798, 1), (key1659, 1), (key1457, 1), (key1667, -1), (key1466, -1), (key1329, -1), (key1302, -1), (key1559, 1), (key1397, 1), (key1316, 1), (key1296, 1), (key1546, -1), (key1391, -1)]

def rawRow6636 : Integer.Sparse Key := [(key1841, -1), (key1844, -1), (key1839, 2), (key1817, -1), (key1825, -1), (key1780, 2), (key1798, 2), (key1774, -1), (key1790, -1), (key1813, 2), (key1772, -1), (key1788, -1), (key1841, 1), (key1844, 1), (key1839, -2), (key1659, 1), (key1667, 1), (key1345, -2), (key1466, -2), (key1339, 1), (key1457, 1), (key1655, -2), (key1337, 1), (key1455, 1), (key1780, -1), (key1798, -1), (key1774, 1), (key1790, 1), (key1345, 1), (key1466, 1), (key1339, -1), (key1457, -1), (key1559, -1), (key1596, -1), (key1329, 1), (key1447, 1), (key1546, 1), (key1573, 1), (key1316, -1), (key1424, -1)]

def rawRow6637 : Integer.Sparse Key := [(key1844, -1), (key1841, -1), (key1839, 2), (key1825, -1), (key1817, -1), (key1798, 2), (key1780, 2), (key1790, -1), (key1774, -1), (key1813, 2), (key1788, -1), (key1772, -1), (key1844, 1), (key1841, 1), (key1839, -2), (key1667, 1), (key1659, 1), (key1466, -2), (key1345, -2), (key1457, 1), (key1339, 1), (key1655, -2), (key1455, 1), (key1337, 1), (key1798, -1), (key1780, -1), (key1790, 1), (key1774, 1), (key1466, 1), (key1345, 1), (key1457, -1), (key1339, -1), (key1596, -1), (key1559, -1), (key1447, 1), (key1329, 1), (key1573, 1), (key1546, 1), (key1424, -1), (key1316, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6678 : Integer.Sparse Key := [(key2617, -2), (key2620, 1), (key2620, 1), (key2633, -2), (key2643, 1), (key2643, 1), (key2650, 1), (key2650, 1), (key2655, 1), (key2655, 1), (key2656, -2), (key2656, -2), (key2787, 2), (key2797, -1), (key2797, -1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, 2), (key2915, 2), (key2940, -1), (key2940, -1), (key2946, 1), (key2946, 1), (key2952, -1), (key2952, -1), (key2962, 1), (key2962, 1), (key2985, 1), (key2985, 1), (key2994, -1), (key2994, -1), (key2999, 1), (key2999, 1), (key3004, -1), (key3004, -1)]

def rawRow6679 : Integer.Sparse Key := [(key2620, -2), (key2617, 1), (key2620, 1), (key2643, -2), (key2633, 1), (key2643, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2656, 1), (key2650, -2), (key2655, -2), (key2797, 2), (key2787, -1), (key2797, -1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, 2), (key2906, 2), (key2945, -1), (key2946, -1), (key2940, 1), (key2945, 1), (key2962, -1), (key2964, -1), (key2952, 1), (key2964, 1), (key2978, 1), (key2994, 1), (key2978, -1), (key2985, -1), (key3001, 1), (key3004, 1), (key2999, -1), (key3001, -1)]

def rawRow6680 : Integer.Sparse Key := [(key2620, -2), (key2620, 1), (key2617, 1), (key2643, -2), (key2643, 1), (key2633, 1), (key2656, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2655, -2), (key2650, -2), (key2797, 2), (key2797, -1), (key2787, -1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, 2), (key2899, 2), (key2946, -1), (key2945, -1), (key2945, 1), (key2940, 1), (key2964, -1), (key2962, -1), (key2964, 1), (key2952, 1), (key2994, 1), (key2978, 1), (key2985, -1), (key2978, -1), (key3004, 1), (key3001, 1), (key3001, -1), (key2999, -1)]

def rawRow6681 : Integer.Sparse Key := [(key2633, -2), (key2643, 1), (key2643, 1), (key2617, -2), (key2655, 1), (key2655, 1), (key2620, 1), (key2620, 1), (key2643, 1), (key2643, 1), (key2656, -2), (key2656, -2), (key2810, 2), (key2899, -1), (key2899, -1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, 2), (key2915, 2), (key2952, -1), (key2952, -1), (key2999, 1), (key2999, 1), (key2940, -1), (key2940, -1), (key2985, 1), (key2985, 1), (key2962, 1), (key2962, 1), (key3004, -1), (key3004, -1), (key2946, 1), (key2946, 1), (key2994, -1), (key2994, -1)]

def rawRow6682 : Integer.Sparse Key := [(key2643, -2), (key2633, 1), (key2643, 1), (key2655, -2), (key2617, 1), (key2655, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2656, 1), (key2620, -2), (key2643, -2), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, 2), (key2833, 2), (key2978, -1), (key2999, -1), (key2952, 1), (key2978, 1), (key2985, -1), (key3001, -1), (key2940, 1), (key3001, 1), (key2945, 1), (key3004, 1), (key2945, -1), (key2962, -1), (key2964, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

def rawRow6683 : Integer.Sparse Key := [(key2643, -2), (key2643, 1), (key2633, 1), (key2655, -2), (key2655, 1), (key2617, 1), (key2656, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2643, -2), (key2620, -2), (key2899, 2), (key2899, -1), (key2810, -1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, 2), (key2797, 2), (key2999, -1), (key2978, -1), (key2978, 1), (key2952, 1), (key3001, -1), (key2985, -1), (key3001, 1), (key2940, 1), (key3004, 1), (key2945, 1), (key2962, -1), (key2945, -1), (key2994, 1), (key2964, 1), (key2964, -1), (key2946, -1)]

def rawRow6684 : Integer.Sparse Key := [(key2650, -2), (key2655, 1), (key2656, 1), (key2620, -2), (key2643, 1), (key2656, 1), (key2617, 1), (key2620, 1), (key2633, 1), (key2643, 1), (key2650, -2), (key2655, -2), (key2833, 2), (key2906, -1), (key2915, -1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, 2), (key2906, 2), (key2962, -1), (key2964, -1), (key3001, 1), (key3004, 1), (key2945, -1), (key2946, -1), (key2978, 1), (key2994, 1), (key2952, 1), (key2964, 1), (key2999, -1), (key3001, -1), (key2940, 1), (key2945, 1), (key2978, -1), (key2985, -1)]

def rawRow6685 : Integer.Sparse Key := [(key2650, -2), (key2656, 1), (key2655, 1), (key2620, -2), (key2656, 1), (key2643, 1), (key2620, 1), (key2617, 1), (key2643, 1), (key2633, 1), (key2655, -2), (key2650, -2), (key2833, 2), (key2915, -1), (key2906, -1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, 2), (key2899, 2), (key2964, -1), (key2962, -1), (key3004, 1), (key3001, 1), (key2946, -1), (key2945, -1), (key2994, 1), (key2978, 1), (key2964, 1), (key2952, 1), (key3001, -1), (key2999, -1), (key2945, 1), (key2940, 1), (key2985, -1), (key2978, -1)]

def rawRow6686 : Integer.Sparse Key := [(key2655, -2), (key2650, 1), (key2656, 1), (key2643, -2), (key2620, 1), (key2656, 1), (key2633, 1), (key2643, 1), (key2617, 1), (key2655, 1), (key2620, -2), (key2643, -2), (key2906, 2), (key2833, -1), (key2915, -1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, 2), (key2833, 2), (key2985, -1), (key3001, -1), (key2964, 1), (key2994, 1), (key2978, -1), (key2999, -1), (key2945, 1), (key3004, 1), (key2940, 1), (key3001, 1), (key2946, -1), (key2964, -1), (key2952, 1), (key2978, 1), (key2945, -1), (key2962, -1)]

def rawRow6687 : Integer.Sparse Key := [(key2655, -2), (key2656, 1), (key2650, 1), (key2643, -2), (key2656, 1), (key2620, 1), (key2643, 1), (key2633, 1), (key2655, 1), (key2617, 1), (key2643, -2), (key2620, -2), (key2906, 2), (key2915, -1), (key2833, -1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, 2), (key2797, 2), (key3001, -1), (key2985, -1), (key2994, 1), (key2964, 1), (key2999, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key3001, 1), (key2940, 1), (key2964, -1), (key2946, -1), (key2978, 1), (key2952, 1), (key2962, -1), (key2945, -1)]

def rawRow6688 : Integer.Sparse Key := [(key2656, -2), (key2650, 1), (key2655, 1), (key2656, -2), (key2620, 1), (key2643, 1), (key2650, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2617, -2), (key2633, -2), (key2915, 2), (key2833, -1), (key2906, -1), (key2915, 2), (key2797, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, 2), (key2810, 2), (key2994, -1), (key3004, -1), (key2962, 1), (key2985, 1), (key2994, -1), (key3004, -1), (key2946, 1), (key2999, 1), (key2946, 1), (key2999, 1), (key2940, -1), (key2952, -1), (key2962, 1), (key2985, 1), (key2940, -1), (key2952, -1)]

def rawRow6689 : Integer.Sparse Key := [(key2656, -2), (key2655, 1), (key2650, 1), (key2656, -2), (key2643, 1), (key2620, 1), (key2655, 1), (key2650, 1), (key2643, 1), (key2620, 1), (key2633, -2), (key2617, -2), (key2915, 2), (key2906, -1), (key2833, -1), (key2915, 2), (key2899, -1), (key2797, -1), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, 2), (key2787, 2), (key3004, -1), (key2994, -1), (key2985, 1), (key2962, 1), (key3004, -1), (key2994, -1), (key2999, 1), (key2946, 1), (key2999, 1), (key2946, 1), (key2952, -1), (key2940, -1), (key2985, 1), (key2962, 1), (key2952, -1), (key2940, -1)]

def rawRow6690 : Integer.Sparse Key := [(key2787, -2), (key2797, 1), (key2797, 1), (key2810, -2), (key2899, 1), (key2899, 1), (key2833, 1), (key2833, 1), (key2906, 1), (key2906, 1), (key2915, -2), (key2915, -2), (key2617, 2), (key2655, -1), (key2655, -1), (key2672, 2), (key2749, -1), (key2749, -1), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, 2), (key3004, 2), (key2620, -1), (key2620, -1), (key2656, 1), (key2656, 1), (key2675, -1), (key2675, -1), (key2730, 1), (key2730, 1), (key2833, 1), (key2833, 1), (key2915, -1), (key2915, -1), (key2946, 1), (key2946, 1), (key2994, -1), (key2994, -1)]

def rawRow6691 : Integer.Sparse Key := [(key2797, -2), (key2787, 1), (key2797, 1), (key2899, -2), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2915, 1), (key2833, -2), (key2906, -2), (key2655, 2), (key2617, -1), (key2655, -1), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, 2), (key2962, 2), (key2643, -1), (key2656, -1), (key2620, 1), (key2643, 1), (key2730, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2797, 1), (key2915, 1), (key2797, -1), (key2833, -1), (key2964, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

def rawRow6692 : Integer.Sparse Key := [(key2797, -2), (key2797, 1), (key2787, 1), (key2899, -2), (key2899, 1), (key2810, 1), (key2915, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2906, -2), (key2833, -2), (key2655, 2), (key2655, -1), (key2617, -1), (key2749, 2), (key2749, -1), (key2672, -1), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, 2), (key2945, 2), (key2656, -1), (key2643, -1), (key2643, 1), (key2620, 1), (key2751, -1), (key2730, -1), (key2751, 1), (key2675, 1), (key2915, 1), (key2797, 1), (key2833, -1), (key2797, -1), (key2994, 1), (key2964, 1), (key2964, -1), (key2946, -1)]

def rawRow6693 : Integer.Sparse Key := [(key2810, -2), (key2833, 1), (key2833, 1), (key2787, -2), (key2906, 1), (key2906, 1), (key2797, 1), (key2797, 1), (key2899, 1), (key2899, 1), (key2915, -2), (key2915, -2), (key2672, 2), (key2749, -1), (key2749, -1), (key2617, 2), (key2962, -1), (key2962, -1), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, 2), (key3004, 2), (key2675, -1), (key2675, -1), (key2946, 1), (key2946, 1), (key2620, -1), (key2620, -1), (key2833, 1), (key2833, 1), (key2730, 1), (key2730, 1), (key2994, -1), (key2994, -1), (key2656, 1), (key2656, 1), (key2915, -1), (key2915, -1)]

def rawRow6694 : Integer.Sparse Key := [(key2833, -2), (key2810, 1), (key2833, 1), (key2906, -2), (key2787, 1), (key2906, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, -2), (key2899, -2), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, 2), (key2617, -1), (key2962, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, 2), (key2749, 2), (key2797, -1), (key2946, -1), (key2675, 1), (key2797, 1), (key2833, -1), (key2964, -1), (key2620, 1), (key2964, 1), (key2643, 1), (key2994, 1), (key2643, -1), (key2730, -1), (key2751, 1), (key2915, 1), (key2656, -1), (key2751, -1)]

def rawRow6695 : Integer.Sparse Key := [(key2833, -2), (key2833, 1), (key2810, 1), (key2906, -2), (key2906, 1), (key2787, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2899, -2), (key2797, -2), (key2749, 2), (key2749, -1), (key2672, -1), (key2962, 2), (key2962, -1), (key2617, -1), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, 2), (key2655, 2), (key2946, -1), (key2797, -1), (key2797, 1), (key2675, 1), (key2964, -1), (key2833, -1), (key2964, 1), (key2620, 1), (key2994, 1), (key2643, 1), (key2730, -1), (key2643, -1), (key2915, 1), (key2751, 1), (key2751, -1), (key2656, -1)]

def rawRow6696 : Integer.Sparse Key := [(key2899, -2), (key2906, 1), (key2915, 1), (key2797, -2), (key2833, 1), (key2915, 1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2833, -2), (key2906, -2), (key2945, 2), (key2962, -1), (key3004, -1), (key2655, 2), (key2749, -1), (key3004, -1), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, 2), (key2962, 2), (key2730, -1), (key2751, -1), (key2964, 1), (key2994, 1), (key2643, -1), (key2656, -1), (key2797, 1), (key2915, 1), (key2675, 1), (key2751, 1), (key2946, -1), (key2964, -1), (key2620, 1), (key2643, 1), (key2797, -1), (key2833, -1)]

def rawRow6697 : Integer.Sparse Key := [(key2899, -2), (key2915, 1), (key2906, 1), (key2797, -2), (key2915, 1), (key2833, 1), (key2797, 1), (key2787, 1), (key2899, 1), (key2810, 1), (key2906, -2), (key2833, -2), (key2945, 2), (key3004, -1), (key2962, -1), (key2655, 2), (key3004, -1), (key2749, -1), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, 2), (key2945, 2), (key2751, -1), (key2730, -1), (key2994, 1), (key2964, 1), (key2656, -1), (key2643, -1), (key2915, 1), (key2797, 1), (key2751, 1), (key2675, 1), (key2964, -1), (key2946, -1), (key2643, 1), (key2620, 1), (key2833, -1), (key2797, -1)]

def rawRow6698 : Integer.Sparse Key := [(key2906, -2), (key2899, 1), (key2915, 1), (key2833, -2), (key2797, 1), (key2915, 1), (key2810, 1), (key2833, 1), (key2787, 1), (key2906, 1), (key2797, -2), (key2899, -2), (key2962, 2), (key2945, -1), (key3004, -1), (key2749, 2), (key2655, -1), (key3004, -1), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, 2), (key2749, 2), (key2833, -1), (key2964, -1), (key2751, 1), (key2915, 1), (key2797, -1), (key2946, -1), (key2643, 1), (key2994, 1), (key2620, 1), (key2964, 1), (key2656, -1), (key2751, -1), (key2675, 1), (key2797, 1), (key2643, -1), (key2730, -1)]

def rawRow6699 : Integer.Sparse Key := [(key2906, -2), (key2915, 1), (key2899, 1), (key2833, -2), (key2915, 1), (key2797, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2899, -2), (key2797, -2), (key2962, 2), (key3004, -1), (key2945, -1), (key2749, 2), (key3004, -1), (key2655, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, 2), (key2655, 2), (key2964, -1), (key2833, -1), (key2915, 1), (key2751, 1), (key2946, -1), (key2797, -1), (key2994, 1), (key2643, 1), (key2964, 1), (key2620, 1), (key2751, -1), (key2656, -1), (key2797, 1), (key2675, 1), (key2730, -1), (key2643, -1)]

def rawRow6700 : Integer.Sparse Key := [(key2915, -2), (key2899, 1), (key2906, 1), (key2915, -2), (key2797, 1), (key2833, 1), (key2899, 1), (key2906, 1), (key2797, 1), (key2833, 1), (key2787, -2), (key2810, -2), (key3004, 2), (key2945, -1), (key2962, -1), (key3004, 2), (key2655, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, 2), (key2672, 2), (key2915, -1), (key2994, -1), (key2730, 1), (key2833, 1), (key2915, -1), (key2994, -1), (key2656, 1), (key2946, 1), (key2656, 1), (key2946, 1), (key2620, -1), (key2675, -1), (key2730, 1), (key2833, 1), (key2620, -1), (key2675, -1)]

def rawRow6701 : Integer.Sparse Key := [(key2915, -2), (key2906, 1), (key2899, 1), (key2915, -2), (key2833, 1), (key2797, 1), (key2906, 1), (key2899, 1), (key2833, 1), (key2797, 1), (key2810, -2), (key2787, -2), (key3004, 2), (key2962, -1), (key2945, -1), (key3004, 2), (key2749, -1), (key2655, -1), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, 2), (key2617, 2), (key2994, -1), (key2915, -1), (key2833, 1), (key2730, 1), (key2994, -1), (key2915, -1), (key2946, 1), (key2656, 1), (key2946, 1), (key2656, 1), (key2675, -1), (key2620, -1), (key2833, 1), (key2730, 1), (key2675, -1), (key2620, -1)]

def rawRow6702 : Integer.Sparse Key := [(key2940, -2), (key2945, 1), (key2946, 1), (key2952, -2), (key2978, 1), (key2999, 1), (key2962, 1), (key2964, 1), (key2985, 1), (key3001, 1), (key2994, -2), (key3004, -2), (key2620, 2), (key2643, -1), (key2656, -1), (key2675, 2), (key2797, -1), (key2946, -1), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, 2), (key2994, 2), (key2617, -1), (key2620, -1), (key2650, 1), (key2655, 1), (key2672, -1), (key2675, -1), (key2707, 1), (key2730, 1), (key2810, 1), (key2833, 1), (key2899, -1), (key2906, -1), (key2940, 1), (key2945, 1), (key2978, -1), (key2985, -1)]

def rawRow6703 : Integer.Sparse Key := [(key2940, -2), (key2946, 1), (key2945, 1), (key2952, -2), (key2999, 1), (key2978, 1), (key2964, 1), (key2962, 1), (key3001, 1), (key2985, 1), (key3004, -2), (key2994, -2), (key2620, 2), (key2656, -1), (key2643, -1), (key2675, 2), (key2946, -1), (key2797, -1), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, 2), (key2915, 2), (key2620, -1), (key2617, -1), (key2655, 1), (key2650, 1), (key2675, -1), (key2672, -1), (key2730, 1), (key2707, 1), (key2833, 1), (key2810, 1), (key2906, -1), (key2899, -1), (key2945, 1), (key2940, 1), (key2985, -1), (key2978, -1)]

def rawRow6704 : Integer.Sparse Key := [(key2946, -2), (key2940, 1), (key2945, 1), (key2999, -2), (key2952, 1), (key2978, 1), (key3001, 1), (key3004, 1), (key2964, 1), (key2994, 1), (key2962, -2), (key2985, -2), (key2656, 2), (key2620, -1), (key2643, -1), (key2946, 2), (key2675, -1), (key2797, -1), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, 2), (key2833, 2), (key2650, -1), (key2655, -1), (key2617, 1), (key2633, 1), (key2730, -1), (key2749, -1), (key2675, 1), (key2739, 1), (key2797, 1), (key2899, 1), (key2787, -1), (key2810, -1), (key2962, 1), (key2985, 1), (key2940, -1), (key2952, -1)]

def rawRow6705 : Integer.Sparse Key := [(key2946, -2), (key2945, 1), (key2940, 1), (key2999, -2), (key2978, 1), (key2952, 1), (key3004, 1), (key3001, 1), (key2994, 1), (key2964, 1), (key2985, -2), (key2962, -2), (key2656, 2), (key2643, -1), (key2620, -1), (key2946, 2), (key2797, -1), (key2675, -1), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, 2), (key2730, 2), (key2655, -1), (key2650, -1), (key2633, 1), (key2617, 1), (key2749, -1), (key2730, -1), (key2739, 1), (key2675, 1), (key2899, 1), (key2797, 1), (key2810, -1), (key2787, -1), (key2985, 1), (key2962, 1), (key2952, -1), (key2940, -1)]

def rawRow6706 : Integer.Sparse Key := [(key2952, -2), (key2962, 1), (key2964, 1), (key2940, -2), (key2985, 1), (key3001, 1), (key2945, 1), (key2946, 1), (key2978, 1), (key2999, 1), (key2994, -2), (key3004, -2), (key2675, 2), (key2730, -1), (key2751, -1), (key2620, 2), (key2833, -1), (key2964, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, 2), (key2994, 2), (key2672, -1), (key2675, -1), (key2730, 1), (key2749, 1), (key2617, -1), (key2620, -1), (key2810, 1), (key2833, 1), (key2707, 1), (key2730, 1), (key2978, -1), (key2985, -1), (key2650, 1), (key2655, 1), (key2899, -1), (key2906, -1)]

def rawRow6707 : Integer.Sparse Key := [(key2952, -2), (key2964, 1), (key2962, 1), (key2940, -2), (key3001, 1), (key2985, 1), (key2946, 1), (key2945, 1), (key2999, 1), (key2978, 1), (key3004, -2), (key2994, -2), (key2675, 2), (key2751, -1), (key2730, -1), (key2620, 2), (key2964, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, 2), (key2915, 2), (key2675, -1), (key2672, -1), (key2749, 1), (key2730, 1), (key2620, -1), (key2617, -1), (key2833, 1), (key2810, 1), (key2730, 1), (key2707, 1), (key2985, -1), (key2978, -1), (key2655, 1), (key2650, 1), (key2906, -1), (key2899, -1)]

def rawRow6708 : Integer.Sparse Key := [(key2962, -2), (key2952, 1), (key2964, 1), (key2985, -2), (key2940, 1), (key3001, 1), (key2978, 1), (key2994, 1), (key2945, 1), (key3004, 1), (key2946, -2), (key2999, -2), (key2730, 2), (key2675, -1), (key2751, -1), (key2833, 2), (key2620, -1), (key2964, -1), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, 2), (key2946, 2), (key2707, -1), (key2730, -1), (key2675, 1), (key2739, 1), (key2810, -1), (key2833, -1), (key2617, 1), (key2962, 1), (key2633, 1), (key2985, 1), (key2643, -1), (key2730, -1), (key2739, 1), (key2899, 1), (key2655, -1), (key2749, -1)]

def rawRow6709 : Integer.Sparse Key := [(key2962, -2), (key2964, 1), (key2952, 1), (key2985, -2), (key3001, 1), (key2940, 1), (key2994, 1), (key2978, 1), (key3004, 1), (key2945, 1), (key2999, -2), (key2946, -2), (key2730, 2), (key2751, -1), (key2675, -1), (key2833, 2), (key2964, -1), (key2620, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, 2), (key2656, 2), (key2730, -1), (key2707, -1), (key2739, 1), (key2675, 1), (key2833, -1), (key2810, -1), (key2962, 1), (key2617, 1), (key2985, 1), (key2633, 1), (key2730, -1), (key2643, -1), (key2899, 1), (key2739, 1), (key2749, -1), (key2655, -1)]

def rawRow6710 : Integer.Sparse Key := [(key2985, -2), (key2978, 1), (key2994, 1), (key2962, -2), (key2945, 1), (key3004, 1), (key2952, 1), (key2964, 1), (key2940, 1), (key3001, 1), (key2946, -2), (key2999, -2), (key2833, 2), (key2797, -1), (key2915, -1), (key2730, 2), (key2643, -1), (key2994, -1), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, 2), (key2946, 2), (key2810, -1), (key2833, -1), (key2797, 1), (key2899, 1), (key2707, -1), (key2730, -1), (key2633, 1), (key2985, 1), (key2617, 1), (key2962, 1), (key2655, -1), (key2749, -1), (key2675, 1), (key2797, 1), (key2643, -1), (key2730, -1)]

def rawRow6711 : Integer.Sparse Key := [(key2985, -2), (key2994, 1), (key2978, 1), (key2962, -2), (key3004, 1), (key2945, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2999, -2), (key2946, -2), (key2833, 2), (key2915, -1), (key2797, -1), (key2730, 2), (key2994, -1), (key2643, -1), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, 2), (key2656, 2), (key2833, -1), (key2810, -1), (key2899, 1), (key2797, 1), (key2730, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key2962, 1), (key2617, 1), (key2749, -1), (key2655, -1), (key2797, 1), (key2675, 1), (key2730, -1), (key2643, -1)]

def rawRow6712 : Integer.Sparse Key := [(key2994, -2), (key2978, 1), (key2985, 1), (key3004, -2), (key2945, 1), (key2962, 1), (key2999, 1), (key3001, 1), (key2946, 1), (key2964, 1), (key2940, -2), (key2952, -2), (key2915, 2), (key2797, -1), (key2833, -1), (key2994, 2), (key2643, -1), (key2730, -1), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, 2), (key2675, 2), (key2899, -1), (key2906, -1), (key2787, 1), (key2810, 1), (key2978, -1), (key2985, -1), (key2643, 1), (key2730, 1), (key2655, 1), (key2749, 1), (key2617, -1), (key2672, -1), (key2730, 1), (key2833, 1), (key2620, -1), (key2675, -1)]

def rawRow6713 : Integer.Sparse Key := [(key2994, -2), (key2985, 1), (key2978, 1), (key3004, -2), (key2962, 1), (key2945, 1), (key3001, 1), (key2999, 1), (key2964, 1), (key2946, 1), (key2952, -2), (key2940, -2), (key2915, 2), (key2833, -1), (key2797, -1), (key2994, 2), (key2730, -1), (key2643, -1), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, 2), (key2620, 2), (key2906, -1), (key2899, -1), (key2810, 1), (key2787, 1), (key2985, -1), (key2978, -1), (key2730, 1), (key2643, 1), (key2749, 1), (key2655, 1), (key2672, -1), (key2617, -1), (key2833, 1), (key2730, 1), (key2675, -1), (key2620, -1)]

def rawRow6714 : Integer.Sparse Key := [(key2999, -2), (key3001, 1), (key3004, 1), (key2946, -2), (key2964, 1), (key2994, 1), (key2940, 1), (key2945, 1), (key2952, 1), (key2978, 1), (key2962, -2), (key2985, -2), (key2946, 2), (key2964, -1), (key2994, -1), (key2656, 2), (key2751, -1), (key2915, -1), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, 2), (key2833, 2), (key2940, -1), (key2945, -1), (key2962, 1), (key2985, 1), (key2650, -1), (key2655, -1), (key2739, 1), (key2899, 1), (key2675, 1), (key2797, 1), (key2730, -1), (key2833, -1), (key2617, 1), (key2633, 1), (key2787, -1), (key2810, -1)]

def rawRow6715 : Integer.Sparse Key := [(key2999, -2), (key3004, 1), (key3001, 1), (key2946, -2), (key2994, 1), (key2964, 1), (key2945, 1), (key2940, 1), (key2978, 1), (key2952, 1), (key2985, -2), (key2962, -2), (key2946, 2), (key2994, -1), (key2964, -1), (key2656, 2), (key2915, -1), (key2751, -1), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, 2), (key2730, 2), (key2945, -1), (key2940, -1), (key2985, 1), (key2962, 1), (key2655, -1), (key2650, -1), (key2899, 1), (key2739, 1), (key2797, 1), (key2675, 1), (key2833, -1), (key2730, -1), (key2633, 1), (key2617, 1), (key2810, -1), (key2787, -1)]

def rawRow6716 : Integer.Sparse Key := [(key3004, -2), (key2999, 1), (key3001, 1), (key2994, -2), (key2946, 1), (key2964, 1), (key2978, 1), (key2985, 1), (key2945, 1), (key2962, 1), (key2940, -2), (key2952, -2), (key2994, 2), (key2946, -1), (key2964, -1), (key2915, 2), (key2656, -1), (key2751, -1), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, 2), (key2675, 2), (key2978, -1), (key2985, -1), (key2940, 1), (key2952, 1), (key2899, -1), (key2906, -1), (key2655, 1), (key2749, 1), (key2643, 1), (key2730, 1), (key2620, -1), (key2675, -1), (key2787, 1), (key2810, 1), (key2617, -1), (key2672, -1)]

def rawRow6717 : Integer.Sparse Key := [(key3004, -2), (key3001, 1), (key2999, 1), (key2994, -2), (key2964, 1), (key2946, 1), (key2985, 1), (key2978, 1), (key2962, 1), (key2945, 1), (key2952, -2), (key2940, -2), (key2994, 2), (key2964, -1), (key2946, -1), (key2915, 2), (key2751, -1), (key2656, -1), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, 2), (key2620, 2), (key2985, -1), (key2978, -1), (key2952, 1), (key2940, 1), (key2906, -1), (key2899, -1), (key2749, 1), (key2655, 1), (key2730, 1), (key2643, 1), (key2675, -1), (key2620, -1), (key2810, 1), (key2787, 1), (key2672, -1), (key2617, -1)]

def rawRow6718 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2036, 2), (key2061, -1), (key2066, -1), (key2061, 2), (key2071, 2), (key2066, -1), (key2071, -1), (key2093, 2), (key2093, -1), (key2096, -1), (key2031, 1), (key2036, 1), (key2036, -2), (key2150, 1), (key2155, 1), (key2150, -2), (key2168, -2), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, 1), (key2201, 1), (key2061, -1), (key2071, -1), (key2066, 1), (key2071, 1), (key2150, 1), (key2168, 1), (key2155, -1), (key2168, -1), (key2243, -1), (key2248, -1), (key2243, 1), (key2255, 1), (key2304, 1), (key2306, 1), (key2304, -1), (key2311, -1)]

def rawRow6719 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2036, 2), (key2066, -1), (key2061, -1), (key2071, 2), (key2061, 2), (key2071, -1), (key2066, -1), (key2093, 2), (key2096, -1), (key2093, -1), (key2036, 1), (key2031, 1), (key2036, -2), (key2155, 1), (key2150, 1), (key2168, -2), (key2150, -2), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, 1), (key2195, 1), (key2071, -1), (key2061, -1), (key2071, 1), (key2066, 1), (key2168, 1), (key2150, 1), (key2168, -1), (key2155, -1), (key2248, -1), (key2243, -1), (key2255, 1), (key2243, 1), (key2306, 1), (key2304, 1), (key2311, -1), (key2304, -1)]

def rawRow6720 : Integer.Sparse Key := [(key2036, -1), (key2036, -1), (key2031, 2), (key2071, -1), (key2071, -1), (key2066, 2), (key2066, 2), (key2061, -1), (key2061, -1), (key2096, 2), (key2093, -1), (key2093, -1), (key2036, 1), (key2036, 1), (key2031, -2), (key2168, 1), (key2168, 1), (key2155, -2), (key2155, -2), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, 1), (key2195, 1), (key2066, -1), (key2066, -1), (key2061, 1), (key2061, 1), (key2155, 1), (key2155, 1), (key2150, -1), (key2150, -1), (key2255, -1), (key2255, -1), (key2248, 1), (key2248, 1), (key2311, 1), (key2311, 1), (key2306, -1), (key2306, -1)]

def rawRow6721 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2093, 2), (key2031, -1), (key2036, -1), (key2061, 2), (key2071, 2), (key2093, -1), (key2096, -1), (key2036, 2), (key2066, -1), (key2071, -1), (key2150, 1), (key2155, 1), (key2195, -2), (key2031, 1), (key2036, 1), (key2150, -2), (key2168, -2), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, 1), (key2168, 1), (key2243, -1), (key2248, -1), (key2304, 1), (key2306, 1), (key2243, 1), (key2255, 1), (key2304, -1), (key2311, -1), (key2061, -1), (key2071, -1), (key2150, 1), (key2168, 1), (key2066, 1), (key2071, 1), (key2155, -1), (key2168, -1)]

def rawRow6722 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2093, 2), (key2036, -1), (key2031, -1), (key2071, 2), (key2061, 2), (key2096, -1), (key2093, -1), (key2036, 2), (key2071, -1), (key2066, -1), (key2155, 1), (key2150, 1), (key2195, -2), (key2036, 1), (key2031, 1), (key2168, -2), (key2150, -2), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, 1), (key2155, 1), (key2248, -1), (key2243, -1), (key2306, 1), (key2304, 1), (key2255, 1), (key2243, 1), (key2311, -1), (key2304, -1), (key2071, -1), (key2061, -1), (key2168, 1), (key2150, 1), (key2071, 1), (key2066, 1), (key2168, -1), (key2155, -1)]

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

def rawRow7381 : Integer.Sparse Key := [(key83, -24), (key83, 6), (key83, 6), (key83, 6), (key0, 6)]

end MUB6.Certificate.GramRows

end OAI
end


