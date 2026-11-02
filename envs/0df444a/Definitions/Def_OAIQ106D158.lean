-- Prove2me | Definitions.Def_OAIQ106D158
-- name    : OAIQ106D158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:09:26.309536+00:00
-- url     : https://prove2.me/theorems/a48c7e2d-8bca-484b-bf5c-372dfd994dc3
-- title:
--   Definitions bundle OAIQ106D158 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 790 declarations of OpenAI's Lean: 790 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow12861`, `OAI.MUB6.Certificate.GramRows.rawRow12862`, `OAI.MUB6.Certificate.GramRows.rawRow12863`, `OAI.MUB6.Certificate.GramRows.rawRow12864`, `OAI.MUB6.Certificate.GramRows.rawRow12865`, `OAI.MUB6.Certificate.GramRows.rawRow12866`, `OAI.MUB6.Certificate.GramRows.rawRow12867`, `OAI.MUB6.Certificate.GramRows.rawRow12868`, `OAI.MUB6.Certificate.GramRows.rawRow12869`, `OAI.MUB6.Certificate.GramRows.rawRow1287`, `OAI.MUB6.Certificate.GramRows.rawRow12870`, `OAI.MUB6.Certificate.GramRows.rawRow12871`, `OAI.MUB6.Certificate.GramRows.rawRow12872`, `OAI.MUB6.Certificate.GramRows.rawRow12873`, `OAI.MUB6.Certificate.GramRows.rawRow12874`, `OAI.MUB6.Certificate.GramRows.rawRow12875`, `OAI.MUB6.Certificate.GramRows.rawRow12876`, `OAI.MUB6.Certificate.GramRows.rawRow12877`, `OAI.MUB6.Certificate.GramRows.rawRow12878`, `OAI.MUB6.Certificate.GramRows.rawRow12879`, `OAI.MUB6.Certificate.GramRows.rawRow1288`, `OAI.MUB6.Certificate.GramRows.rawRow12880`, `OAI.MUB6.Certificate.GramRows.rawRow12881`, `OAI.MUB6.Certificate.GramRows.rawRow12882`, `OAI.MUB6.Certificate.GramRows.rawRow12883`, `OAI.MUB6.Certificate.GramRows.rawRow12884`, `OAI.MUB6.Certificate.GramRows.rawRow12885`, `OAI.MUB6.Certificate.GramRows.rawRow12886`, `OAI.MUB6.Certificate.GramRows.rawRow12887`, `OAI.MUB6.Certificate.GramRows.rawRow12888`, `OAI.MUB6.Certificate.GramRows.rawRow12889`, `OAI.MUB6.Certificate.GramRows.rawRow1289`, `OAI.MUB6.Certificate.GramRows.rawRow12890`, `OAI.MUB6.Certificate.GramRows.rawRow12891`, `OAI.MUB6.Certificate.GramRows.rawRow12892`, `OAI.MUB6.Certificate.GramRows.rawRow12893`, `OAI.MUB6.Certificate.GramRows.rawRow12894`, `OAI.MUB6.Certificate.GramRows.rawRow12895`, `OAI.MUB6.Certificate.GramRows.rawRow12896`, `OAI.MUB6.Certificate.GramRows.rawRow12897` and 750 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block1.lean), [`MutuallyUnbiased_GramRows_Block124`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block124.lean), [`MutuallyUnbiased_GramRows_Block125`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block125.lean), [`MutuallyUnbiased_GramRows_Block126`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block126.lean), [`MutuallyUnbiased_GramRows_Block127`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block127.lean), [`MutuallyUnbiased_GramRows_Block128`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block128.lean), [`MutuallyUnbiased_GramRows_Block129`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block129.lean), [`MutuallyUnbiased_GramRows_Block130`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block130.lean), [`MutuallyUnbiased_GramRows_Block168`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean), [`MutuallyUnbiased_GramRows_Block34`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block34.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_24`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_25`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13 : Integer.Sparse Key := [(key316, -1), (key319, -1), (key328, 2), (key302, 1), (key305, 1), (key328, -1), (key340, -1), (key305, -2), (key319, 1), (key335, 1), (key406, 1), (key409, 1), (key418, -2), (key236, -1), (key239, -1), (key578, 1), (key583, 1), (key239, 2), (key409, -1), (key418, -1), (key316, -1), (key319, -1), (key593, 1), (key595, 1), (key248, 1), (key251, 1), (key593, -1), (key601, -1), (key251, -1), (key260, -1), (key319, 1), (key328, 1), (key335, 2), (key467, -1), (key469, -1), (key267, -2), (key467, 1), (key475, 1), (key267, 1), (key271, 1), (key335, -1), (key340, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow129 : Integer.Sparse Key := [(key1312, -1), (key1318, -1), (key1326, 2), (key1292, 1), (key1298, 1), (key1326, -1), (key1354, -1), (key1298, -2), (key1318, 1), (key1351, 1), (key1542, 1), (key1548, 1), (key1556, -2), (key1387, -1), (key1393, -1), (key1556, 1), (key1899, 1), (key1393, 2), (key1548, -1), (key1896, -1), (key1569, -1), (key1575, -1), (key1624, 1), (key1683, 1), (key1420, 1), (key1426, 1), (key1624, -1), (key1920, -1), (key1426, -1), (key1472, -1), (key1575, 1), (key1903, 1), (key1593, 2), (key1633, -1), (key1689, -1), (key1444, -2), (key1633, 1), (key1926, 1), (key1444, 1), (key1480, 1), (key1593, -1), (key1911, -1)]

def rawRow130 : Integer.Sparse Key := [(key1318, -1), (key1312, -1), (key1326, 2), (key1298, 1), (key1292, 1), (key1354, -1), (key1326, -1), (key1298, -2), (key1351, 1), (key1318, 1), (key1548, 1), (key1542, 1), (key1556, -2), (key1393, -1), (key1387, -1), (key1899, 1), (key1556, 1), (key1393, 2), (key1896, -1), (key1548, -1), (key1575, -1), (key1569, -1), (key1683, 1), (key1624, 1), (key1426, 1), (key1420, 1), (key1920, -1), (key1624, -1), (key1472, -1), (key1426, -1), (key1903, 1), (key1575, 1), (key1593, 2), (key1689, -1), (key1633, -1), (key1444, -2), (key1926, 1), (key1633, 1), (key1480, 1), (key1444, 1), (key1911, -1), (key1593, -1)]

def rawRow131 : Integer.Sparse Key := [(key1318, -1), (key1326, -1), (key1312, 2), (key1351, 1), (key1354, 1), (key1292, -1), (key1312, -1), (key1351, -2), (key1298, 1), (key1318, 1), (key1548, 1), (key1556, 1), (key1542, -2), (key1896, -1), (key1899, -1), (key1387, 1), (key1542, 1), (key1896, 2), (key1393, -1), (key1548, -1), (key1681, -1), (key1683, -1), (key1569, 1), (key1618, 1), (key1918, 1), (key1920, 1), (key1420, -1), (key1618, -1), (key1903, -1), (key1918, -1), (key1472, 1), (key1681, 1), (key1689, 2), (key1593, -1), (key1633, -1), (key1926, -2), (key1444, 1), (key1633, 1), (key1911, 1), (key1926, 1), (key1480, -1), (key1689, -1)]

def rawRow132 : Integer.Sparse Key := [(key1326, -1), (key1318, -1), (key1312, 2), (key1354, 1), (key1351, 1), (key1312, -1), (key1292, -1), (key1351, -2), (key1318, 1), (key1298, 1), (key1556, 1), (key1548, 1), (key1542, -2), (key1899, -1), (key1896, -1), (key1542, 1), (key1387, 1), (key1896, 2), (key1548, -1), (key1393, -1), (key1683, -1), (key1681, -1), (key1618, 1), (key1569, 1), (key1920, 1), (key1918, 1), (key1618, -1), (key1420, -1), (key1918, -1), (key1903, -1), (key1681, 1), (key1472, 1), (key1689, 2), (key1633, -1), (key1593, -1), (key1926, -2), (key1633, 1), (key1444, 1), (key1926, 1), (key1911, 1), (key1689, -1), (key1480, -1)]

def rawRow134 : Integer.Sparse Key := [(key1351, -1), (key1354, -1), (key1351, 2), (key1318, 1), (key1326, 1), (key1298, -1), (key1318, -1), (key1312, -2), (key1292, 1), (key1312, 1), (key1896, 1), (key1899, 1), (key1896, -2), (key1548, -1), (key1556, -1), (key1393, 1), (key1548, 1), (key1542, 2), (key1387, -1), (key1542, -1), (key1918, -1), (key1920, -1), (key1903, 1), (key1918, 1), (key1681, 1), (key1683, 1), (key1472, -1), (key1681, -1), (key1569, -1), (key1618, -1), (key1420, 1), (key1618, 1), (key1926, 2), (key1911, -1), (key1926, -1), (key1689, -2), (key1480, 1), (key1689, 1), (key1593, 1), (key1633, 1), (key1444, -1), (key1633, -1)]

def rawRow135 : Integer.Sparse Key := [(key1354, -1), (key1351, -1), (key1351, 2), (key1326, 1), (key1318, 1), (key1318, -1), (key1298, -1), (key1312, -2), (key1312, 1), (key1292, 1), (key1899, 1), (key1896, 1), (key1896, -2), (key1556, -1), (key1548, -1), (key1548, 1), (key1393, 1), (key1542, 2), (key1542, -1), (key1387, -1), (key1920, -1), (key1918, -1), (key1918, 1), (key1903, 1), (key1683, 1), (key1681, 1), (key1681, -1), (key1472, -1), (key1618, -1), (key1569, -1), (key1618, 1), (key1420, 1), (key1926, 2), (key1926, -1), (key1911, -1), (key1689, -2), (key1689, 1), (key1480, 1), (key1633, 1), (key1593, 1), (key1633, -1), (key1444, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12861 : Integer.Sparse Key := [(key868, -6), (key882, -6), (key866, -6), (key866, -6), (key901, 2), (key913, 2), (key900, 2), (key901, 2), (key913, 2), (key734, 2), (key882, 2), (key732, 2), (key866, 2), (key900, 2), (key732, 2), (key866, 2)]

def rawRow12862 : Integer.Sparse Key := [(key882, -6), (key868, -6), (key866, -6), (key866, -6), (key913, 2), (key901, 2), (key900, 2), (key913, 2), (key901, 2), (key882, 2), (key734, 2), (key866, 2), (key732, 2), (key900, 2), (key866, 2), (key732, 2)]

def rawRow12863 : Integer.Sparse Key := [(key900, -6), (key901, -6), (key901, -6), (key913, -6), (key732, 2), (key734, 2), (key734, 2), (key866, 2), (key868, 2), (key866, 2), (key901, 2), (key868, 2), (key901, 2), (key882, 2), (key882, 2), (key913, 2)]

def rawRow12864 : Integer.Sparse Key := [(key901, -6), (key900, -6), (key901, -6), (key913, -6), (key734, 2), (key732, 2), (key734, 2), (key868, 2), (key866, 2), (key901, 2), (key866, 2), (key901, 2), (key868, 2), (key882, 2), (key913, 2), (key882, 2)]

def rawRow12865 : Integer.Sparse Key := [(key901, -6), (key901, -6), (key900, -6), (key913, -6), (key734, 2), (key734, 2), (key732, 2), (key901, 2), (key901, 2), (key868, 2), (key868, 2), (key866, 2), (key866, 2), (key913, 2), (key882, 2), (key882, 2)]

def rawRow12866 : Integer.Sparse Key := [(key900, -6), (key901, -6), (key913, -6), (key901, -6), (key866, 2), (key868, 2), (key882, 2), (key732, 2), (key734, 2), (key866, 2), (key901, 2), (key882, 2), (key913, 2), (key734, 2), (key868, 2), (key901, 2)]

def rawRow12867 : Integer.Sparse Key := [(key901, -6), (key900, -6), (key913, -6), (key901, -6), (key868, 2), (key866, 2), (key882, 2), (key734, 2), (key732, 2), (key901, 2), (key866, 2), (key913, 2), (key882, 2), (key734, 2), (key901, 2), (key868, 2)]

def rawRow12868 : Integer.Sparse Key := [(key900, -6), (key913, -6), (key901, -6), (key901, -6), (key866, 2), (key882, 2), (key868, 2), (key866, 2), (key882, 2), (key732, 2), (key913, 2), (key734, 2), (key901, 2), (key868, 2), (key734, 2), (key901, 2)]

def rawRow12869 : Integer.Sparse Key := [(key913, -6), (key900, -6), (key901, -6), (key901, -6), (key882, 2), (key866, 2), (key868, 2), (key882, 2), (key866, 2), (key913, 2), (key732, 2), (key901, 2), (key734, 2), (key868, 2), (key901, 2), (key734, 2)]

def rawRow12870 : Integer.Sparse Key := [(key901, -6), (key913, -6), (key900, -6), (key901, -6), (key868, 2), (key882, 2), (key866, 2), (key901, 2), (key913, 2), (key734, 2), (key882, 2), (key732, 2), (key866, 2), (key901, 2), (key734, 2), (key868, 2)]

def rawRow12871 : Integer.Sparse Key := [(key913, -6), (key901, -6), (key900, -6), (key901, -6), (key882, 2), (key868, 2), (key866, 2), (key913, 2), (key901, 2), (key882, 2), (key734, 2), (key866, 2), (key732, 2), (key901, 2), (key868, 2), (key734, 2)]

def rawRow12872 : Integer.Sparse Key := [(key901, -6), (key901, -6), (key913, -6), (key900, -6), (key901, 2), (key901, 2), (key913, 2), (key734, 2), (key734, 2), (key868, 2), (key868, 2), (key882, 2), (key882, 2), (key732, 2), (key866, 2), (key866, 2)]

def rawRow12873 : Integer.Sparse Key := [(key901, -6), (key913, -6), (key901, -6), (key900, -6), (key901, 2), (key913, 2), (key901, 2), (key868, 2), (key882, 2), (key734, 2), (key882, 2), (key734, 2), (key868, 2), (key866, 2), (key732, 2), (key866, 2)]

def rawRow12874 : Integer.Sparse Key := [(key913, -6), (key901, -6), (key901, -6), (key900, -6), (key913, 2), (key901, 2), (key901, 2), (key882, 2), (key868, 2), (key882, 2), (key734, 2), (key868, 2), (key734, 2), (key866, 2), (key866, 2), (key732, 2)]

def rawRow12875 : Integer.Sparse Key := [(key498, 6), (key498, 6), (key504, 6), (key666, 6), (key232, -6), (key504, -6), (key562, -6), (key562, -6)]

def rawRow12876 : Integer.Sparse Key := [(key498, 6), (key504, 6), (key498, 6), (key666, 6), (key232, -6), (key562, -6), (key504, -6), (key562, -6)]

def rawRow12877 : Integer.Sparse Key := [(key504, 6), (key498, 6), (key498, 6), (key666, 6), (key232, -6), (key562, -6), (key562, -6), (key504, -6)]

def rawRow12878 : Integer.Sparse Key := [(key498, 6), (key498, 6), (key666, 6), (key504, 6), (key504, -6), (key232, -6), (key562, -6), (key562, -6)]

def rawRow12879 : Integer.Sparse Key := [(key498, 6), (key666, 6), (key498, 6), (key504, 6), (key504, -6), (key562, -6), (key232, -6), (key562, -6)]

def rawRow12880 : Integer.Sparse Key := [(key666, 6), (key498, 6), (key498, 6), (key504, 6), (key504, -6), (key562, -6), (key562, -6), (key232, -6)]

def rawRow12881 : Integer.Sparse Key := [(key498, 6), (key504, 6), (key666, 6), (key498, 6), (key562, -6), (key232, -6), (key504, -6), (key562, -6)]

def rawRow12882 : Integer.Sparse Key := [(key504, 6), (key498, 6), (key666, 6), (key498, 6), (key562, -6), (key232, -6), (key562, -6), (key504, -6)]

def rawRow12883 : Integer.Sparse Key := [(key498, 6), (key666, 6), (key504, 6), (key498, 6), (key562, -6), (key504, -6), (key232, -6), (key562, -6)]

def rawRow12884 : Integer.Sparse Key := [(key666, 6), (key498, 6), (key504, 6), (key498, 6), (key562, -6), (key504, -6), (key562, -6), (key232, -6)]

def rawRow12885 : Integer.Sparse Key := [(key504, 6), (key666, 6), (key498, 6), (key498, 6), (key562, -6), (key562, -6), (key232, -6), (key504, -6)]

def rawRow12886 : Integer.Sparse Key := [(key666, 6), (key504, 6), (key498, 6), (key498, 6), (key562, -6), (key562, -6), (key504, -6), (key232, -6)]

def rawRow12887 : Integer.Sparse Key := [(key552, 6), (key562, 6), (key562, 6), (key683, 6), (key226, -6), (key498, -6), (key498, -6), (key552, -6)]

def rawRow12888 : Integer.Sparse Key := [(key562, 6), (key552, 6), (key562, 6), (key683, 6), (key226, -6), (key498, -6), (key552, -6), (key498, -6)]

def rawRow12889 : Integer.Sparse Key := [(key562, 6), (key562, 6), (key552, 6), (key683, 6), (key226, -6), (key552, -6), (key498, -6), (key498, -6)]

def rawRow12890 : Integer.Sparse Key := [(key552, 6), (key562, 6), (key683, 6), (key562, 6), (key498, -6), (key226, -6), (key498, -6), (key552, -6)]

def rawRow12891 : Integer.Sparse Key := [(key562, 6), (key552, 6), (key683, 6), (key562, 6), (key498, -6), (key226, -6), (key552, -6), (key498, -6)]

def rawRow12892 : Integer.Sparse Key := [(key552, 6), (key683, 6), (key562, 6), (key562, 6), (key498, -6), (key498, -6), (key226, -6), (key552, -6)]

def rawRow12893 : Integer.Sparse Key := [(key683, 6), (key552, 6), (key562, 6), (key562, 6), (key498, -6), (key498, -6), (key552, -6), (key226, -6)]

def rawRow12894 : Integer.Sparse Key := [(key562, 6), (key683, 6), (key552, 6), (key562, 6), (key498, -6), (key552, -6), (key226, -6), (key498, -6)]

def rawRow12895 : Integer.Sparse Key := [(key683, 6), (key562, 6), (key552, 6), (key562, 6), (key498, -6), (key552, -6), (key498, -6), (key226, -6)]

def rawRow12896 : Integer.Sparse Key := [(key562, 6), (key562, 6), (key683, 6), (key552, 6), (key552, -6), (key226, -6), (key498, -6), (key498, -6)]

def rawRow12897 : Integer.Sparse Key := [(key562, 6), (key683, 6), (key562, 6), (key552, 6), (key552, -6), (key498, -6), (key226, -6), (key498, -6)]

def rawRow12898 : Integer.Sparse Key := [(key683, 6), (key562, 6), (key562, 6), (key552, 6), (key552, -6), (key498, -6), (key498, -6), (key226, -6)]

def rawRow12899 : Integer.Sparse Key := [(key1704, -6), (key1704, -6), (key1708, -6), (key1857, -6), (key1281, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1704, 2), (key1753, 2), (key1753, 2), (key1758, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1888, 2)]

def rawRow12900 : Integer.Sparse Key := [(key1704, -6), (key1708, -6), (key1704, -6), (key1857, -6), (key1281, 2), (key1285, 2), (key1281, 2), (key1753, 2), (key1758, 2), (key1704, 2), (key1758, 2), (key1704, 2), (key1753, 2), (key1888, 2), (key1857, 2), (key1888, 2)]

def rawRow12901 : Integer.Sparse Key := [(key1708, -6), (key1704, -6), (key1704, -6), (key1857, -6), (key1285, 2), (key1281, 2), (key1281, 2), (key1758, 2), (key1753, 2), (key1758, 2), (key1704, 2), (key1753, 2), (key1704, 2), (key1888, 2), (key1888, 2), (key1857, 2)]

def rawRow12902 : Integer.Sparse Key := [(key1704, -6), (key1704, -6), (key1857, -6), (key1708, -6), (key1704, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1281, 2), (key1753, 2), (key1753, 2), (key1888, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1758, 2)]

def rawRow12903 : Integer.Sparse Key := [(key1704, -6), (key1857, -6), (key1704, -6), (key1708, -6), (key1704, 2), (key1857, 2), (key1704, 2), (key1753, 2), (key1888, 2), (key1281, 2), (key1888, 2), (key1281, 2), (key1753, 2), (key1758, 2), (key1285, 2), (key1758, 2)]

def rawRow12904 : Integer.Sparse Key := [(key1857, -6), (key1704, -6), (key1704, -6), (key1708, -6), (key1857, 2), (key1704, 2), (key1704, 2), (key1888, 2), (key1753, 2), (key1888, 2), (key1281, 2), (key1753, 2), (key1281, 2), (key1758, 2), (key1758, 2), (key1285, 2)]

def rawRow12905 : Integer.Sparse Key := [(key1704, -6), (key1708, -6), (key1857, -6), (key1704, -6), (key1753, 2), (key1758, 2), (key1888, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1281, 2), (key1704, 2), (key1753, 2)]

def rawRow12906 : Integer.Sparse Key := [(key1708, -6), (key1704, -6), (key1857, -6), (key1704, -6), (key1758, 2), (key1753, 2), (key1888, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1281, 2), (key1753, 2), (key1704, 2)]

def rawRow12907 : Integer.Sparse Key := [(key1704, -6), (key1857, -6), (key1708, -6), (key1704, -6), (key1753, 2), (key1888, 2), (key1758, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1704, 2), (key1281, 2), (key1753, 2)]

def rawRow12908 : Integer.Sparse Key := [(key1857, -6), (key1704, -6), (key1708, -6), (key1704, -6), (key1888, 2), (key1753, 2), (key1758, 2), (key1857, 2), (key1704, 2), (key1888, 2), (key1281, 2), (key1758, 2), (key1285, 2), (key1704, 2), (key1753, 2), (key1281, 2)]

def rawRow12909 : Integer.Sparse Key := [(key1708, -6), (key1857, -6), (key1704, -6), (key1704, -6), (key1758, 2), (key1888, 2), (key1753, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1753, 2), (key1281, 2), (key1704, 2)]

def rawRow12910 : Integer.Sparse Key := [(key1857, -6), (key1708, -6), (key1704, -6), (key1704, -6), (key1888, 2), (key1758, 2), (key1753, 2), (key1888, 2), (key1758, 2), (key1857, 2), (key1285, 2), (key1704, 2), (key1281, 2), (key1753, 2), (key1704, 2), (key1281, 2)]

def rawRow12911 : Integer.Sparse Key := [(key1753, -6), (key1758, -6), (key1758, -6), (key1888, -6), (key1281, 2), (key1285, 2), (key1285, 2), (key1704, 2), (key1708, 2), (key1704, 2), (key1758, 2), (key1708, 2), (key1758, 2), (key1857, 2), (key1857, 2), (key1888, 2)]

def rawRow12912 : Integer.Sparse Key := [(key1758, -6), (key1753, -6), (key1758, -6), (key1888, -6), (key1285, 2), (key1281, 2), (key1285, 2), (key1708, 2), (key1704, 2), (key1758, 2), (key1704, 2), (key1758, 2), (key1708, 2), (key1857, 2), (key1888, 2), (key1857, 2)]

def rawRow12913 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1753, -6), (key1888, -6), (key1285, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1758, 2), (key1708, 2), (key1708, 2), (key1704, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1857, 2)]

def rawRow12914 : Integer.Sparse Key := [(key1753, -6), (key1758, -6), (key1888, -6), (key1758, -6), (key1704, 2), (key1708, 2), (key1857, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1285, 2), (key1708, 2), (key1758, 2)]

def rawRow12915 : Integer.Sparse Key := [(key1758, -6), (key1753, -6), (key1888, -6), (key1758, -6), (key1708, 2), (key1704, 2), (key1857, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1285, 2), (key1758, 2), (key1708, 2)]

def rawRow12916 : Integer.Sparse Key := [(key1753, -6), (key1888, -6), (key1758, -6), (key1758, -6), (key1704, 2), (key1857, 2), (key1708, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1708, 2), (key1285, 2), (key1758, 2)]

def rawRow12917 : Integer.Sparse Key := [(key1888, -6), (key1753, -6), (key1758, -6), (key1758, -6), (key1857, 2), (key1704, 2), (key1708, 2), (key1857, 2), (key1704, 2), (key1888, 2), (key1281, 2), (key1758, 2), (key1285, 2), (key1708, 2), (key1758, 2), (key1285, 2)]

def rawRow12918 : Integer.Sparse Key := [(key1758, -6), (key1888, -6), (key1753, -6), (key1758, -6), (key1708, 2), (key1857, 2), (key1704, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1758, 2), (key1285, 2), (key1708, 2)]

def rawRow12919 : Integer.Sparse Key := [(key1888, -6), (key1758, -6), (key1753, -6), (key1758, -6), (key1857, 2), (key1708, 2), (key1704, 2), (key1888, 2), (key1758, 2), (key1857, 2), (key1285, 2), (key1704, 2), (key1281, 2), (key1758, 2), (key1708, 2), (key1285, 2)]

def rawRow12920 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1888, -6), (key1753, -6), (key1758, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1285, 2), (key1708, 2), (key1708, 2), (key1857, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1704, 2)]

def rawRow12921 : Integer.Sparse Key := [(key1758, -6), (key1888, -6), (key1758, -6), (key1753, -6), (key1758, 2), (key1888, 2), (key1758, 2), (key1708, 2), (key1857, 2), (key1285, 2), (key1857, 2), (key1285, 2), (key1708, 2), (key1704, 2), (key1281, 2), (key1704, 2)]

def rawRow12922 : Integer.Sparse Key := [(key1888, -6), (key1758, -6), (key1758, -6), (key1753, -6), (key1888, 2), (key1758, 2), (key1758, 2), (key1857, 2), (key1708, 2), (key1857, 2), (key1285, 2), (key1708, 2), (key1285, 2), (key1704, 2), (key1704, 2), (key1281, 2)]

def rawRow12923 : Integer.Sparse Key := [(key1494, -6), (key1720, -6), (key1726, -6), (key1726, -6), (key1368, 6), (key1720, 6), (key1744, 6), (key1744, 6)]

def rawRow12924 : Integer.Sparse Key := [(key1494, -6), (key1726, -6), (key1720, -6), (key1726, -6), (key1368, 6), (key1744, 6), (key1720, 6), (key1744, 6)]

def rawRow12925 : Integer.Sparse Key := [(key1494, -6), (key1726, -6), (key1726, -6), (key1720, -6), (key1368, 6), (key1744, 6), (key1744, 6), (key1720, 6)]

def rawRow12926 : Integer.Sparse Key := [(key1720, -6), (key1494, -6), (key1726, -6), (key1726, -6), (key1720, 6), (key1368, 6), (key1744, 6), (key1744, 6)]

def rawRow12927 : Integer.Sparse Key := [(key1720, -6), (key1726, -6), (key1494, -6), (key1726, -6), (key1720, 6), (key1744, 6), (key1368, 6), (key1744, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12928 : Integer.Sparse Key := [(key1720, -6), (key1726, -6), (key1726, -6), (key1494, -6), (key1720, 6), (key1744, 6), (key1744, 6), (key1368, 6)]

def rawRow12929 : Integer.Sparse Key := [(key1726, -6), (key1494, -6), (key1720, -6), (key1726, -6), (key1744, 6), (key1368, 6), (key1720, 6), (key1744, 6)]

def rawRow12930 : Integer.Sparse Key := [(key1726, -6), (key1494, -6), (key1726, -6), (key1720, -6), (key1744, 6), (key1368, 6), (key1744, 6), (key1720, 6)]

def rawRow12931 : Integer.Sparse Key := [(key1726, -6), (key1720, -6), (key1494, -6), (key1726, -6), (key1744, 6), (key1720, 6), (key1368, 6), (key1744, 6)]

def rawRow12932 : Integer.Sparse Key := [(key1726, -6), (key1720, -6), (key1726, -6), (key1494, -6), (key1744, 6), (key1720, 6), (key1744, 6), (key1368, 6)]

def rawRow12933 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1494, -6), (key1720, -6), (key1744, 6), (key1744, 6), (key1368, 6), (key1720, 6)]

def rawRow12934 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1720, -6), (key1494, -6), (key1744, 6), (key1744, 6), (key1720, 6), (key1368, 6)]

def rawRow12935 : Integer.Sparse Key := [(key1516, -6), (key1744, -6), (key1744, -6), (key1755, -6), (key1377, 6), (key1726, 6), (key1726, 6), (key1755, 6)]

def rawRow12936 : Integer.Sparse Key := [(key1516, -6), (key1744, -6), (key1755, -6), (key1744, -6), (key1377, 6), (key1726, 6), (key1755, 6), (key1726, 6)]

def rawRow12937 : Integer.Sparse Key := [(key1516, -6), (key1755, -6), (key1744, -6), (key1744, -6), (key1377, 6), (key1755, 6), (key1726, 6), (key1726, 6)]

def rawRow12938 : Integer.Sparse Key := [(key1744, -6), (key1516, -6), (key1744, -6), (key1755, -6), (key1726, 6), (key1377, 6), (key1726, 6), (key1755, 6)]

def rawRow12939 : Integer.Sparse Key := [(key1744, -6), (key1516, -6), (key1755, -6), (key1744, -6), (key1726, 6), (key1377, 6), (key1755, 6), (key1726, 6)]

def rawRow12940 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1516, -6), (key1755, -6), (key1726, 6), (key1726, 6), (key1377, 6), (key1755, 6)]

def rawRow12941 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1755, -6), (key1516, -6), (key1726, 6), (key1726, 6), (key1755, 6), (key1377, 6)]

def rawRow12942 : Integer.Sparse Key := [(key1744, -6), (key1755, -6), (key1516, -6), (key1744, -6), (key1726, 6), (key1755, 6), (key1377, 6), (key1726, 6)]

def rawRow12943 : Integer.Sparse Key := [(key1744, -6), (key1755, -6), (key1744, -6), (key1516, -6), (key1726, 6), (key1755, 6), (key1726, 6), (key1377, 6)]

def rawRow12944 : Integer.Sparse Key := [(key1755, -6), (key1516, -6), (key1744, -6), (key1744, -6), (key1755, 6), (key1377, 6), (key1726, 6), (key1726, 6)]

def rawRow12945 : Integer.Sparse Key := [(key1755, -6), (key1744, -6), (key1516, -6), (key1744, -6), (key1755, 6), (key1726, 6), (key1377, 6), (key1726, 6)]

def rawRow12946 : Integer.Sparse Key := [(key1755, -6), (key1744, -6), (key1744, -6), (key1516, -6), (key1755, 6), (key1726, 6), (key1726, 6), (key1377, 6)]

def rawRow12947 : Integer.Sparse Key := [(key1366, -2), (key1370, -2), (key1370, -2), (key1718, -2), (key1747, -2), (key1747, -2), (key1865, -2), (key1865, -2), (key1880, -2), (key1880, -2), (key1883, -2), (key1883, -2), (key1366, 2), (key1379, 2), (key1379, 2), (key1492, 2), (key1519, 2), (key1519, 2), (key1870, 2), (key1870, 2), (key1880, 2), (key1880, 2), (key1891, 2), (key1891, 2)]

def rawRow12948 : Integer.Sparse Key := [(key1370, -2), (key1366, -2), (key1370, -2), (key1747, -2), (key1718, -2), (key1747, -2), (key1880, -2), (key1883, -2), (key1865, -2), (key1883, -2), (key1865, -2), (key1880, -2), (key1379, 2), (key1366, 2), (key1379, 2), (key1519, 2), (key1492, 2), (key1519, 2), (key1880, 2), (key1891, 2), (key1870, 2), (key1891, 2), (key1870, 2), (key1880, 2)]

def rawRow12949 : Integer.Sparse Key := [(key1370, -2), (key1370, -2), (key1366, -2), (key1747, -2), (key1747, -2), (key1718, -2), (key1883, -2), (key1880, -2), (key1883, -2), (key1865, -2), (key1880, -2), (key1865, -2), (key1379, 2), (key1379, 2), (key1366, 2), (key1519, 2), (key1519, 2), (key1492, 2), (key1891, 2), (key1880, 2), (key1891, 2), (key1870, 2), (key1880, 2), (key1870, 2)]

def rawRow12950 : Integer.Sparse Key := [(key1718, -2), (key1865, -2), (key1865, -2), (key1366, -2), (key1880, -2), (key1880, -2), (key1370, -2), (key1370, -2), (key1747, -2), (key1747, -2), (key1883, -2), (key1883, -2), (key1492, 2), (key1870, 2), (key1870, 2), (key1366, 2), (key1880, 2), (key1880, 2), (key1379, 2), (key1379, 2), (key1519, 2), (key1519, 2), (key1891, 2), (key1891, 2)]

def rawRow12951 : Integer.Sparse Key := [(key1865, -2), (key1718, -2), (key1865, -2), (key1880, -2), (key1366, -2), (key1880, -2), (key1747, -2), (key1883, -2), (key1370, -2), (key1883, -2), (key1370, -2), (key1747, -2), (key1870, 2), (key1492, 2), (key1870, 2), (key1880, 2), (key1366, 2), (key1880, 2), (key1519, 2), (key1891, 2), (key1379, 2), (key1891, 2), (key1379, 2), (key1519, 2)]

def rawRow12952 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1718, -2), (key1880, -2), (key1880, -2), (key1366, -2), (key1883, -2), (key1747, -2), (key1883, -2), (key1370, -2), (key1747, -2), (key1370, -2), (key1870, 2), (key1870, 2), (key1492, 2), (key1880, 2), (key1880, 2), (key1366, 2), (key1891, 2), (key1519, 2), (key1891, 2), (key1379, 2), (key1519, 2), (key1379, 2)]

def rawRow12953 : Integer.Sparse Key := [(key1747, -2), (key1880, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1883, -2), (key1366, -2), (key1370, -2), (key1718, -2), (key1747, -2), (key1865, -2), (key1880, -2), (key1519, 2), (key1880, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1891, 2), (key1366, 2), (key1379, 2), (key1492, 2), (key1519, 2), (key1870, 2), (key1880, 2)]

def rawRow12954 : Integer.Sparse Key := [(key1747, -2), (key1883, -2), (key1880, -2), (key1370, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1366, -2), (key1747, -2), (key1718, -2), (key1880, -2), (key1865, -2), (key1519, 2), (key1891, 2), (key1880, 2), (key1379, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1366, 2), (key1519, 2), (key1492, 2), (key1880, 2), (key1870, 2)]

def rawRow12955 : Integer.Sparse Key := [(key1880, -2), (key1747, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1883, -2), (key1718, -2), (key1865, -2), (key1366, -2), (key1880, -2), (key1370, -2), (key1747, -2), (key1880, 2), (key1519, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1891, 2), (key1492, 2), (key1870, 2), (key1366, 2), (key1880, 2), (key1379, 2), (key1519, 2)]

def rawRow12956 : Integer.Sparse Key := [(key1880, -2), (key1883, -2), (key1747, -2), (key1865, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1718, -2), (key1880, -2), (key1366, -2), (key1747, -2), (key1370, -2), (key1880, 2), (key1891, 2), (key1519, 2), (key1870, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1492, 2), (key1880, 2), (key1366, 2), (key1519, 2), (key1379, 2)]

def rawRow12957 : Integer.Sparse Key := [(key1883, -2), (key1747, -2), (key1880, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1747, -2), (key1880, -2), (key1370, -2), (key1865, -2), (key1366, -2), (key1718, -2), (key1891, 2), (key1519, 2), (key1880, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1519, 2), (key1880, 2), (key1379, 2), (key1870, 2), (key1366, 2), (key1492, 2)]

def rawRow12958 : Integer.Sparse Key := [(key1883, -2), (key1880, -2), (key1747, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1880, -2), (key1747, -2), (key1865, -2), (key1370, -2), (key1718, -2), (key1366, -2), (key1891, 2), (key1880, 2), (key1519, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1880, 2), (key1519, 2), (key1870, 2), (key1379, 2), (key1492, 2), (key1366, 2)]

def rawRow12959 : Integer.Sparse Key := [(key1379, -2), (key1379, -2), (key1381, -2), (key1728, -2), (key1728, -2), (key1761, -2), (key1870, -2), (key1872, -2), (key1870, -2), (key1891, -2), (key1872, -2), (key1891, -2), (key1370, 2), (key1370, 2), (key1381, 2), (key1496, 2), (key1496, 2), (key1522, 2), (key1865, 2), (key1872, 2), (key1865, 2), (key1883, 2), (key1872, 2), (key1883, 2)]

def rawRow12960 : Integer.Sparse Key := [(key1379, -2), (key1381, -2), (key1379, -2), (key1728, -2), (key1761, -2), (key1728, -2), (key1872, -2), (key1870, -2), (key1891, -2), (key1870, -2), (key1891, -2), (key1872, -2), (key1370, 2), (key1381, 2), (key1370, 2), (key1496, 2), (key1522, 2), (key1496, 2), (key1872, 2), (key1865, 2), (key1883, 2), (key1865, 2), (key1883, 2), (key1872, 2)]

def rawRow12961 : Integer.Sparse Key := [(key1381, -2), (key1379, -2), (key1379, -2), (key1761, -2), (key1728, -2), (key1728, -2), (key1891, -2), (key1891, -2), (key1872, -2), (key1872, -2), (key1870, -2), (key1870, -2), (key1381, 2), (key1370, 2), (key1370, 2), (key1522, 2), (key1496, 2), (key1496, 2), (key1883, 2), (key1883, 2), (key1872, 2), (key1872, 2), (key1865, 2), (key1865, 2)]

def rawRow12962 : Integer.Sparse Key := [(key1728, -2), (key1870, -2), (key1872, -2), (key1379, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1381, -2), (key1728, -2), (key1761, -2), (key1872, -2), (key1891, -2), (key1496, 2), (key1865, 2), (key1872, 2), (key1370, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1381, 2), (key1496, 2), (key1522, 2), (key1872, 2), (key1883, 2)]

def rawRow12963 : Integer.Sparse Key := [(key1728, -2), (key1872, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1870, -2), (key1381, -2), (key1379, -2), (key1761, -2), (key1728, -2), (key1891, -2), (key1872, -2), (key1496, 2), (key1872, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1865, 2), (key1381, 2), (key1370, 2), (key1522, 2), (key1496, 2), (key1883, 2), (key1872, 2)]

def rawRow12964 : Integer.Sparse Key := [(key1870, -2), (key1728, -2), (key1872, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1728, -2), (key1872, -2), (key1379, -2), (key1891, -2), (key1381, -2), (key1761, -2), (key1865, 2), (key1496, 2), (key1872, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1496, 2), (key1872, 2), (key1370, 2), (key1883, 2), (key1381, 2), (key1522, 2)]

def rawRow12965 : Integer.Sparse Key := [(key1870, -2), (key1872, -2), (key1728, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1872, -2), (key1728, -2), (key1891, -2), (key1379, -2), (key1761, -2), (key1381, -2), (key1865, 2), (key1872, 2), (key1496, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1872, 2), (key1496, 2), (key1883, 2), (key1370, 2), (key1522, 2), (key1381, 2)]

def rawRow12966 : Integer.Sparse Key := [(key1872, -2), (key1728, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1870, -2), (key1761, -2), (key1891, -2), (key1381, -2), (key1872, -2), (key1379, -2), (key1728, -2), (key1872, 2), (key1496, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1865, 2), (key1522, 2), (key1883, 2), (key1381, 2), (key1872, 2), (key1370, 2), (key1496, 2)]

def rawRow12967 : Integer.Sparse Key := [(key1872, -2), (key1870, -2), (key1728, -2), (key1891, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1761, -2), (key1872, -2), (key1381, -2), (key1728, -2), (key1379, -2), (key1872, 2), (key1865, 2), (key1496, 2), (key1883, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1522, 2), (key1872, 2), (key1381, 2), (key1496, 2), (key1370, 2)]

def rawRow12968 : Integer.Sparse Key := [(key1761, -2), (key1891, -2), (key1891, -2), (key1381, -2), (key1872, -2), (key1872, -2), (key1379, -2), (key1379, -2), (key1728, -2), (key1728, -2), (key1870, -2), (key1870, -2), (key1522, 2), (key1883, 2), (key1883, 2), (key1381, 2), (key1872, 2), (key1872, 2), (key1370, 2), (key1370, 2), (key1496, 2), (key1496, 2), (key1865, 2), (key1865, 2)]

def rawRow12969 : Integer.Sparse Key := [(key1891, -2), (key1761, -2), (key1891, -2), (key1872, -2), (key1381, -2), (key1872, -2), (key1728, -2), (key1870, -2), (key1379, -2), (key1870, -2), (key1379, -2), (key1728, -2), (key1883, 2), (key1522, 2), (key1883, 2), (key1872, 2), (key1381, 2), (key1872, 2), (key1496, 2), (key1865, 2), (key1370, 2), (key1865, 2), (key1370, 2), (key1496, 2)]

def rawRow12970 : Integer.Sparse Key := [(key1891, -2), (key1891, -2), (key1761, -2), (key1872, -2), (key1872, -2), (key1381, -2), (key1870, -2), (key1728, -2), (key1870, -2), (key1379, -2), (key1728, -2), (key1379, -2), (key1883, 2), (key1883, 2), (key1522, 2), (key1872, 2), (key1872, 2), (key1381, 2), (key1865, 2), (key1496, 2), (key1865, 2), (key1370, 2), (key1496, 2), (key1370, 2)]

def rawRow12971 : Integer.Sparse Key := [(key227, 2), (key231, 2), (key231, 2), (key499, 2), (key560, 2), (key560, 2), (key623, 2), (key623, 2), (key649, 2), (key649, 2), (key653, 2), (key653, 2), (key231, -2), (key231, -2), (key233, -2), (key503, -2), (key503, -2), (key560, -2), (key560, -2), (key564, -2), (key564, -2), (key625, -2), (key653, -2), (key653, -2)]

def rawRow12972 : Integer.Sparse Key := [(key231, 2), (key227, 2), (key231, 2), (key560, 2), (key499, 2), (key560, 2), (key649, 2), (key653, 2), (key623, 2), (key653, 2), (key623, 2), (key649, 2), (key231, -2), (key233, -2), (key231, -2), (key560, -2), (key564, -2), (key503, -2), (key564, -2), (key503, -2), (key560, -2), (key653, -2), (key625, -2), (key653, -2)]

def rawRow12973 : Integer.Sparse Key := [(key231, 2), (key231, 2), (key227, 2), (key560, 2), (key560, 2), (key499, 2), (key653, 2), (key649, 2), (key653, 2), (key623, 2), (key649, 2), (key623, 2), (key233, -2), (key231, -2), (key231, -2), (key564, -2), (key560, -2), (key564, -2), (key503, -2), (key560, -2), (key503, -2), (key653, -2), (key653, -2), (key625, -2)]

def rawRow12974 : Integer.Sparse Key := [(key499, 2), (key623, 2), (key623, 2), (key227, 2), (key649, 2), (key649, 2), (key231, 2), (key231, 2), (key560, 2), (key560, 2), (key653, 2), (key653, 2), (key503, -2), (key503, -2), (key625, -2), (key231, -2), (key231, -2), (key560, -2), (key560, -2), (key653, -2), (key653, -2), (key233, -2), (key564, -2), (key564, -2)]

def rawRow12975 : Integer.Sparse Key := [(key623, 2), (key499, 2), (key623, 2), (key649, 2), (key227, 2), (key649, 2), (key560, 2), (key653, 2), (key231, 2), (key653, 2), (key231, 2), (key560, 2), (key503, -2), (key625, -2), (key503, -2), (key560, -2), (key653, -2), (key231, -2), (key653, -2), (key231, -2), (key560, -2), (key564, -2), (key233, -2), (key564, -2)]

def rawRow12976 : Integer.Sparse Key := [(key623, 2), (key623, 2), (key499, 2), (key649, 2), (key649, 2), (key227, 2), (key653, 2), (key560, 2), (key653, 2), (key231, 2), (key560, 2), (key231, 2), (key625, -2), (key503, -2), (key503, -2), (key653, -2), (key560, -2), (key653, -2), (key231, -2), (key560, -2), (key231, -2), (key564, -2), (key564, -2), (key233, -2)]

def rawRow12977 : Integer.Sparse Key := [(key560, 2), (key649, 2), (key653, 2), (key231, 2), (key623, 2), (key653, 2), (key227, 2), (key231, 2), (key499, 2), (key560, 2), (key623, 2), (key649, 2), (key560, -2), (key564, -2), (key653, -2), (key231, -2), (key233, -2), (key503, -2), (key564, -2), (key625, -2), (key653, -2), (key231, -2), (key503, -2), (key560, -2)]

def rawRow12978 : Integer.Sparse Key := [(key560, 2), (key653, 2), (key649, 2), (key231, 2), (key653, 2), (key623, 2), (key231, 2), (key227, 2), (key560, 2), (key499, 2), (key649, 2), (key623, 2), (key564, -2), (key560, -2), (key653, -2), (key233, -2), (key231, -2), (key564, -2), (key503, -2), (key653, -2), (key625, -2), (key231, -2), (key560, -2), (key503, -2)]

def rawRow12979 : Integer.Sparse Key := [(key649, 2), (key560, 2), (key653, 2), (key623, 2), (key231, 2), (key653, 2), (key499, 2), (key623, 2), (key227, 2), (key649, 2), (key231, 2), (key560, 2), (key560, -2), (key653, -2), (key564, -2), (key503, -2), (key625, -2), (key231, -2), (key653, -2), (key233, -2), (key564, -2), (key503, -2), (key231, -2), (key560, -2)]

def rawRow12980 : Integer.Sparse Key := [(key649, 2), (key653, 2), (key560, 2), (key623, 2), (key653, 2), (key231, 2), (key623, 2), (key499, 2), (key649, 2), (key227, 2), (key560, 2), (key231, 2), (key653, -2), (key560, -2), (key564, -2), (key625, -2), (key503, -2), (key653, -2), (key231, -2), (key564, -2), (key233, -2), (key503, -2), (key560, -2), (key231, -2)]

def rawRow12981 : Integer.Sparse Key := [(key653, 2), (key560, 2), (key649, 2), (key653, 2), (key231, 2), (key623, 2), (key560, 2), (key649, 2), (key231, 2), (key623, 2), (key227, 2), (key499, 2), (key564, -2), (key653, -2), (key560, -2), (key564, -2), (key653, -2), (key233, -2), (key625, -2), (key231, -2), (key503, -2), (key560, -2), (key231, -2), (key503, -2)]

def rawRow12982 : Integer.Sparse Key := [(key653, 2), (key649, 2), (key560, 2), (key653, 2), (key623, 2), (key231, 2), (key649, 2), (key560, 2), (key623, 2), (key231, 2), (key499, 2), (key227, 2), (key653, -2), (key564, -2), (key560, -2), (key653, -2), (key564, -2), (key625, -2), (key233, -2), (key503, -2), (key231, -2), (key560, -2), (key503, -2), (key231, -2)]

def rawRow12983 : Integer.Sparse Key := [(key231, 2), (key231, 2), (key233, 2), (key503, 2), (key503, 2), (key564, 2), (key623, 2), (key625, 2), (key623, 2), (key653, 2), (key625, 2), (key653, 2), (key227, -2), (key231, -2), (key231, -2), (key499, -2), (key503, -2), (key499, -2), (key560, -2), (key503, -2), (key560, -2), (key623, -2), (key623, -2), (key649, -2)]

def rawRow12984 : Integer.Sparse Key := [(key231, 2), (key233, 2), (key231, 2), (key503, 2), (key564, 2), (key503, 2), (key625, 2), (key623, 2), (key653, 2), (key623, 2), (key653, 2), (key625, 2), (key231, -2), (key227, -2), (key231, -2), (key503, -2), (key499, -2), (key560, -2), (key499, -2), (key560, -2), (key503, -2), (key623, -2), (key649, -2), (key623, -2)]

def rawRow12985 : Integer.Sparse Key := [(key233, 2), (key231, 2), (key231, 2), (key564, 2), (key503, 2), (key503, 2), (key653, 2), (key653, 2), (key625, 2), (key625, 2), (key623, 2), (key623, 2), (key231, -2), (key231, -2), (key227, -2), (key560, -2), (key560, -2), (key503, -2), (key503, -2), (key499, -2), (key499, -2), (key649, -2), (key623, -2), (key623, -2)]

def rawRow12986 : Integer.Sparse Key := [(key503, 2), (key623, 2), (key625, 2), (key231, 2), (key623, 2), (key653, 2), (key231, 2), (key233, 2), (key503, 2), (key564, 2), (key625, 2), (key653, 2), (key499, -2), (key503, -2), (key623, -2), (key227, -2), (key231, -2), (key499, -2), (key560, -2), (key623, -2), (key649, -2), (key231, -2), (key503, -2), (key560, -2)]

def rawRow12987 : Integer.Sparse Key := [(key503, 2), (key625, 2), (key623, 2), (key231, 2), (key653, 2), (key623, 2), (key233, 2), (key231, 2), (key564, 2), (key503, 2), (key653, 2), (key625, 2), (key503, -2), (key499, -2), (key623, -2), (key231, -2), (key227, -2), (key560, -2), (key499, -2), (key649, -2), (key623, -2), (key231, -2), (key560, -2), (key503, -2)]

def rawRow12988 : Integer.Sparse Key := [(key623, 2), (key503, 2), (key625, 2), (key623, 2), (key231, 2), (key653, 2), (key503, 2), (key625, 2), (key231, 2), (key653, 2), (key233, 2), (key564, 2), (key499, -2), (key623, -2), (key503, -2), (key499, -2), (key623, -2), (key227, -2), (key649, -2), (key231, -2), (key560, -2), (key503, -2), (key231, -2), (key560, -2)]

def rawRow12989 : Integer.Sparse Key := [(key623, 2), (key625, 2), (key503, 2), (key623, 2), (key653, 2), (key231, 2), (key625, 2), (key503, 2), (key653, 2), (key231, 2), (key564, 2), (key233, 2), (key623, -2), (key499, -2), (key503, -2), (key623, -2), (key499, -2), (key649, -2), (key227, -2), (key560, -2), (key231, -2), (key503, -2), (key560, -2), (key231, -2)]

def rawRow12990 : Integer.Sparse Key := [(key625, 2), (key503, 2), (key623, 2), (key653, 2), (key231, 2), (key623, 2), (key564, 2), (key653, 2), (key233, 2), (key625, 2), (key231, 2), (key503, 2), (key503, -2), (key623, -2), (key499, -2), (key560, -2), (key649, -2), (key231, -2), (key623, -2), (key227, -2), (key499, -2), (key560, -2), (key231, -2), (key503, -2)]

def rawRow12991 : Integer.Sparse Key := [(key625, 2), (key623, 2), (key503, 2), (key653, 2), (key623, 2), (key231, 2), (key653, 2), (key564, 2), (key625, 2), (key233, 2), (key503, 2), (key231, 2), (key623, -2), (key503, -2), (key499, -2), (key649, -2), (key560, -2), (key623, -2), (key231, -2), (key499, -2), (key227, -2), (key560, -2), (key503, -2), (key231, -2)]

def rawRow12992 : Integer.Sparse Key := [(key564, 2), (key653, 2), (key653, 2), (key233, 2), (key625, 2), (key625, 2), (key231, 2), (key231, 2), (key503, 2), (key503, 2), (key623, 2), (key623, 2), (key560, -2), (key560, -2), (key649, -2), (key231, -2), (key231, -2), (key503, -2), (key503, -2), (key623, -2), (key623, -2), (key227, -2), (key499, -2), (key499, -2)]

def rawRow12993 : Integer.Sparse Key := [(key653, 2), (key564, 2), (key653, 2), (key625, 2), (key233, 2), (key625, 2), (key503, 2), (key623, 2), (key231, 2), (key623, 2), (key231, 2), (key503, 2), (key560, -2), (key649, -2), (key560, -2), (key503, -2), (key623, -2), (key231, -2), (key623, -2), (key231, -2), (key503, -2), (key499, -2), (key227, -2), (key499, -2)]

def rawRow12994 : Integer.Sparse Key := [(key653, 2), (key653, 2), (key564, 2), (key625, 2), (key625, 2), (key233, 2), (key623, 2), (key503, 2), (key623, 2), (key231, 2), (key503, 2), (key231, 2), (key649, -2), (key560, -2), (key560, -2), (key623, -2), (key503, -2), (key623, -2), (key231, -2), (key503, -2), (key231, -2), (key499, -2), (key499, -2), (key227, -2)]

def rawRow12995 : Integer.Sparse Key := [(key1505, -4), (key1509, -4), (key1509, -4), (key1738, -4), (key1738, -4), (key1745, -4), (key1509, 6), (key1509, 6), (key1517, 6), (key1745, 6)]

def rawRow12996 : Integer.Sparse Key := [(key1509, -4), (key1505, -4), (key1509, -4), (key1738, -4), (key1745, -4), (key1738, -4), (key1509, 6), (key1517, 6), (key1509, 6), (key1745, 6)]

def rawRow12997 : Integer.Sparse Key := [(key1509, -4), (key1509, -4), (key1505, -4), (key1745, -4), (key1738, -4), (key1738, -4), (key1517, 6), (key1509, 6), (key1509, 6), (key1745, 6)]

def rawRow12998 : Integer.Sparse Key := [(key1505, -4), (key1738, -4), (key1738, -4), (key1509, -4), (key1509, -4), (key1745, -4), (key1509, 6), (key1509, 6), (key1745, 6), (key1517, 6)]

def rawRow12999 : Integer.Sparse Key := [(key1738, -4), (key1505, -4), (key1738, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1509, 6), (key1745, 6), (key1509, 6), (key1517, 6)]

def rawRow13000 : Integer.Sparse Key := [(key1738, -4), (key1738, -4), (key1505, -4), (key1745, -4), (key1509, -4), (key1509, -4), (key1745, 6), (key1509, 6), (key1509, 6), (key1517, 6)]

def rawRow13001 : Integer.Sparse Key := [(key1509, -4), (key1738, -4), (key1745, -4), (key1505, -4), (key1509, -4), (key1738, -4), (key1509, 6), (key1517, 6), (key1745, 6), (key1509, 6)]

def rawRow13002 : Integer.Sparse Key := [(key1509, -4), (key1745, -4), (key1738, -4), (key1509, -4), (key1505, -4), (key1738, -4), (key1517, 6), (key1509, 6), (key1745, 6), (key1509, 6)]

def rawRow13003 : Integer.Sparse Key := [(key1738, -4), (key1509, -4), (key1745, -4), (key1505, -4), (key1738, -4), (key1509, -4), (key1509, 6), (key1745, 6), (key1517, 6), (key1509, 6)]

def rawRow13004 : Integer.Sparse Key := [(key1738, -4), (key1745, -4), (key1509, -4), (key1738, -4), (key1505, -4), (key1509, -4), (key1745, 6), (key1509, 6), (key1517, 6), (key1509, 6)]

def rawRow13005 : Integer.Sparse Key := [(key1745, -4), (key1509, -4), (key1738, -4), (key1509, -4), (key1738, -4), (key1505, -4), (key1517, 6), (key1745, 6), (key1509, 6), (key1509, 6)]

def rawRow13006 : Integer.Sparse Key := [(key1745, -4), (key1738, -4), (key1509, -4), (key1738, -4), (key1509, -4), (key1505, -4), (key1745, 6), (key1517, 6), (key1509, 6), (key1509, 6)]

def rawRow13007 : Integer.Sparse Key := [(key1509, -4), (key1509, -4), (key1517, -4), (key1738, -4), (key1745, -4), (key1745, -4), (key1505, 6), (key1509, 6), (key1509, 6), (key1738, 6)]

def rawRow13008 : Integer.Sparse Key := [(key1509, -4), (key1517, -4), (key1509, -4), (key1745, -4), (key1738, -4), (key1745, -4), (key1509, 6), (key1505, 6), (key1509, 6), (key1738, 6)]

def rawRow13009 : Integer.Sparse Key := [(key1517, -4), (key1509, -4), (key1509, -4), (key1745, -4), (key1745, -4), (key1738, -4), (key1509, 6), (key1509, 6), (key1505, 6), (key1738, 6)]

def rawRow13010 : Integer.Sparse Key := [(key1509, -4), (key1738, -4), (key1745, -4), (key1509, -4), (key1517, -4), (key1745, -4), (key1505, 6), (key1509, 6), (key1738, 6), (key1509, 6)]

def rawRow13011 : Integer.Sparse Key := [(key1509, -4), (key1745, -4), (key1738, -4), (key1517, -4), (key1509, -4), (key1745, -4), (key1509, 6), (key1505, 6), (key1738, 6), (key1509, 6)]

def rawRow13012 : Integer.Sparse Key := [(key1738, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1745, -4), (key1517, -4), (key1505, 6), (key1738, 6), (key1509, 6), (key1509, 6)]

def rawRow13013 : Integer.Sparse Key := [(key1738, -4), (key1745, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1517, -4), (key1738, 6), (key1505, 6), (key1509, 6), (key1509, 6)]

def rawRow13014 : Integer.Sparse Key := [(key1745, -4), (key1509, -4), (key1738, -4), (key1517, -4), (key1745, -4), (key1509, -4), (key1509, 6), (key1738, 6), (key1505, 6), (key1509, 6)]

def rawRow13015 : Integer.Sparse Key := [(key1745, -4), (key1738, -4), (key1509, -4), (key1745, -4), (key1517, -4), (key1509, -4), (key1738, 6), (key1509, 6), (key1505, 6), (key1509, 6)]

def rawRow13016 : Integer.Sparse Key := [(key1517, -4), (key1745, -4), (key1745, -4), (key1509, -4), (key1509, -4), (key1738, -4), (key1509, 6), (key1509, 6), (key1738, 6), (key1505, 6)]

def rawRow13017 : Integer.Sparse Key := [(key1745, -4), (key1517, -4), (key1745, -4), (key1509, -4), (key1738, -4), (key1509, -4), (key1509, 6), (key1738, 6), (key1509, 6), (key1505, 6)]

def rawRow13018 : Integer.Sparse Key := [(key1745, -4), (key1745, -4), (key1517, -4), (key1738, -4), (key1509, -4), (key1509, -4), (key1738, 6), (key1509, 6), (key1509, 6), (key1505, 6)]

def rawRow13019 : Integer.Sparse Key := [(key514, 6), (key514, 6), (key519, 6), (key550, 6), (key519, -24)]

def rawRow13020 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key514, 6), (key550, 6), (key519, -24)]

def rawRow13021 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key514, 6), (key550, 6), (key519, -24)]

def rawRow13022 : Integer.Sparse Key := [(key514, 6), (key514, 6), (key550, 6), (key519, 6), (key519, -24)]

def rawRow13023 : Integer.Sparse Key := [(key514, 6), (key550, 6), (key514, 6), (key519, 6), (key519, -24)]

def rawRow13024 : Integer.Sparse Key := [(key550, 6), (key514, 6), (key514, 6), (key519, 6), (key519, -24)]

def rawRow13025 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key550, 6), (key514, 6), (key519, -24)]

def rawRow13026 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key550, 6), (key514, 6), (key519, -24)]

def rawRow13027 : Integer.Sparse Key := [(key514, 6), (key550, 6), (key519, 6), (key514, 6), (key519, -24)]

def rawRow13028 : Integer.Sparse Key := [(key550, 6), (key514, 6), (key519, 6), (key514, 6), (key519, -24)]

def rawRow13029 : Integer.Sparse Key := [(key519, 6), (key550, 6), (key514, 6), (key514, 6), (key519, -24)]

def rawRow13030 : Integer.Sparse Key := [(key550, 6), (key519, 6), (key514, 6), (key514, 6), (key519, -24)]

def rawRow13031 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key519, 6), (key550, 6), (key514, -24)]

def rawRow13032 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key519, 6), (key550, 6), (key514, -24)]

def rawRow13033 : Integer.Sparse Key := [(key519, 6), (key519, 6), (key514, 6), (key550, 6), (key514, -24)]

def rawRow13034 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key550, 6), (key519, 6), (key514, -24)]

def rawRow13035 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key550, 6), (key519, 6), (key514, -24)]

def rawRow13036 : Integer.Sparse Key := [(key514, 6), (key550, 6), (key519, 6), (key519, 6), (key514, -24)]

def rawRow13037 : Integer.Sparse Key := [(key550, 6), (key514, 6), (key519, 6), (key519, 6), (key514, -24)]

def rawRow13038 : Integer.Sparse Key := [(key519, 6), (key550, 6), (key514, 6), (key519, 6), (key514, -24)]

def rawRow13039 : Integer.Sparse Key := [(key550, 6), (key519, 6), (key514, 6), (key519, 6), (key514, -24)]

def rawRow13040 : Integer.Sparse Key := [(key519, 6), (key519, 6), (key550, 6), (key514, 6), (key514, -24)]

def rawRow13041 : Integer.Sparse Key := [(key519, 6), (key550, 6), (key519, 6), (key514, 6), (key514, -24)]

def rawRow13042 : Integer.Sparse Key := [(key550, 6), (key519, 6), (key519, 6), (key514, 6), (key514, -24)]

def rawRow13043 : Integer.Sparse Key := [(key1367, 1), (key1367, 1), (key1376, 1), (key1376, 1), (key1380, 1), (key1380, 1), (key1493, 1), (key1493, 1), (key1515, 1), (key1515, 1), (key1520, 1), (key1520, 1), (key1725, 1), (key1725, 1), (key1743, 1), (key1743, 1), (key1759, 1), (key1759, 1), (key1871, 1), (key1871, 1), (key1881, 1), (key1881, 1), (key1889, 1), (key1889, 1), (key1371, -2), (key1380, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1520, -2), (key1729, -2), (key1729, -2), (key1748, -2), (key1748, -2), (key1759, -2), (key1759, -2)]

def rawRow13044 : Integer.Sparse Key := [(key1376, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, 1), (key1881, 1), (key1380, -2), (key1371, -2), (key1380, -2), (key1520, -2), (key1497, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1729, -2), (key1748, -2)]

def rawRow13045 : Integer.Sparse Key := [(key1380, 1), (key1376, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1367, 1), (key1520, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1493, 1), (key1759, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1725, 1), (key1889, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1881, 1), (key1871, 1), (key1380, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1520, -2), (key1497, -2), (key1759, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1748, -2), (key1729, -2)]

def rawRow13046 : Integer.Sparse Key := [(key1493, 1), (key1493, 1), (key1725, 1), (key1725, 1), (key1871, 1), (key1871, 1), (key1367, 1), (key1367, 1), (key1743, 1), (key1743, 1), (key1881, 1), (key1881, 1), (key1376, 1), (key1376, 1), (key1515, 1), (key1515, 1), (key1889, 1), (key1889, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1), (key1497, -2), (key1729, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1380, -2), (key1380, -2), (key1520, -2), (key1520, -2), (key1759, -2), (key1759, -2)]

def rawRow13047 : Integer.Sparse Key := [(key1725, 1), (key1871, 1), (key1493, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1729, -2), (key1497, -2), (key1729, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1759, -2), (key1380, -2), (key1520, -2)]

def rawRow13048 : Integer.Sparse Key := [(key1871, 1), (key1725, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1493, 1), (key1881, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1367, 1), (key1889, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1376, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1), (key1729, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1759, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1520, -2), (key1380, -2)]

def rawRow13049 : Integer.Sparse Key := [(key1515, 1), (key1520, 1), (key1743, 1), (key1759, 1), (key1881, 1), (key1889, 1), (key1376, 1), (key1380, 1), (key1725, 1), (key1759, 1), (key1871, 1), (key1889, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1367, 1), (key1376, 1), (key1493, 1), (key1515, 1), (key1725, 1), (key1743, 1), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1371, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1729, -2), (key1748, -2)]

def rawRow13050 : Integer.Sparse Key := [(key1520, 1), (key1515, 1), (key1759, 1), (key1743, 1), (key1889, 1), (key1881, 1), (key1380, 1), (key1376, 1), (key1759, 1), (key1725, 1), (key1889, 1), (key1871, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1376, 1), (key1367, 1), (key1515, 1), (key1493, 1), (key1743, 1), (key1725, 1), (key1520, -2), (key1759, -2), (key1748, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1497, -2), (key1748, -2), (key1729, -2)]

def rawRow13051 : Integer.Sparse Key := [(key1743, 1), (key1881, 1), (key1515, 1), (key1889, 1), (key1520, 1), (key1759, 1), (key1725, 1), (key1871, 1), (key1376, 1), (key1889, 1), (key1380, 1), (key1759, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1493, 1), (key1725, 1), (key1367, 1), (key1743, 1), (key1376, 1), (key1515, 1), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1497, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1380, -2), (key1520, -2)]

def rawRow13052 : Integer.Sparse Key := [(key1881, 1), (key1743, 1), (key1889, 1), (key1515, 1), (key1759, 1), (key1520, 1), (key1871, 1), (key1725, 1), (key1889, 1), (key1376, 1), (key1759, 1), (key1380, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1725, 1), (key1493, 1), (key1743, 1), (key1367, 1), (key1515, 1), (key1376, 1), (key1748, -2), (key1759, -2), (key1520, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1371, -2), (key1520, -2), (key1380, -2)]

def rawRow13053 : Integer.Sparse Key := [(key1759, 1), (key1889, 1), (key1520, 1), (key1881, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1889, 1), (key1380, 1), (key1871, 1), (key1376, 1), (key1725, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1376, 1), (key1725, 1), (key1367, 1), (key1493, 1), (key1759, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1520, -2), (key1748, -2), (key1380, -2), (key1729, -2), (key1371, -2), (key1497, -2)]

def rawRow13054 : Integer.Sparse Key := [(key1889, 1), (key1759, 1), (key1881, 1), (key1520, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1759, 1), (key1871, 1), (key1380, 1), (key1725, 1), (key1376, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1725, 1), (key1376, 1), (key1493, 1), (key1367, 1), (key1759, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1748, -2), (key1520, -2), (key1729, -2), (key1380, -2), (key1497, -2), (key1371, -2)]

def rawRow13055 : Integer.Sparse Key := [(key1367, 1), (key1371, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1493, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1719, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1866, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1871, 1), (key1881, 1), (key1367, -2), (key1367, -2), (key1376, -2), (key1493, -2), (key1493, -2), (key1515, -2), (key1719, -2), (key1725, -2), (key1719, -2), (key1743, -2), (key1725, -2), (key1743, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13056 : Integer.Sparse Key := [(key1371, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1871, 1), (key1367, -2), (key1376, -2), (key1367, -2), (key1493, -2), (key1515, -2), (key1493, -2), (key1725, -2), (key1719, -2), (key1743, -2), (key1719, -2), (key1743, -2), (key1725, -2)]

def rawRow13057 : Integer.Sparse Key := [(key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1367, 1), (key1367, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1493, 1), (key1493, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1719, 1), (key1719, 1), (key1881, 1), (key1881, 1), (key1871, 1), (key1871, 1), (key1866, 1), (key1866, 1), (key1376, -2), (key1367, -2), (key1367, -2), (key1515, -2), (key1493, -2), (key1493, -2), (key1743, -2), (key1743, -2), (key1725, -2), (key1725, -2), (key1719, -2), (key1719, -2)]

def rawRow13058 : Integer.Sparse Key := [(key1493, 1), (key1497, 1), (key1719, 1), (key1729, 1), (key1866, 1), (key1871, 1), (key1367, 1), (key1371, 1), (key1719, 1), (key1748, 1), (key1866, 1), (key1881, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1), (key1493, -2), (key1719, -2), (key1725, -2), (key1367, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1376, -2), (key1493, -2), (key1515, -2), (key1725, -2), (key1743, -2)]

def rawRow13059 : Integer.Sparse Key := [(key1497, 1), (key1493, 1), (key1729, 1), (key1719, 1), (key1871, 1), (key1866, 1), (key1371, 1), (key1367, 1), (key1748, 1), (key1719, 1), (key1881, 1), (key1866, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1), (key1493, -2), (key1725, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1719, -2), (key1376, -2), (key1367, -2), (key1515, -2), (key1493, -2), (key1743, -2), (key1725, -2)]

def rawRow13060 : Integer.Sparse Key := [(key1719, 1), (key1866, 1), (key1493, 1), (key1871, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1866, 1), (key1367, 1), (key1881, 1), (key1371, 1), (key1748, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1), (key1719, -2), (key1493, -2), (key1725, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1493, -2), (key1725, -2), (key1367, -2), (key1743, -2), (key1376, -2), (key1515, -2)]

def rawRow13061 : Integer.Sparse Key := [(key1866, 1), (key1719, 1), (key1871, 1), (key1493, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1719, 1), (key1881, 1), (key1367, 1), (key1748, 1), (key1371, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1), (key1719, -2), (key1725, -2), (key1493, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1725, -2), (key1493, -2), (key1743, -2), (key1367, -2), (key1515, -2), (key1376, -2)]

def rawRow13062 : Integer.Sparse Key := [(key1729, 1), (key1871, 1), (key1497, 1), (key1866, 1), (key1493, 1), (key1719, 1), (key1748, 1), (key1881, 1), (key1371, 1), (key1866, 1), (key1367, 1), (key1719, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1), (key1725, -2), (key1493, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1719, -2), (key1515, -2), (key1743, -2), (key1376, -2), (key1725, -2), (key1367, -2), (key1493, -2)]

def rawRow13063 : Integer.Sparse Key := [(key1871, 1), (key1729, 1), (key1866, 1), (key1497, 1), (key1719, 1), (key1493, 1), (key1881, 1), (key1748, 1), (key1866, 1), (key1371, 1), (key1719, 1), (key1367, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1), (key1725, -2), (key1719, -2), (key1493, -2), (key1743, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1515, -2), (key1725, -2), (key1376, -2), (key1493, -2), (key1367, -2)]

def rawRow13064 : Integer.Sparse Key := [(key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1881, 1), (key1881, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1871, 1), (key1871, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1866, 1), (key1866, 1), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1), (key1515, -2), (key1743, -2), (key1743, -2), (key1376, -2), (key1725, -2), (key1725, -2), (key1367, -2), (key1367, -2), (key1493, -2), (key1493, -2), (key1719, -2), (key1719, -2)]

def rawRow13065 : Integer.Sparse Key := [(key1748, 1), (key1881, 1), (key1520, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1743, -2), (key1515, -2), (key1743, -2), (key1725, -2), (key1376, -2), (key1725, -2), (key1493, -2), (key1719, -2), (key1367, -2), (key1719, -2), (key1367, -2), (key1493, -2)]

def rawRow13066 : Integer.Sparse Key := [(key1881, 1), (key1748, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1871, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1866, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1), (key1743, -2), (key1743, -2), (key1515, -2), (key1725, -2), (key1725, -2), (key1376, -2), (key1719, -2), (key1493, -2), (key1719, -2), (key1367, -2), (key1493, -2), (key1367, -2)]

def rawRow13067 : Integer.Sparse Key := [(key1367, -2), (key1367, -2), (key1371, -2), (key1719, -2), (key1719, -2), (key1743, -2), (key1743, -2), (key1748, -2), (key1748, -2), (key1866, -2), (key1881, -2), (key1881, -2), (key1367, 1), (key1367, 1), (key1376, 1), (key1376, 1), (key1380, 1), (key1380, 1), (key1493, 1), (key1493, 1), (key1515, 1), (key1515, 1), (key1520, 1), (key1520, 1), (key1725, 1), (key1725, 1), (key1743, 1), (key1743, 1), (key1759, 1), (key1759, 1), (key1871, 1), (key1871, 1), (key1881, 1), (key1881, 1), (key1889, 1), (key1889, 1)]

def rawRow13068 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1367, -2), (key1743, -2), (key1748, -2), (key1719, -2), (key1748, -2), (key1719, -2), (key1743, -2), (key1881, -2), (key1866, -2), (key1881, -2), (key1376, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, 1), (key1881, 1)]

def rawRow13069 : Integer.Sparse Key := [(key1371, -2), (key1367, -2), (key1367, -2), (key1748, -2), (key1743, -2), (key1748, -2), (key1719, -2), (key1743, -2), (key1719, -2), (key1881, -2), (key1881, -2), (key1866, -2), (key1380, 1), (key1376, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1367, 1), (key1520, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1493, 1), (key1759, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1725, 1), (key1889, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1881, 1), (key1871, 1)]

def rawRow13070 : Integer.Sparse Key := [(key1719, -2), (key1719, -2), (key1866, -2), (key1367, -2), (key1367, -2), (key1743, -2), (key1743, -2), (key1881, -2), (key1881, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1493, 1), (key1493, 1), (key1725, 1), (key1725, 1), (key1871, 1), (key1871, 1), (key1367, 1), (key1367, 1), (key1743, 1), (key1743, 1), (key1881, 1), (key1881, 1), (key1376, 1), (key1376, 1), (key1515, 1), (key1515, 1), (key1889, 1), (key1889, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1)]

def rawRow13071 : Integer.Sparse Key := [(key1719, -2), (key1866, -2), (key1719, -2), (key1743, -2), (key1881, -2), (key1367, -2), (key1881, -2), (key1367, -2), (key1743, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1725, 1), (key1871, 1), (key1493, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1)]

def rawRow13072 : Integer.Sparse Key := [(key1866, -2), (key1719, -2), (key1719, -2), (key1881, -2), (key1743, -2), (key1881, -2), (key1367, -2), (key1743, -2), (key1367, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1871, 1), (key1725, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1493, 1), (key1881, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1367, 1), (key1889, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1376, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1)]

def rawRow13073 : Integer.Sparse Key := [(key1743, -2), (key1748, -2), (key1881, -2), (key1367, -2), (key1371, -2), (key1719, -2), (key1748, -2), (key1866, -2), (key1881, -2), (key1367, -2), (key1719, -2), (key1743, -2), (key1515, 1), (key1520, 1), (key1743, 1), (key1759, 1), (key1881, 1), (key1889, 1), (key1376, 1), (key1380, 1), (key1725, 1), (key1759, 1), (key1871, 1), (key1889, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1367, 1), (key1376, 1), (key1493, 1), (key1515, 1), (key1725, 1), (key1743, 1)]

def rawRow13074 : Integer.Sparse Key := [(key1748, -2), (key1743, -2), (key1881, -2), (key1371, -2), (key1367, -2), (key1748, -2), (key1719, -2), (key1881, -2), (key1866, -2), (key1367, -2), (key1743, -2), (key1719, -2), (key1520, 1), (key1515, 1), (key1759, 1), (key1743, 1), (key1889, 1), (key1881, 1), (key1380, 1), (key1376, 1), (key1759, 1), (key1725, 1), (key1889, 1), (key1871, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1376, 1), (key1367, 1), (key1515, 1), (key1493, 1), (key1743, 1), (key1725, 1)]

def rawRow13075 : Integer.Sparse Key := [(key1743, -2), (key1881, -2), (key1748, -2), (key1719, -2), (key1866, -2), (key1367, -2), (key1881, -2), (key1371, -2), (key1748, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1743, 1), (key1881, 1), (key1515, 1), (key1889, 1), (key1520, 1), (key1759, 1), (key1725, 1), (key1871, 1), (key1376, 1), (key1889, 1), (key1380, 1), (key1759, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1493, 1), (key1725, 1), (key1367, 1), (key1743, 1), (key1376, 1), (key1515, 1)]

def rawRow13076 : Integer.Sparse Key := [(key1881, -2), (key1743, -2), (key1748, -2), (key1866, -2), (key1719, -2), (key1881, -2), (key1367, -2), (key1748, -2), (key1371, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1881, 1), (key1743, 1), (key1889, 1), (key1515, 1), (key1759, 1), (key1520, 1), (key1871, 1), (key1725, 1), (key1889, 1), (key1376, 1), (key1759, 1), (key1380, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1725, 1), (key1493, 1), (key1743, 1), (key1367, 1), (key1515, 1), (key1376, 1)]

def rawRow13077 : Integer.Sparse Key := [(key1748, -2), (key1881, -2), (key1743, -2), (key1748, -2), (key1881, -2), (key1371, -2), (key1866, -2), (key1367, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1719, -2), (key1759, 1), (key1889, 1), (key1520, 1), (key1881, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1889, 1), (key1380, 1), (key1871, 1), (key1376, 1), (key1725, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1376, 1), (key1725, 1), (key1367, 1), (key1493, 1)]

def rawRow13078 : Integer.Sparse Key := [(key1881, -2), (key1748, -2), (key1743, -2), (key1881, -2), (key1748, -2), (key1866, -2), (key1371, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1719, -2), (key1367, -2), (key1889, 1), (key1759, 1), (key1881, 1), (key1520, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1759, 1), (key1871, 1), (key1380, 1), (key1725, 1), (key1376, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1725, 1), (key1376, 1), (key1493, 1), (key1367, 1)]

def rawRow13079 : Integer.Sparse Key := [(key1376, -2), (key1380, -2), (key1380, -2), (key1725, -2), (key1729, -2), (key1725, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1871, -2), (key1871, -2), (key1889, -2), (key1367, 1), (key1371, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1493, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1719, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1866, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1871, 1), (key1881, 1)]

def rawRow13080 : Integer.Sparse Key := [(key1380, -2), (key1376, -2), (key1380, -2), (key1729, -2), (key1725, -2), (key1759, -2), (key1725, -2), (key1759, -2), (key1729, -2), (key1871, -2), (key1889, -2), (key1871, -2), (key1371, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1871, 1)]

def rawRow13081 : Integer.Sparse Key := [(key1380, -2), (key1380, -2), (key1376, -2), (key1759, -2), (key1759, -2), (key1729, -2), (key1729, -2), (key1725, -2), (key1725, -2), (key1889, -2), (key1871, -2), (key1871, -2), (key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1367, 1), (key1367, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1493, 1), (key1493, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1719, 1), (key1719, 1), (key1881, 1), (key1881, 1), (key1871, 1), (key1871, 1), (key1866, 1), (key1866, 1)]

def rawRow13082 : Integer.Sparse Key := [(key1725, -2), (key1729, -2), (key1871, -2), (key1376, -2), (key1380, -2), (key1725, -2), (key1759, -2), (key1871, -2), (key1889, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1493, 1), (key1497, 1), (key1719, 1), (key1729, 1), (key1866, 1), (key1871, 1), (key1367, 1), (key1371, 1), (key1719, 1), (key1748, 1), (key1866, 1), (key1881, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1)]

def rawRow13083 : Integer.Sparse Key := [(key1729, -2), (key1725, -2), (key1871, -2), (key1380, -2), (key1376, -2), (key1759, -2), (key1725, -2), (key1889, -2), (key1871, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1497, 1), (key1493, 1), (key1729, 1), (key1719, 1), (key1871, 1), (key1866, 1), (key1371, 1), (key1367, 1), (key1748, 1), (key1719, 1), (key1881, 1), (key1866, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1)]

def rawRow13084 : Integer.Sparse Key := [(key1725, -2), (key1871, -2), (key1729, -2), (key1725, -2), (key1871, -2), (key1376, -2), (key1889, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1719, 1), (key1866, 1), (key1493, 1), (key1871, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1866, 1), (key1367, 1), (key1881, 1), (key1371, 1), (key1748, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1)]

def rawRow13085 : Integer.Sparse Key := [(key1871, -2), (key1725, -2), (key1729, -2), (key1871, -2), (key1725, -2), (key1889, -2), (key1376, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1866, 1), (key1719, 1), (key1871, 1), (key1493, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1719, 1), (key1881, 1), (key1367, 1), (key1748, 1), (key1371, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1)]

def rawRow13086 : Integer.Sparse Key := [(key1729, -2), (key1871, -2), (key1725, -2), (key1759, -2), (key1889, -2), (key1380, -2), (key1871, -2), (key1376, -2), (key1725, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1729, 1), (key1871, 1), (key1497, 1), (key1866, 1), (key1493, 1), (key1719, 1), (key1748, 1), (key1881, 1), (key1371, 1), (key1866, 1), (key1367, 1), (key1719, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1)]

def rawRow13087 : Integer.Sparse Key := [(key1871, -2), (key1729, -2), (key1725, -2), (key1889, -2), (key1759, -2), (key1871, -2), (key1380, -2), (key1725, -2), (key1376, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1871, 1), (key1729, 1), (key1866, 1), (key1497, 1), (key1719, 1), (key1493, 1), (key1881, 1), (key1748, 1), (key1866, 1), (key1371, 1), (key1719, 1), (key1367, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1)]

def rawRow13088 : Integer.Sparse Key := [(key1759, -2), (key1759, -2), (key1889, -2), (key1380, -2), (key1380, -2), (key1729, -2), (key1729, -2), (key1871, -2), (key1871, -2), (key1376, -2), (key1725, -2), (key1725, -2), (key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1881, 1), (key1881, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1871, 1), (key1871, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1866, 1), (key1866, 1), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1)]

def rawRow13089 : Integer.Sparse Key := [(key1759, -2), (key1889, -2), (key1759, -2), (key1729, -2), (key1871, -2), (key1380, -2), (key1871, -2), (key1380, -2), (key1729, -2), (key1725, -2), (key1376, -2), (key1725, -2), (key1748, 1), (key1881, 1), (key1520, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1)]

def rawRow13090 : Integer.Sparse Key := [(key1889, -2), (key1759, -2), (key1759, -2), (key1871, -2), (key1729, -2), (key1871, -2), (key1380, -2), (key1729, -2), (key1380, -2), (key1725, -2), (key1725, -2), (key1376, -2), (key1881, 1), (key1748, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1871, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1866, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1)]

def rawRow13091 : Integer.Sparse Key := [(key1703, -4), (key1707, -4), (key1707, -4), (key1856, -4), (key1856, -4), (key1858, -4), (key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1887, 2), (key1887, 2), (key1890, 2), (key1890, 2)]

def rawRow13092 : Integer.Sparse Key := [(key1707, -4), (key1703, -4), (key1707, -4), (key1856, -4), (key1858, -4), (key1856, -4), (key1284, 2), (key1280, 2), (key1284, 2), (key1757, 2), (key1703, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1887, 2)]

def rawRow13093 : Integer.Sparse Key := [(key1707, -4), (key1707, -4), (key1703, -4), (key1858, -4), (key1856, -4), (key1856, -4), (key1284, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1703, 2), (key1890, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1887, 2), (key1856, 2)]

def rawRow13094 : Integer.Sparse Key := [(key1703, -4), (key1856, -4), (key1856, -4), (key1707, -4), (key1707, -4), (key1858, -4), (key1703, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1757, 2), (key1757, 2), (key1890, 2), (key1890, 2)]

def rawRow13095 : Integer.Sparse Key := [(key1856, -4), (key1703, -4), (key1856, -4), (key1707, -4), (key1858, -4), (key1707, -4), (key1856, 2), (key1703, 2), (key1856, 2), (key1887, 2), (key1280, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1890, 2), (key1284, 2), (key1757, 2)]

def rawRow13096 : Integer.Sparse Key := [(key1856, -4), (key1856, -4), (key1703, -4), (key1858, -4), (key1707, -4), (key1707, -4), (key1856, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1280, 2), (key1890, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1757, 2), (key1284, 2)]

def rawRow13097 : Integer.Sparse Key := [(key1707, -4), (key1856, -4), (key1858, -4), (key1703, -4), (key1707, -4), (key1856, -4), (key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1856, 2), (key1887, 2)]

def rawRow13098 : Integer.Sparse Key := [(key1707, -4), (key1858, -4), (key1856, -4), (key1707, -4), (key1703, -4), (key1856, -4), (key1757, 2), (key1890, 2), (key1887, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1703, 2), (key1887, 2), (key1856, 2)]

def rawRow13099 : Integer.Sparse Key := [(key1856, -4), (key1707, -4), (key1858, -4), (key1703, -4), (key1856, -4), (key1707, -4), (key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1703, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1284, 2), (key1757, 2)]

def rawRow13100 : Integer.Sparse Key := [(key1856, -4), (key1858, -4), (key1707, -4), (key1856, -4), (key1703, -4), (key1707, -4), (key1887, 2), (key1890, 2), (key1757, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1280, 2), (key1757, 2), (key1284, 2)]

def rawRow13101 : Integer.Sparse Key := [(key1858, -4), (key1707, -4), (key1856, -4), (key1707, -4), (key1856, -4), (key1703, -4), (key1890, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1757, 2), (key1887, 2), (key1284, 2), (key1856, 2), (key1280, 2), (key1703, 2)]

def rawRow13102 : Integer.Sparse Key := [(key1858, -4), (key1856, -4), (key1707, -4), (key1856, -4), (key1707, -4), (key1703, -4), (key1890, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1284, 2), (key1703, 2), (key1280, 2)]

def rawRow13103 : Integer.Sparse Key := [(key1757, -4), (key1757, -4), (key1760, -4), (key1887, -4), (key1890, -4), (key1890, -4), (key1284, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1707, 2), (key1760, 2), (key1856, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1858, 2), (key1890, 2)]

def rawRow13104 : Integer.Sparse Key := [(key1757, -4), (key1760, -4), (key1757, -4), (key1890, -4), (key1887, -4), (key1890, -4), (key1284, 2), (key1286, 2), (key1284, 2), (key1707, 2), (key1760, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1858, 2)]

def rawRow13105 : Integer.Sparse Key := [(key1760, -4), (key1757, -4), (key1757, -4), (key1890, -4), (key1890, -4), (key1887, -4), (key1286, 2), (key1284, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1707, 2), (key1890, 2), (key1890, 2), (key1858, 2), (key1858, 2), (key1856, 2), (key1856, 2)]

def rawRow13106 : Integer.Sparse Key := [(key1757, -4), (key1887, -4), (key1890, -4), (key1757, -4), (key1760, -4), (key1890, -4), (key1707, 2), (key1856, 2), (key1858, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1760, 2), (key1858, 2), (key1890, 2)]

def rawRow13107 : Integer.Sparse Key := [(key1757, -4), (key1890, -4), (key1887, -4), (key1760, -4), (key1757, -4), (key1890, -4), (key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1286, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1890, 2), (key1858, 2)]

def rawRow13108 : Integer.Sparse Key := [(key1887, -4), (key1757, -4), (key1890, -4), (key1757, -4), (key1890, -4), (key1760, -4), (key1856, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1707, 2), (key1858, 2), (key1284, 2), (key1890, 2), (key1286, 2), (key1760, 2)]

def rawRow13109 : Integer.Sparse Key := [(key1887, -4), (key1890, -4), (key1757, -4), (key1890, -4), (key1757, -4), (key1760, -4), (key1856, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1858, 2), (key1707, 2), (key1890, 2), (key1284, 2), (key1760, 2), (key1286, 2)]

def rawRow13110 : Integer.Sparse Key := [(key1890, -4), (key1757, -4), (key1887, -4), (key1760, -4), (key1890, -4), (key1757, -4), (key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1760, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1284, 2), (key1707, 2)]

def rawRow13111 : Integer.Sparse Key := [(key1890, -4), (key1887, -4), (key1757, -4), (key1890, -4), (key1760, -4), (key1757, -4), (key1858, 2), (key1856, 2), (key1707, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1286, 2), (key1707, 2), (key1284, 2)]

def rawRow13112 : Integer.Sparse Key := [(key1760, -4), (key1890, -4), (key1890, -4), (key1757, -4), (key1757, -4), (key1887, -4), (key1760, 2), (key1890, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1858, 2), (key1284, 2), (key1284, 2), (key1707, 2), (key1707, 2), (key1856, 2), (key1856, 2)]

def rawRow13113 : Integer.Sparse Key := [(key1890, -4), (key1760, -4), (key1890, -4), (key1757, -4), (key1887, -4), (key1757, -4), (key1890, 2), (key1760, 2), (key1890, 2), (key1858, 2), (key1286, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1856, 2), (key1284, 2), (key1707, 2)]

def rawRow13114 : Integer.Sparse Key := [(key1890, -4), (key1890, -4), (key1760, -4), (key1887, -4), (key1757, -4), (key1757, -4), (key1890, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1858, 2), (key1286, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1707, 2), (key1284, 2)]

def rawRow13115 : Integer.Sparse Key := [(key524, -24), (key296, 6), (key524, 6), (key555, 6), (key555, 6)]

def rawRow13116 : Integer.Sparse Key := [(key524, -24), (key296, 6), (key555, 6), (key524, 6), (key555, 6)]

def rawRow13117 : Integer.Sparse Key := [(key524, -24), (key296, 6), (key555, 6), (key555, 6), (key524, 6)]

def rawRow13118 : Integer.Sparse Key := [(key524, -24), (key524, 6), (key296, 6), (key555, 6), (key555, 6)]

def rawRow13119 : Integer.Sparse Key := [(key524, -24), (key524, 6), (key555, 6), (key296, 6), (key555, 6)]

def rawRow13120 : Integer.Sparse Key := [(key524, -24), (key524, 6), (key555, 6), (key555, 6), (key296, 6)]

def rawRow13121 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key296, 6), (key524, 6), (key555, 6)]

def rawRow13122 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key296, 6), (key555, 6), (key524, 6)]

def rawRow13123 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key524, 6), (key296, 6), (key555, 6)]

def rawRow13124 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key524, 6), (key555, 6), (key296, 6)]

def rawRow13125 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key555, 6), (key296, 6), (key524, 6)]

def rawRow13126 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key555, 6), (key524, 6), (key296, 6)]

def rawRow13127 : Integer.Sparse Key := [(key555, -24), (key296, 6), (key524, 6), (key524, 6), (key555, 6)]

def rawRow13128 : Integer.Sparse Key := [(key555, -24), (key296, 6), (key524, 6), (key555, 6), (key524, 6)]

def rawRow13129 : Integer.Sparse Key := [(key555, -24), (key296, 6), (key555, 6), (key524, 6), (key524, 6)]

def rawRow13130 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key296, 6), (key524, 6), (key555, 6)]

def rawRow13131 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key296, 6), (key555, 6), (key524, 6)]

def rawRow13132 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key524, 6), (key296, 6), (key555, 6)]

def rawRow13133 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key524, 6), (key555, 6), (key296, 6)]

def rawRow13134 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key555, 6), (key296, 6), (key524, 6)]

def rawRow13135 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key555, 6), (key524, 6), (key296, 6)]

def rawRow13136 : Integer.Sparse Key := [(key555, -24), (key555, 6), (key296, 6), (key524, 6), (key524, 6)]

def rawRow13137 : Integer.Sparse Key := [(key555, -24), (key555, 6), (key524, 6), (key296, 6), (key524, 6)]

def rawRow13138 : Integer.Sparse Key := [(key555, -24), (key555, 6), (key524, 6), (key524, 6), (key296, 6)]

def rawRow13139 : Integer.Sparse Key := [(key1508, 6), (key1508, 6), (key1521, 6), (key1882, 6), (key1510, -6), (key1510, -6), (key1521, -6), (key1749, -6)]

def rawRow13140 : Integer.Sparse Key := [(key1508, 6), (key1521, 6), (key1508, 6), (key1882, 6), (key1510, -6), (key1521, -6), (key1510, -6), (key1749, -6)]

def rawRow13141 : Integer.Sparse Key := [(key1521, 6), (key1508, 6), (key1508, 6), (key1882, 6), (key1521, -6), (key1510, -6), (key1510, -6), (key1749, -6)]

def rawRow13142 : Integer.Sparse Key := [(key1508, 6), (key1508, 6), (key1882, 6), (key1521, 6), (key1510, -6), (key1510, -6), (key1749, -6), (key1521, -6)]

def rawRow13143 : Integer.Sparse Key := [(key1508, 6), (key1882, 6), (key1508, 6), (key1521, 6), (key1510, -6), (key1749, -6), (key1510, -6), (key1521, -6)]

def rawRow13144 : Integer.Sparse Key := [(key1882, 6), (key1508, 6), (key1508, 6), (key1521, 6), (key1749, -6), (key1510, -6), (key1510, -6), (key1521, -6)]

def rawRow13145 : Integer.Sparse Key := [(key1508, 6), (key1521, 6), (key1882, 6), (key1508, 6), (key1510, -6), (key1521, -6), (key1749, -6), (key1510, -6)]

def rawRow13146 : Integer.Sparse Key := [(key1521, 6), (key1508, 6), (key1882, 6), (key1508, 6), (key1521, -6), (key1510, -6), (key1749, -6), (key1510, -6)]

def rawRow13147 : Integer.Sparse Key := [(key1508, 6), (key1882, 6), (key1521, 6), (key1508, 6), (key1510, -6), (key1749, -6), (key1521, -6), (key1510, -6)]

def rawRow13148 : Integer.Sparse Key := [(key1882, 6), (key1508, 6), (key1521, 6), (key1508, 6), (key1749, -6), (key1510, -6), (key1521, -6), (key1510, -6)]

def rawRow13149 : Integer.Sparse Key := [(key1521, 6), (key1882, 6), (key1508, 6), (key1508, 6), (key1521, -6), (key1749, -6), (key1510, -6), (key1510, -6)]

def rawRow13150 : Integer.Sparse Key := [(key1882, 6), (key1521, 6), (key1508, 6), (key1508, 6), (key1749, -6), (key1521, -6), (key1510, -6), (key1510, -6)]

def rawRow13151 : Integer.Sparse Key := [(key1504, 6), (key1510, 6), (key1510, 6), (key1876, 6), (key1504, -6), (key1508, -6), (key1508, -6), (key1737, -6)]

def rawRow13152 : Integer.Sparse Key := [(key1510, 6), (key1504, 6), (key1510, 6), (key1876, 6), (key1508, -6), (key1504, -6), (key1508, -6), (key1737, -6)]

def rawRow13153 : Integer.Sparse Key := [(key1510, 6), (key1510, 6), (key1504, 6), (key1876, 6), (key1508, -6), (key1508, -6), (key1504, -6), (key1737, -6)]

def rawRow13154 : Integer.Sparse Key := [(key1504, 6), (key1510, 6), (key1876, 6), (key1510, 6), (key1504, -6), (key1508, -6), (key1737, -6), (key1508, -6)]

def rawRow13155 : Integer.Sparse Key := [(key1510, 6), (key1504, 6), (key1876, 6), (key1510, 6), (key1508, -6), (key1504, -6), (key1737, -6), (key1508, -6)]

def rawRow13156 : Integer.Sparse Key := [(key1504, 6), (key1876, 6), (key1510, 6), (key1510, 6), (key1504, -6), (key1737, -6), (key1508, -6), (key1508, -6)]

def rawRow13157 : Integer.Sparse Key := [(key1876, 6), (key1504, 6), (key1510, 6), (key1510, 6), (key1737, -6), (key1504, -6), (key1508, -6), (key1508, -6)]

def rawRow13158 : Integer.Sparse Key := [(key1510, 6), (key1876, 6), (key1504, 6), (key1510, 6), (key1508, -6), (key1737, -6), (key1504, -6), (key1508, -6)]

def rawRow13159 : Integer.Sparse Key := [(key1876, 6), (key1510, 6), (key1504, 6), (key1510, 6), (key1737, -6), (key1508, -6), (key1504, -6), (key1508, -6)]

def rawRow13160 : Integer.Sparse Key := [(key1510, 6), (key1510, 6), (key1876, 6), (key1504, 6), (key1508, -6), (key1508, -6), (key1737, -6), (key1504, -6)]

def rawRow13161 : Integer.Sparse Key := [(key1510, 6), (key1876, 6), (key1510, 6), (key1504, 6), (key1508, -6), (key1737, -6), (key1508, -6), (key1504, -6)]

def rawRow13162 : Integer.Sparse Key := [(key1876, 6), (key1510, 6), (key1510, 6), (key1504, 6), (key1737, -6), (key1508, -6), (key1508, -6), (key1504, -6)]

def rawRow13163 : Integer.Sparse Key := [(key291, 2), (key294, 2), (key294, 2), (key518, 2), (key553, 2), (key553, 2), (key631, 2), (key631, 2), (key647, 2), (key647, 2), (key650, 2), (key650, 2), (key294, -2), (key294, -2), (key298, -2), (key522, -2), (key522, -2), (key553, -2), (key553, -2), (key561, -2), (key561, -2), (key632, -2), (key650, -2), (key650, -2)]

def rawRow13164 : Integer.Sparse Key := [(key294, 2), (key291, 2), (key294, 2), (key553, 2), (key518, 2), (key553, 2), (key647, 2), (key650, 2), (key631, 2), (key650, 2), (key631, 2), (key647, 2), (key294, -2), (key298, -2), (key294, -2), (key553, -2), (key561, -2), (key522, -2), (key561, -2), (key522, -2), (key553, -2), (key650, -2), (key632, -2), (key650, -2)]

def rawRow13165 : Integer.Sparse Key := [(key294, 2), (key294, 2), (key291, 2), (key553, 2), (key553, 2), (key518, 2), (key650, 2), (key647, 2), (key650, 2), (key631, 2), (key647, 2), (key631, 2), (key298, -2), (key294, -2), (key294, -2), (key561, -2), (key553, -2), (key561, -2), (key522, -2), (key553, -2), (key522, -2), (key650, -2), (key650, -2), (key632, -2)]

def rawRow13166 : Integer.Sparse Key := [(key518, 2), (key553, 2), (key553, 2), (key291, 2), (key647, 2), (key647, 2), (key294, 2), (key294, 2), (key553, 2), (key553, 2), (key650, 2), (key650, 2), (key522, -2), (key522, -2), (key632, -2), (key294, -2), (key294, -2), (key553, -2), (key553, -2), (key650, -2), (key650, -2), (key298, -2), (key561, -2), (key561, -2)]

def rawRow13167 : Integer.Sparse Key := [(key553, 2), (key518, 2), (key553, 2), (key647, 2), (key291, 2), (key647, 2), (key553, 2), (key650, 2), (key294, 2), (key650, 2), (key294, 2), (key553, 2), (key522, -2), (key632, -2), (key522, -2), (key553, -2), (key650, -2), (key294, -2), (key650, -2), (key294, -2), (key553, -2), (key561, -2), (key298, -2), (key561, -2)]

def rawRow13168 : Integer.Sparse Key := [(key553, 2), (key553, 2), (key518, 2), (key647, 2), (key647, 2), (key291, 2), (key650, 2), (key553, 2), (key650, 2), (key294, 2), (key553, 2), (key294, 2), (key632, -2), (key522, -2), (key522, -2), (key650, -2), (key553, -2), (key650, -2), (key294, -2), (key553, -2), (key294, -2), (key561, -2), (key561, -2), (key298, -2)]

def rawRow13169 : Integer.Sparse Key := [(key631, 2), (key647, 2), (key650, 2), (key294, 2), (key553, 2), (key650, 2), (key291, 2), (key294, 2), (key518, 2), (key553, 2), (key631, 2), (key647, 2), (key553, -2), (key561, -2), (key650, -2), (key294, -2), (key298, -2), (key522, -2), (key561, -2), (key632, -2), (key650, -2), (key294, -2), (key522, -2), (key553, -2)]

def rawRow13170 : Integer.Sparse Key := [(key631, 2), (key650, 2), (key647, 2), (key294, 2), (key650, 2), (key553, 2), (key294, 2), (key291, 2), (key553, 2), (key518, 2), (key647, 2), (key631, 2), (key561, -2), (key553, -2), (key650, -2), (key298, -2), (key294, -2), (key561, -2), (key522, -2), (key650, -2), (key632, -2), (key294, -2), (key553, -2), (key522, -2)]

def rawRow13171 : Integer.Sparse Key := [(key647, 2), (key631, 2), (key650, 2), (key553, 2), (key294, 2), (key650, 2), (key518, 2), (key553, 2), (key291, 2), (key647, 2), (key294, 2), (key553, 2), (key553, -2), (key650, -2), (key561, -2), (key522, -2), (key632, -2), (key294, -2), (key650, -2), (key298, -2), (key561, -2), (key522, -2), (key294, -2), (key553, -2)]

def rawRow13172 : Integer.Sparse Key := [(key647, 2), (key650, 2), (key631, 2), (key553, 2), (key650, 2), (key294, 2), (key553, 2), (key518, 2), (key647, 2), (key291, 2), (key553, 2), (key294, 2), (key650, -2), (key553, -2), (key561, -2), (key632, -2), (key522, -2), (key650, -2), (key294, -2), (key561, -2), (key298, -2), (key522, -2), (key553, -2), (key294, -2)]

def rawRow13173 : Integer.Sparse Key := [(key650, 2), (key631, 2), (key647, 2), (key650, 2), (key294, 2), (key553, 2), (key631, 2), (key647, 2), (key294, 2), (key553, 2), (key291, 2), (key518, 2), (key561, -2), (key650, -2), (key553, -2), (key561, -2), (key650, -2), (key298, -2), (key632, -2), (key294, -2), (key522, -2), (key553, -2), (key294, -2), (key522, -2)]

def rawRow13174 : Integer.Sparse Key := [(key650, 2), (key647, 2), (key631, 2), (key650, 2), (key553, 2), (key294, 2), (key647, 2), (key631, 2), (key553, 2), (key294, 2), (key518, 2), (key291, 2), (key650, -2), (key561, -2), (key553, -2), (key650, -2), (key561, -2), (key632, -2), (key298, -2), (key522, -2), (key294, -2), (key553, -2), (key522, -2), (key294, -2)]

def rawRow13175 : Integer.Sparse Key := [(key294, 2), (key294, 2), (key298, 2), (key522, 2), (key522, 2), (key632, 2), (key553, 2), (key561, 2), (key553, 2), (key650, 2), (key561, 2), (key650, 2), (key291, -2), (key294, -2), (key294, -2), (key518, -2), (key522, -2), (key518, -2), (key553, -2), (key522, -2), (key553, -2), (key631, -2), (key631, -2), (key647, -2)]

def rawRow13176 : Integer.Sparse Key := [(key294, 2), (key298, 2), (key294, 2), (key522, 2), (key632, 2), (key522, 2), (key561, 2), (key553, 2), (key650, 2), (key553, 2), (key650, 2), (key561, 2), (key294, -2), (key291, -2), (key294, -2), (key522, -2), (key518, -2), (key553, -2), (key518, -2), (key553, -2), (key522, -2), (key631, -2), (key647, -2), (key631, -2)]

def rawRow13177 : Integer.Sparse Key := [(key298, 2), (key294, 2), (key294, 2), (key632, 2), (key522, 2), (key522, 2), (key650, 2), (key650, 2), (key561, 2), (key561, 2), (key553, 2), (key553, 2), (key294, -2), (key294, -2), (key291, -2), (key553, -2), (key553, -2), (key522, -2), (key522, -2), (key518, -2), (key518, -2), (key647, -2), (key631, -2), (key631, -2)]

def rawRow13178 : Integer.Sparse Key := [(key522, 2), (key553, 2), (key561, 2), (key294, 2), (key553, 2), (key650, 2), (key294, 2), (key298, 2), (key522, 2), (key632, 2), (key561, 2), (key650, 2), (key518, -2), (key522, -2), (key553, -2), (key291, -2), (key294, -2), (key518, -2), (key553, -2), (key631, -2), (key647, -2), (key294, -2), (key522, -2), (key553, -2)]

def rawRow13179 : Integer.Sparse Key := [(key522, 2), (key561, 2), (key553, 2), (key294, 2), (key650, 2), (key553, 2), (key298, 2), (key294, 2), (key632, 2), (key522, 2), (key650, 2), (key561, 2), (key522, -2), (key518, -2), (key553, -2), (key294, -2), (key291, -2), (key553, -2), (key518, -2), (key647, -2), (key631, -2), (key294, -2), (key553, -2), (key522, -2)]

def rawRow13180 : Integer.Sparse Key := [(key553, 2), (key522, 2), (key561, 2), (key553, 2), (key294, 2), (key650, 2), (key522, 2), (key561, 2), (key294, 2), (key650, 2), (key298, 2), (key632, 2), (key518, -2), (key553, -2), (key522, -2), (key518, -2), (key553, -2), (key291, -2), (key647, -2), (key294, -2), (key553, -2), (key522, -2), (key294, -2), (key553, -2)]

def rawRow13181 : Integer.Sparse Key := [(key553, 2), (key561, 2), (key522, 2), (key553, 2), (key650, 2), (key294, 2), (key561, 2), (key522, 2), (key650, 2), (key294, 2), (key632, 2), (key298, 2), (key553, -2), (key518, -2), (key522, -2), (key553, -2), (key518, -2), (key647, -2), (key291, -2), (key553, -2), (key294, -2), (key522, -2), (key553, -2), (key294, -2)]

def rawRow13182 : Integer.Sparse Key := [(key561, 2), (key522, 2), (key553, 2), (key650, 2), (key294, 2), (key553, 2), (key632, 2), (key650, 2), (key298, 2), (key561, 2), (key294, 2), (key522, 2), (key522, -2), (key553, -2), (key518, -2), (key631, -2), (key647, -2), (key294, -2), (key553, -2), (key291, -2), (key518, -2), (key553, -2), (key294, -2), (key522, -2)]

def rawRow13183 : Integer.Sparse Key := [(key561, 2), (key553, 2), (key522, 2), (key650, 2), (key553, 2), (key294, 2), (key650, 2), (key632, 2), (key561, 2), (key298, 2), (key522, 2), (key294, 2), (key553, -2), (key522, -2), (key518, -2), (key647, -2), (key631, -2), (key553, -2), (key294, -2), (key518, -2), (key291, -2), (key553, -2), (key522, -2), (key294, -2)]

end MUB6.Certificate.GramRows

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

def rawRow13184 : Integer.Sparse Key := [(key632, 2), (key650, 2), (key650, 2), (key298, 2), (key561, 2), (key561, 2), (key294, 2), (key294, 2), (key522, 2), (key522, 2), (key553, 2), (key553, 2), (key631, -2), (key631, -2), (key647, -2), (key294, -2), (key294, -2), (key522, -2), (key522, -2), (key553, -2), (key553, -2), (key291, -2), (key518, -2), (key518, -2)]

def rawRow13185 : Integer.Sparse Key := [(key650, 2), (key632, 2), (key650, 2), (key561, 2), (key298, 2), (key561, 2), (key522, 2), (key553, 2), (key294, 2), (key553, 2), (key294, 2), (key522, 2), (key631, -2), (key647, -2), (key631, -2), (key522, -2), (key553, -2), (key294, -2), (key553, -2), (key294, -2), (key522, -2), (key518, -2), (key291, -2), (key518, -2)]

def rawRow13186 : Integer.Sparse Key := [(key650, 2), (key650, 2), (key632, 2), (key561, 2), (key561, 2), (key298, 2), (key553, 2), (key522, 2), (key553, 2), (key294, 2), (key522, 2), (key294, 2), (key647, -2), (key631, -2), (key631, -2), (key553, -2), (key522, -2), (key553, -2), (key294, -2), (key522, -2), (key294, -2), (key518, -2), (key518, -2), (key291, -2)]

def rawRow13187 : Integer.Sparse Key := [(key2362, 4), (key2562, 4), (key2562, 4), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2367, 4), (key2525, 4), (key2525, 4)]

def rawRow13188 : Integer.Sparse Key := [(key2562, 4), (key2362, 4), (key2562, 4), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2525, 4), (key2367, 4), (key2525, 4)]

def rawRow13189 : Integer.Sparse Key := [(key2562, 4), (key2562, 4), (key2362, 4), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2525, 4), (key2525, 4), (key2367, 4)]

def rawRow13190 : Integer.Sparse Key := [(key2365, 4), (key2521, 4), (key2564, 4), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow13191 : Integer.Sparse Key := [(key2365, 4), (key2564, 4), (key2521, 4), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2367, -2), (key2365, -2), (key2525, -2), (key2460, -2), (key2564, -2), (key2533, -2), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow13192 : Integer.Sparse Key := [(key2521, 4), (key2365, 4), (key2564, 4), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow13193 : Integer.Sparse Key := [(key2521, 4), (key2564, 4), (key2365, 4), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2525, -2), (key2367, -2), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow13194 : Integer.Sparse Key := [(key2564, 4), (key2365, 4), (key2521, 4), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2525, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2365, -2), (key2460, -2), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow13195 : Integer.Sparse Key := [(key2564, 4), (key2521, 4), (key2365, 4), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2564, -2), (key2525, -2), (key2533, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow13196 : Integer.Sparse Key := [(key2365, 4), (key2521, 4), (key2564, 4), (key2365, -2), (key2367, -2), (key2460, -2), (key2533, -2), (key2525, -2), (key2564, -2), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow13197 : Integer.Sparse Key := [(key2365, 4), (key2564, 4), (key2521, 4), (key2367, -2), (key2365, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2525, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow13198 : Integer.Sparse Key := [(key2521, 4), (key2365, 4), (key2564, 4), (key2460, -2), (key2525, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow13199 : Integer.Sparse Key := [(key2521, 4), (key2564, 4), (key2365, 4), (key2525, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2533, -2), (key2367, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow13200 : Integer.Sparse Key := [(key2564, 4), (key2365, 4), (key2521, 4), (key2533, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2365, -2), (key2460, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow13201 : Integer.Sparse Key := [(key2564, 4), (key2521, 4), (key2365, 4), (key2564, -2), (key2533, -2), (key2525, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow13202 : Integer.Sparse Key := [(key2367, 4), (key2525, 4), (key2525, 4), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2362, 4), (key2457, 4), (key2457, 4)]

def rawRow13203 : Integer.Sparse Key := [(key2525, 4), (key2367, 4), (key2525, 4), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2457, 4), (key2362, 4), (key2457, 4)]

def rawRow13204 : Integer.Sparse Key := [(key2525, 4), (key2525, 4), (key2367, 4), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2457, 4), (key2457, 4), (key2362, 4)]

def rawRow13205 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1169, 4), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1183, 4), (key1183, 4), (key1220, 4)]

def rawRow13206 : Integer.Sparse Key := [(key1090, 4), (key1169, 4), (key1090, 4), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, 4), (key1220, 4), (key1183, 4)]

def rawRow13207 : Integer.Sparse Key := [(key1169, 4), (key1090, 4), (key1090, 4), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1220, 4), (key1183, 4), (key1183, 4)]

def rawRow13208 : Integer.Sparse Key := [(key1098, 4), (key1098, 4), (key1098, 4), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

def rawRow13209 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1169, 4), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1183, 4), (key1183, 4), (key1220, 4)]

def rawRow13210 : Integer.Sparse Key := [(key1090, 4), (key1169, 4), (key1090, 4), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, 4), (key1220, 4), (key1183, 4)]

def rawRow13211 : Integer.Sparse Key := [(key1169, 4), (key1090, 4), (key1090, 4), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, 4), (key1183, 4), (key1183, 4)]

def rawRow13212 : Integer.Sparse Key := [(key976, 4), (key1180, 4), (key1220, 4), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key984, 4), (key1098, 4), (key1169, 4)]

def rawRow13213 : Integer.Sparse Key := [(key976, 4), (key1220, 4), (key1180, 4), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, 4), (key1169, 4), (key1098, 4)]

def rawRow13214 : Integer.Sparse Key := [(key1180, 4), (key976, 4), (key1220, 4), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1098, 4), (key984, 4), (key1169, 4)]

def rawRow13215 : Integer.Sparse Key := [(key1180, 4), (key1220, 4), (key976, 4), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1098, 4), (key1169, 4), (key984, 4)]

def rawRow13216 : Integer.Sparse Key := [(key1220, 4), (key976, 4), (key1180, 4), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, 4), (key984, 4), (key1098, 4)]

def rawRow13217 : Integer.Sparse Key := [(key1220, 4), (key1180, 4), (key976, 4), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1169, 4), (key1098, 4), (key984, 4)]

def rawRow13218 : Integer.Sparse Key := [(key984, 4), (key1183, 4), (key1183, 4), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, 4), (key1090, 4), (key1090, 4)]

def rawRow13219 : Integer.Sparse Key := [(key1183, 4), (key984, 4), (key1183, 4), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, 4), (key976, 4), (key1090, 4)]

def rawRow13220 : Integer.Sparse Key := [(key1183, 4), (key1183, 4), (key984, 4), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1090, 4), (key1090, 4), (key976, 4)]

def rawRow13221 : Integer.Sparse Key := [(key1098, 4), (key1098, 4), (key1098, 4), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

def rawRow13222 : Integer.Sparse Key := [(key984, 4), (key1183, 4), (key1183, 4), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key976, 4), (key1090, 4), (key1090, 4)]

def rawRow13223 : Integer.Sparse Key := [(key1183, 4), (key984, 4), (key1183, 4), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, 4), (key976, 4), (key1090, 4)]

def rawRow13224 : Integer.Sparse Key := [(key1183, 4), (key1183, 4), (key984, 4), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1090, 4), (key1090, 4), (key976, 4)]

def rawRow13225 : Integer.Sparse Key := [(key1, -2), (key7, -2), (key7, -2), (key7, 6), (key84, -2), (key90, -2), (key90, -2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key90, -2), (key90, -2), (key151, -2), (key193, 6), (key193, -2), (key193, -2), (key202, -2)]

def rawRow13226 : Integer.Sparse Key := [(key7, -2), (key1, -2), (key7, -2), (key7, 6), (key90, -2), (key84, -2), (key90, -2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key90, -2), (key151, -2), (key90, -2), (key193, 6), (key193, -2), (key202, -2), (key193, -2)]

def rawRow13227 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key1, -2), (key7, 6), (key90, -2), (key90, -2), (key84, -2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key151, -2), (key90, -2), (key90, -2), (key193, 6), (key202, -2), (key193, -2), (key193, -2)]

def rawRow13228 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key7, -2), (key1, 6), (key151, -2), (key151, -2), (key151, -2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key84, -2), (key84, -2), (key84, -2), (key202, 6), (key193, -2), (key193, -2), (key193, -2)]

def rawRow13229 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key90, -2), (key151, 6), (key1, -2), (key7, -2), (key7, -2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key193, -2), (key193, -2), (key202, -2), (key7, 6), (key90, -2), (key90, -2), (key151, -2)]

def rawRow13230 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key90, -2), (key151, 6), (key7, -2), (key1, -2), (key7, -2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key193, -2), (key202, -2), (key193, -2), (key7, 6), (key90, -2), (key151, -2), (key90, -2)]

def rawRow13231 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key84, -2), (key151, 6), (key7, -2), (key7, -2), (key1, -2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key202, -2), (key193, -2), (key193, -2), (key7, 6), (key151, -2), (key90, -2), (key90, -2)]

def rawRow13232 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key151, -2), (key90, 6), (key84, -2), (key90, -2), (key151, -2), (key1, 2), (key7, 2), (key84, 2), (key151, 2), (key193, 2), (key202, 2), (key7, -2), (key90, -2), (key151, -2), (key90, 6), (key7, -2), (key90, -2), (key151, -2)]

def rawRow13233 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key151, -2), (key90, 6), (key90, -2), (key84, -2), (key151, -2), (key7, 2), (key1, 2), (key151, 2), (key84, 2), (key202, 2), (key193, 2), (key7, -2), (key151, -2), (key90, -2), (key90, 6), (key7, -2), (key151, -2), (key90, -2)]

def rawRow13234 : Integer.Sparse Key := [(key84, -2), (key151, -2), (key90, -2), (key90, 6), (key84, -2), (key151, -2), (key90, -2), (key84, 2), (key151, 2), (key1, 2), (key202, 2), (key7, 2), (key151, 2), (key90, -2), (key7, -2), (key151, -2), (key90, 6), (key90, -2), (key7, -2), (key151, -2)]

def rawRow13235 : Integer.Sparse Key := [(key151, -2), (key84, -2), (key90, -2), (key90, 6), (key151, -2), (key84, -2), (key90, -2), (key151, 2), (key84, 2), (key202, 2), (key1, 2), (key151, 2), (key7, 2), (key90, -2), (key151, -2), (key7, -2), (key90, 6), (key90, -2), (key151, -2), (key7, -2)]

def rawRow13236 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key84, -2), (key90, 6), (key90, -2), (key151, -2), (key84, -2), (key193, 2), (key202, 2), (key7, 2), (key151, 2), (key1, 2), (key84, 2), (key151, -2), (key7, -2), (key90, -2), (key90, 6), (key151, -2), (key7, -2), (key90, -2)]

def rawRow13237 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key84, -2), (key90, 6), (key151, -2), (key90, -2), (key84, -2), (key202, 2), (key193, 2), (key151, 2), (key7, 2), (key84, 2), (key1, 2), (key151, -2), (key90, -2), (key7, -2), (key90, 6), (key151, -2), (key90, -2), (key7, -2)]

def rawRow13238 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key151, -2), (key84, 6), (key193, -2), (key193, -2), (key202, -2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key1, -2), (key84, -2), (key84, -2), (key151, 6), (key7, -2), (key90, -2), (key90, -2)]

def rawRow13239 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key90, -2), (key84, 6), (key193, -2), (key202, -2), (key193, -2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key84, -2), (key1, -2), (key84, -2), (key151, 6), (key90, -2), (key7, -2), (key90, -2)]

def rawRow13240 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key90, -2), (key84, 6), (key202, -2), (key193, -2), (key193, -2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key84, -2), (key84, -2), (key1, -2), (key151, 6), (key90, -2), (key90, -2), (key7, -2)]

def rawRow13241 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key193, -2), (key202, 6), (key7, -2), (key7, -2), (key7, -2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key151, -2), (key151, -2), (key151, -2), (key1, 6), (key84, -2), (key84, -2), (key84, -2)]

def rawRow13242 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key202, -2), (key193, 6), (key90, -2), (key90, -2), (key151, -2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key7, -2), (key90, -2), (key90, -2), (key84, 6), (key1, -2), (key84, -2), (key84, -2)]

def rawRow13243 : Integer.Sparse Key := [(key193, -2), (key202, -2), (key193, -2), (key193, 6), (key90, -2), (key151, -2), (key90, -2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key90, -2), (key7, -2), (key90, -2), (key84, 6), (key84, -2), (key1, -2), (key84, -2)]

def rawRow13244 : Integer.Sparse Key := [(key202, -2), (key193, -2), (key193, -2), (key193, 6), (key151, -2), (key90, -2), (key90, -2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key90, -2), (key90, -2), (key7, -2), (key84, 6), (key84, -2), (key84, -2), (key1, -2)]

def rawRow13245 : Integer.Sparse Key := [(key2452, 4), (key2452, 4), (key2519, 4), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2530, 4), (key2530, 4), (key2560, 4)]

def rawRow13246 : Integer.Sparse Key := [(key2452, 4), (key2519, 4), (key2452, 4), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, 4), (key2560, 4), (key2530, 4)]

def rawRow13247 : Integer.Sparse Key := [(key2519, 4), (key2452, 4), (key2452, 4), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2560, 4), (key2530, 4), (key2530, 4)]

def rawRow13248 : Integer.Sparse Key := [(key2458, 4), (key2458, 4), (key2458, 4), (key2452, -2), (key2452, -2), (key2452, -2), (key2452, -2), (key2452, -2), (key2452, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2528, 4), (key2528, 4), (key2528, 4)]

def rawRow13249 : Integer.Sparse Key := [(key2452, 4), (key2452, 4), (key2519, 4), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2530, 4), (key2530, 4), (key2560, 4)]

def rawRow13250 : Integer.Sparse Key := [(key2452, 4), (key2519, 4), (key2452, 4), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, 4), (key2560, 4), (key2530, 4)]

def rawRow13251 : Integer.Sparse Key := [(key2519, 4), (key2452, 4), (key2452, 4), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, 4), (key2530, 4), (key2530, 4)]

def rawRow13252 : Integer.Sparse Key := [(key2357, 4), (key2528, 4), (key2560, 4), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2363, 4), (key2458, 4), (key2519, 4)]

def rawRow13253 : Integer.Sparse Key := [(key2361, 4), (key2560, 4), (key2528, 4), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, 4), (key2519, 4), (key2458, 4)]

def rawRow13254 : Integer.Sparse Key := [(key2517, 4), (key2357, 4), (key2560, 4), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2458, 4), (key2363, 4), (key2519, 4)]

def rawRow13255 : Integer.Sparse Key := [(key2517, 4), (key2560, 4), (key2357, 4), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2458, 4), (key2519, 4), (key2363, 4)]

def rawRow13256 : Integer.Sparse Key := [(key2579, 4), (key2361, 4), (key2517, 4), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, 4), (key2363, 4), (key2458, 4)]

def rawRow13257 : Integer.Sparse Key := [(key2579, 4), (key2517, 4), (key2361, 4), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2519, 4), (key2458, 4), (key2363, 4)]

def rawRow13258 : Integer.Sparse Key := [(key2366, 4), (key2523, 4), (key2523, 4), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2363, -2), (key2363, -2), (key2458, -2), (key2458, -2), (key2530, -2), (key2530, -2), (key2357, 4), (key2452, 4), (key2452, 4)]

def rawRow13259 : Integer.Sparse Key := [(key2523, 4), (key2366, 4), (key2523, 4), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2452, 4), (key2357, 4), (key2452, 4)]

def rawRow13260 : Integer.Sparse Key := [(key2523, 4), (key2523, 4), (key2366, 4), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2530, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2363, -2), (key2452, 4), (key2452, 4), (key2357, 4)]

def rawRow13261 : Integer.Sparse Key := [(key2461, 4), (key2461, 4), (key2461, 4), (key2523, -2), (key2523, -2), (key2523, -2), (key2523, -2), (key2523, -2), (key2523, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow13262 : Integer.Sparse Key := [(key2366, 4), (key2523, 4), (key2523, 4), (key2366, -2), (key2366, -2), (key2461, -2), (key2461, -2), (key2523, -2), (key2523, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow13263 : Integer.Sparse Key := [(key2523, 4), (key2366, 4), (key2523, 4), (key2461, -2), (key2523, -2), (key2366, -2), (key2523, -2), (key2366, -2), (key2461, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow13264 : Integer.Sparse Key := [(key2523, 4), (key2523, 4), (key2366, 4), (key2523, -2), (key2461, -2), (key2523, -2), (key2366, -2), (key2461, -2), (key2366, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow13265 : Integer.Sparse Key := [(key971, -2), (key979, -2), (key979, -2), (key979, 6), (key1085, -2), (key1093, -2), (key1093, -2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1093, -2), (key1093, -2), (key1228, -2), (key1164, 6), (key1164, -2), (key1164, -2), (key1245, -2)]

def rawRow13266 : Integer.Sparse Key := [(key979, -2), (key971, -2), (key979, -2), (key979, 6), (key1093, -2), (key1085, -2), (key1093, -2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, -2), (key1228, -2), (key1093, -2), (key1164, 6), (key1164, -2), (key1245, -2), (key1164, -2)]

def rawRow13267 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key971, -2), (key979, 6), (key1093, -2), (key1093, -2), (key1085, -2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1228, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key1245, -2), (key1164, -2), (key1164, -2)]

def rawRow13268 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key979, -2), (key971, 6), (key1228, -2), (key1228, -2), (key1228, -2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1245, 6), (key1164, -2), (key1164, -2), (key1164, -2)]

def rawRow13269 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key971, -2), (key979, -2), (key979, -2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1164, -2), (key1164, -2), (key1245, -2), (key979, 6), (key1093, -2), (key1093, -2), (key1228, -2)]

def rawRow13270 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1093, -2), (key1164, 6), (key979, -2), (key971, -2), (key979, -2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1164, -2), (key1245, -2), (key1164, -2), (key979, 6), (key1093, -2), (key1228, -2), (key1093, -2)]

def rawRow13271 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1085, -2), (key1164, 6), (key979, -2), (key979, -2), (key971, -2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1245, -2), (key1164, -2), (key1164, -2), (key979, 6), (key1228, -2), (key1093, -2), (key1093, -2)]

def rawRow13272 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1164, -2), (key1093, 6), (key1085, -2), (key1093, -2), (key1164, -2), (key971, 2), (key979, 2), (key1085, 2), (key1228, 2), (key1164, 2), (key1245, 2), (key979, -2), (key1093, -2), (key1228, -2), (key1093, 6), (key979, -2), (key1093, -2), (key1228, -2)]

def rawRow13273 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1164, -2), (key1093, 6), (key1093, -2), (key1085, -2), (key1164, -2), (key979, 2), (key971, 2), (key1228, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key979, -2), (key1228, -2), (key1093, -2), (key1093, 6), (key979, -2), (key1228, -2), (key1093, -2)]

def rawRow13274 : Integer.Sparse Key := [(key1085, -2), (key1164, -2), (key1093, -2), (key1093, 6), (key1085, -2), (key1164, -2), (key1093, -2), (key1085, 2), (key1164, 2), (key971, 2), (key1245, 2), (key979, 2), (key1228, 2), (key1093, -2), (key979, -2), (key1228, -2), (key1093, 6), (key1093, -2), (key979, -2), (key1228, -2)]

def rawRow13275 : Integer.Sparse Key := [(key1164, -2), (key1085, -2), (key1093, -2), (key1093, 6), (key1164, -2), (key1085, -2), (key1093, -2), (key1164, 2), (key1085, 2), (key1245, 2), (key971, 2), (key1228, 2), (key979, 2), (key1093, -2), (key1228, -2), (key979, -2), (key1093, 6), (key1093, -2), (key1228, -2), (key979, -2)]

def rawRow13276 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1085, -2), (key1093, 6), (key1093, -2), (key1164, -2), (key1085, -2), (key1228, 2), (key1245, 2), (key979, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1228, -2), (key979, -2), (key1093, -2), (key1093, 6), (key1228, -2), (key979, -2), (key1093, -2)]

def rawRow13277 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1085, -2), (key1093, 6), (key1164, -2), (key1093, -2), (key1085, -2), (key1245, 2), (key1228, 2), (key1164, 2), (key979, 2), (key1085, 2), (key971, 2), (key1228, -2), (key1093, -2), (key979, -2), (key1093, 6), (key1228, -2), (key1093, -2), (key979, -2)]

def rawRow13278 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1164, -2), (key1085, 6), (key1228, -2), (key1228, -2), (key1245, -2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1228, 6), (key979, -2), (key1093, -2), (key1093, -2)]

def rawRow13279 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1093, -2), (key1085, 6), (key1228, -2), (key1245, -2), (key1228, -2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1228, 6), (key1093, -2), (key979, -2), (key1093, -2)]

def rawRow13280 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key1245, -2), (key1228, -2), (key1228, -2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1228, 6), (key1093, -2), (key1093, -2), (key979, -2)]

def rawRow13281 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1228, -2), (key1245, 6), (key979, -2), (key979, -2), (key979, -2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1164, -2), (key1164, -2), (key1164, -2), (key971, 6), (key1085, -2), (key1085, -2), (key1085, -2)]

def rawRow13282 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1245, -2), (key1228, 6), (key1093, -2), (key1093, -2), (key1164, -2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key979, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key971, -2), (key1085, -2), (key1085, -2)]

def rawRow13283 : Integer.Sparse Key := [(key1228, -2), (key1245, -2), (key1228, -2), (key1228, 6), (key1093, -2), (key1164, -2), (key1093, -2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, -2), (key979, -2), (key1093, -2), (key1085, 6), (key1085, -2), (key971, -2), (key1085, -2)]

def rawRow13284 : Integer.Sparse Key := [(key1245, -2), (key1228, -2), (key1228, -2), (key1228, 6), (key1164, -2), (key1093, -2), (key1093, -2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, -2), (key1093, -2), (key979, -2), (key1085, 6), (key1085, -2), (key1085, -2), (key971, -2)]

def rawRow13285 : Integer.Sparse Key := [(key2353, -2), (key2359, -2), (key2359, -2), (key2359, 6), (key2448, -2), (key2454, -2), (key2454, -2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2454, -2), (key2454, -2), (key2515, -2), (key2566, 6), (key2566, -2), (key2566, -2), (key2578, -2)]

def rawRow13286 : Integer.Sparse Key := [(key2359, -2), (key2353, -2), (key2359, -2), (key2359, 6), (key2454, -2), (key2448, -2), (key2454, -2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, -2), (key2515, -2), (key2454, -2), (key2566, 6), (key2566, -2), (key2578, -2), (key2566, -2)]

def rawRow13287 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2353, -2), (key2359, 6), (key2454, -2), (key2454, -2), (key2448, -2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2515, -2), (key2454, -2), (key2454, -2), (key2566, 6), (key2578, -2), (key2566, -2), (key2566, -2)]

def rawRow13288 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2359, -2), (key2353, 6), (key2515, -2), (key2515, -2), (key2515, -2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2578, 6), (key2566, -2), (key2566, -2), (key2566, -2)]

def rawRow13289 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2454, -2), (key2515, 6), (key2353, -2), (key2359, -2), (key2359, -2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, 6), (key2454, -2), (key2454, -2), (key2515, -2)]

def rawRow13290 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2454, -2), (key2515, 6), (key2359, -2), (key2353, -2), (key2359, -2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2566, -2), (key2578, -2), (key2566, -2), (key2359, 6), (key2454, -2), (key2515, -2), (key2454, -2)]

def rawRow13291 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2448, -2), (key2515, 6), (key2359, -2), (key2359, -2), (key2353, -2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2578, -2), (key2566, -2), (key2566, -2), (key2359, 6), (key2515, -2), (key2454, -2), (key2454, -2)]

def rawRow13292 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2515, -2), (key2454, 6), (key2448, -2), (key2454, -2), (key2515, -2), (key2353, 2), (key2359, 2), (key2448, 2), (key2515, 2), (key2566, 2), (key2578, 2), (key2359, -2), (key2454, -2), (key2515, -2), (key2454, 6), (key2359, -2), (key2454, -2), (key2515, -2)]

def rawRow13293 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2515, -2), (key2454, 6), (key2454, -2), (key2448, -2), (key2515, -2), (key2359, 2), (key2353, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2359, -2), (key2515, -2), (key2454, -2), (key2454, 6), (key2359, -2), (key2515, -2), (key2454, -2)]

def rawRow13294 : Integer.Sparse Key := [(key2448, -2), (key2515, -2), (key2454, -2), (key2454, 6), (key2448, -2), (key2515, -2), (key2454, -2), (key2448, 2), (key2515, 2), (key2353, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2454, -2), (key2359, -2), (key2515, -2), (key2454, 6), (key2454, -2), (key2359, -2), (key2515, -2)]

def rawRow13295 : Integer.Sparse Key := [(key2515, -2), (key2448, -2), (key2454, -2), (key2454, 6), (key2515, -2), (key2448, -2), (key2454, -2), (key2515, 2), (key2448, 2), (key2578, 2), (key2353, 2), (key2515, 2), (key2359, 2), (key2454, -2), (key2515, -2), (key2359, -2), (key2454, 6), (key2454, -2), (key2515, -2), (key2359, -2)]

def rawRow13296 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2448, -2), (key2454, 6), (key2454, -2), (key2515, -2), (key2448, -2), (key2566, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2515, -2), (key2359, -2), (key2454, -2), (key2454, 6), (key2515, -2), (key2359, -2), (key2454, -2)]

def rawRow13297 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2448, -2), (key2454, 6), (key2515, -2), (key2454, -2), (key2448, -2), (key2578, 2), (key2566, 2), (key2515, 2), (key2359, 2), (key2448, 2), (key2353, 2), (key2515, -2), (key2454, -2), (key2359, -2), (key2454, 6), (key2515, -2), (key2454, -2), (key2359, -2)]

def rawRow13298 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2515, -2), (key2448, 6), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2515, 6), (key2359, -2), (key2454, -2), (key2454, -2)]

def rawRow13299 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2454, -2), (key2448, 6), (key2566, -2), (key2578, -2), (key2566, -2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2515, 6), (key2454, -2), (key2359, -2), (key2454, -2)]

def rawRow13300 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2578, -2), (key2566, -2), (key2566, -2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2515, 6), (key2454, -2), (key2454, -2), (key2359, -2)]

def rawRow13301 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2566, -2), (key2578, 6), (key2359, -2), (key2359, -2), (key2359, -2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2515, -2), (key2515, -2), (key2515, -2), (key2353, 6), (key2448, -2), (key2448, -2), (key2448, -2)]

def rawRow13302 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2578, -2), (key2566, 6), (key2454, -2), (key2454, -2), (key2515, -2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2359, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2353, -2), (key2448, -2), (key2448, -2)]

def rawRow13303 : Integer.Sparse Key := [(key2566, -2), (key2578, -2), (key2566, -2), (key2566, 6), (key2454, -2), (key2515, -2), (key2454, -2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, -2), (key2359, -2), (key2454, -2), (key2448, 6), (key2448, -2), (key2353, -2), (key2448, -2)]

def rawRow13304 : Integer.Sparse Key := [(key2578, -2), (key2566, -2), (key2566, -2), (key2566, 6), (key2515, -2), (key2454, -2), (key2454, -2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2454, -2), (key2454, -2), (key2359, -2), (key2448, 6), (key2448, -2), (key2448, -2), (key2353, -2)]

def rawRow13305 : Integer.Sparse Key := [(key2471, 4), (key2471, 4), (key2471, 4), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2518, 4), (key2518, 4), (key2518, 4)]

def rawRow13306 : Integer.Sparse Key := [(key2405, 4), (key2479, 4), (key2479, 4), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2436, 4), (key2502, 4), (key2502, 4)]

def rawRow13307 : Integer.Sparse Key := [(key2479, 4), (key2405, 4), (key2479, 4), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2502, 4), (key2436, 4), (key2502, 4)]

def rawRow13308 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2405, 4), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2436, -2), (key2502, 4), (key2502, 4), (key2436, 4)]

def rawRow13309 : Integer.Sparse Key := [(key2471, 4), (key2471, 4), (key2471, 4), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2518, 4), (key2518, 4), (key2518, 4)]

def rawRow13310 : Integer.Sparse Key := [(key2377, 4), (key2502, 4), (key2502, 4), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2389, 4), (key2479, 4), (key2479, 4)]

def rawRow13311 : Integer.Sparse Key := [(key2502, 4), (key2377, 4), (key2502, 4), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, 4), (key2389, 4), (key2479, 4)]

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

def rawRow13312 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2377, 4), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2479, 4), (key2479, 4), (key2389, 4)]

def rawRow13313 : Integer.Sparse Key := [(key2405, 4), (key2479, 4), (key2479, 4), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, 4), (key2502, 4), (key2502, 4)]

def rawRow13314 : Integer.Sparse Key := [(key2479, 4), (key2405, 4), (key2479, 4), (key2502, -2), (key2518, -2), (key2436, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 4), (key2436, 4), (key2502, 4)]

def rawRow13315 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2405, 4), (key2518, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2502, 4), (key2502, 4), (key2436, 4)]

def rawRow13316 : Integer.Sparse Key := [(key2377, 4), (key2502, 4), (key2502, 4), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, 4), (key2479, 4), (key2479, 4)]

def rawRow13317 : Integer.Sparse Key := [(key2502, 4), (key2377, 4), (key2502, 4), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, 4), (key2389, 4), (key2479, 4)]

def rawRow13318 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2377, 4), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2479, 4), (key2479, 4), (key2389, 4)]

def rawRow13319 : Integer.Sparse Key := [(key2389, 4), (key2436, 4), (key2518, 4), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, 4), (key2405, 4), (key2471, 4)]

def rawRow13320 : Integer.Sparse Key := [(key2389, 4), (key2518, 4), (key2436, 4), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2377, 4), (key2471, 4), (key2405, 4)]

def rawRow13321 : Integer.Sparse Key := [(key2436, 4), (key2389, 4), (key2518, 4), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, 4), (key2377, 4), (key2471, 4)]

def rawRow13322 : Integer.Sparse Key := [(key2436, 4), (key2518, 4), (key2389, 4), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2405, 4), (key2471, 4), (key2377, 4)]

def rawRow13323 : Integer.Sparse Key := [(key2518, 4), (key2389, 4), (key2436, 4), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2471, 4), (key2377, 4), (key2405, 4)]

def rawRow13324 : Integer.Sparse Key := [(key2518, 4), (key2436, 4), (key2389, 4), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2471, 4), (key2405, 4), (key2377, 4)]

def rawRow13325 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key995, -2), (key1011, 6), (key1030, -2), (key1030, -2), (key1030, -2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1119, -2), (key1119, -2), (key1119, -2), (key1067, 6), (key1146, -2), (key1146, -2), (key1146, -2)]

def rawRow13326 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key1011, -2), (key995, 6), (key1108, -2), (key1108, -2), (key1119, -2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1030, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1067, -2), (key1146, -2), (key1146, -2)]

def rawRow13327 : Integer.Sparse Key := [(key995, -2), (key1011, -2), (key995, -2), (key995, 6), (key1108, -2), (key1119, -2), (key1108, -2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1108, -2), (key1030, -2), (key1108, -2), (key1146, 6), (key1146, -2), (key1067, -2), (key1146, -2)]

def rawRow13328 : Integer.Sparse Key := [(key1011, -2), (key995, -2), (key995, -2), (key995, 6), (key1119, -2), (key1108, -2), (key1108, -2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1108, -2), (key1108, -2), (key1030, -2), (key1146, 6), (key1146, -2), (key1146, -2), (key1067, -2)]

def rawRow13329 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1030, -2), (key1067, 6), (key995, -2), (key995, -2), (key995, -2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1146, -2), (key1146, -2), (key1146, -2), (key1011, 6), (key1119, -2), (key1119, -2), (key1119, -2)]

def rawRow13330 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1067, -2), (key1030, 6), (key1108, -2), (key1108, -2), (key1146, -2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key995, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1011, -2), (key1119, -2), (key1119, -2)]

def rawRow13331 : Integer.Sparse Key := [(key1030, -2), (key1067, -2), (key1030, -2), (key1030, 6), (key1108, -2), (key1146, -2), (key1108, -2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, -2), (key995, -2), (key1108, -2), (key1119, 6), (key1119, -2), (key1011, -2), (key1119, -2)]

def rawRow13332 : Integer.Sparse Key := [(key1067, -2), (key1030, -2), (key1030, -2), (key1030, 6), (key1146, -2), (key1108, -2), (key1108, -2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1108, -2), (key1108, -2), (key995, -2), (key1119, 6), (key1119, -2), (key1119, -2), (key1011, -2)]

def rawRow13333 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1119, -2), (key1146, 6), (key995, -2), (key995, -2), (key1011, -2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1067, -2), (key1146, -2), (key1146, -2), (key995, 6), (key1030, -2), (key1108, -2), (key1108, -2)]

def rawRow13334 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1108, -2), (key1146, 6), (key995, -2), (key1011, -2), (key995, -2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1146, -2), (key1067, -2), (key1146, -2), (key995, 6), (key1108, -2), (key1030, -2), (key1108, -2)]

def rawRow13335 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1011, -2), (key995, -2), (key995, -2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1146, -2), (key1146, -2), (key1067, -2), (key995, 6), (key1108, -2), (key1108, -2), (key1030, -2)]

def rawRow13336 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1146, -2), (key1119, 6), (key1030, -2), (key1030, -2), (key1067, -2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1011, -2), (key1119, -2), (key1119, -2), (key1030, 6), (key995, -2), (key1108, -2), (key1108, -2)]

def rawRow13337 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1108, -2), (key1119, 6), (key1030, -2), (key1067, -2), (key1030, -2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1119, -2), (key1011, -2), (key1119, -2), (key1030, 6), (key1108, -2), (key995, -2), (key1108, -2)]

def rawRow13338 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1067, -2), (key1030, -2), (key1030, -2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1119, -2), (key1119, -2), (key1011, -2), (key1030, 6), (key1108, -2), (key1108, -2), (key995, -2)]

def rawRow13339 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1146, -2), (key1108, 6), (key1108, -2), (key1119, -2), (key1146, -2), (key995, 2), (key1011, 2), (key1030, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key995, -2), (key1030, -2), (key1108, -2), (key1108, 6), (key995, -2), (key1030, -2), (key1108, -2)]

def rawRow13340 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1146, -2), (key1108, 6), (key1119, -2), (key1108, -2), (key1146, -2), (key1011, 2), (key995, 2), (key1119, 2), (key1030, 2), (key1146, 2), (key1067, 2), (key995, -2), (key1108, -2), (key1030, -2), (key1108, 6), (key995, -2), (key1108, -2), (key1030, -2)]

def rawRow13341 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1119, -2), (key1108, 6), (key1108, -2), (key1146, -2), (key1119, -2), (key1030, 2), (key1067, 2), (key995, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1030, -2), (key995, -2), (key1108, -2), (key1108, 6), (key1030, -2), (key995, -2), (key1108, -2)]

def rawRow13342 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1119, -2), (key1108, 6), (key1146, -2), (key1108, -2), (key1119, -2), (key1067, 2), (key1030, 2), (key1146, 2), (key995, 2), (key1119, 2), (key1011, 2), (key1030, -2), (key1108, -2), (key995, -2), (key1108, 6), (key1030, -2), (key1108, -2), (key995, -2)]

def rawRow13343 : Integer.Sparse Key := [(key1119, -2), (key1146, -2), (key1108, -2), (key1108, 6), (key1119, -2), (key1146, -2), (key1108, -2), (key1119, 2), (key1146, 2), (key1011, 2), (key1067, 2), (key995, 2), (key1030, 2), (key1108, -2), (key995, -2), (key1030, -2), (key1108, 6), (key1108, -2), (key995, -2), (key1030, -2)]

def rawRow13344 : Integer.Sparse Key := [(key1146, -2), (key1119, -2), (key1108, -2), (key1108, 6), (key1146, -2), (key1119, -2), (key1108, -2), (key1146, 2), (key1119, 2), (key1067, 2), (key1011, 2), (key1030, 2), (key995, 2), (key1108, -2), (key1030, -2), (key995, -2), (key1108, 6), (key1108, -2), (key1030, -2), (key995, -2)]

def rawRow13345 : Integer.Sparse Key := [(key2372, -2), (key2372, -2), (key2372, -2), (key2385, 6), (key2400, -2), (key2400, -2), (key2400, -2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2475, -2), (key2475, -2), (key2475, -2), (key2432, 6), (key2498, -2), (key2498, -2), (key2498, -2)]

def rawRow13346 : Integer.Sparse Key := [(key2372, -2), (key2372, -2), (key2385, -2), (key2372, 6), (key2466, -2), (key2466, -2), (key2475, -2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2400, -2), (key2466, -2), (key2466, -2), (key2498, 6), (key2432, -2), (key2498, -2), (key2498, -2)]

def rawRow13347 : Integer.Sparse Key := [(key2372, -2), (key2385, -2), (key2372, -2), (key2372, 6), (key2466, -2), (key2475, -2), (key2466, -2), (key2466, 2), (key2475, 2), (key2400, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2466, -2), (key2400, -2), (key2466, -2), (key2498, 6), (key2498, -2), (key2432, -2), (key2498, -2)]

def rawRow13348 : Integer.Sparse Key := [(key2385, -2), (key2372, -2), (key2372, -2), (key2372, 6), (key2475, -2), (key2466, -2), (key2466, -2), (key2475, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2400, 2), (key2466, -2), (key2466, -2), (key2400, -2), (key2498, 6), (key2498, -2), (key2498, -2), (key2432, -2)]

def rawRow13349 : Integer.Sparse Key := [(key2400, -2), (key2400, -2), (key2400, -2), (key2432, 6), (key2372, -2), (key2372, -2), (key2372, -2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2498, -2), (key2498, -2), (key2498, -2), (key2385, 6), (key2475, -2), (key2475, -2), (key2475, -2)]

def rawRow13350 : Integer.Sparse Key := [(key2400, -2), (key2400, -2), (key2432, -2), (key2400, 6), (key2466, -2), (key2466, -2), (key2498, -2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2372, -2), (key2466, -2), (key2466, -2), (key2475, 6), (key2385, -2), (key2475, -2), (key2475, -2)]

def rawRow13351 : Integer.Sparse Key := [(key2400, -2), (key2432, -2), (key2400, -2), (key2400, 6), (key2466, -2), (key2498, -2), (key2466, -2), (key2466, 2), (key2498, 2), (key2372, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2466, -2), (key2372, -2), (key2466, -2), (key2475, 6), (key2475, -2), (key2385, -2), (key2475, -2)]

def rawRow13352 : Integer.Sparse Key := [(key2432, -2), (key2400, -2), (key2400, -2), (key2400, 6), (key2498, -2), (key2466, -2), (key2466, -2), (key2498, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2466, -2), (key2466, -2), (key2372, -2), (key2475, 6), (key2475, -2), (key2475, -2), (key2385, -2)]

def rawRow13353 : Integer.Sparse Key := [(key2466, -2), (key2466, -2), (key2475, -2), (key2498, 6), (key2372, -2), (key2372, -2), (key2385, -2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2432, -2), (key2498, -2), (key2498, -2), (key2372, 6), (key2400, -2), (key2466, -2), (key2466, -2)]

def rawRow13354 : Integer.Sparse Key := [(key2466, -2), (key2475, -2), (key2466, -2), (key2498, 6), (key2372, -2), (key2385, -2), (key2372, -2), (key2466, 2), (key2475, 2), (key2400, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, -2), (key2432, -2), (key2498, -2), (key2372, 6), (key2466, -2), (key2400, -2), (key2466, -2)]

def rawRow13355 : Integer.Sparse Key := [(key2475, -2), (key2466, -2), (key2466, -2), (key2498, 6), (key2385, -2), (key2372, -2), (key2372, -2), (key2475, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2400, 2), (key2498, -2), (key2498, -2), (key2432, -2), (key2372, 6), (key2466, -2), (key2466, -2), (key2400, -2)]

def rawRow13356 : Integer.Sparse Key := [(key2466, -2), (key2466, -2), (key2498, -2), (key2475, 6), (key2400, -2), (key2400, -2), (key2432, -2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2385, -2), (key2475, -2), (key2475, -2), (key2400, 6), (key2372, -2), (key2466, -2), (key2466, -2)]

def rawRow13357 : Integer.Sparse Key := [(key2466, -2), (key2498, -2), (key2466, -2), (key2475, 6), (key2400, -2), (key2432, -2), (key2400, -2), (key2466, 2), (key2498, 2), (key2372, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2475, -2), (key2385, -2), (key2475, -2), (key2400, 6), (key2466, -2), (key2372, -2), (key2466, -2)]

def rawRow13358 : Integer.Sparse Key := [(key2498, -2), (key2466, -2), (key2466, -2), (key2475, 6), (key2432, -2), (key2400, -2), (key2400, -2), (key2498, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2475, -2), (key2475, -2), (key2385, -2), (key2400, 6), (key2466, -2), (key2466, -2), (key2372, -2)]

def rawRow13359 : Integer.Sparse Key := [(key2466, -2), (key2475, -2), (key2498, -2), (key2466, 6), (key2466, -2), (key2475, -2), (key2498, -2), (key2372, 2), (key2385, 2), (key2400, 2), (key2475, 2), (key2432, 2), (key2498, 2), (key2372, -2), (key2400, -2), (key2466, -2), (key2466, 6), (key2372, -2), (key2400, -2), (key2466, -2)]

def rawRow13360 : Integer.Sparse Key := [(key2475, -2), (key2466, -2), (key2498, -2), (key2466, 6), (key2475, -2), (key2466, -2), (key2498, -2), (key2385, 2), (key2372, 2), (key2475, 2), (key2400, 2), (key2498, 2), (key2432, 2), (key2372, -2), (key2466, -2), (key2400, -2), (key2466, 6), (key2372, -2), (key2466, -2), (key2400, -2)]

def rawRow13361 : Integer.Sparse Key := [(key2466, -2), (key2498, -2), (key2475, -2), (key2466, 6), (key2466, -2), (key2498, -2), (key2475, -2), (key2400, 2), (key2432, 2), (key2372, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2400, -2), (key2372, -2), (key2466, -2), (key2466, 6), (key2400, -2), (key2372, -2), (key2466, -2)]

def rawRow13362 : Integer.Sparse Key := [(key2498, -2), (key2466, -2), (key2475, -2), (key2466, 6), (key2498, -2), (key2466, -2), (key2475, -2), (key2432, 2), (key2400, 2), (key2498, 2), (key2372, 2), (key2475, 2), (key2385, 2), (key2400, -2), (key2466, -2), (key2372, -2), (key2466, 6), (key2400, -2), (key2466, -2), (key2372, -2)]

def rawRow13363 : Integer.Sparse Key := [(key2475, -2), (key2498, -2), (key2466, -2), (key2466, 6), (key2475, -2), (key2498, -2), (key2466, -2), (key2475, 2), (key2498, 2), (key2385, 2), (key2432, 2), (key2372, 2), (key2400, 2), (key2466, -2), (key2372, -2), (key2400, -2), (key2466, 6), (key2466, -2), (key2372, -2), (key2400, -2)]

def rawRow13364 : Integer.Sparse Key := [(key2498, -2), (key2475, -2), (key2466, -2), (key2466, 6), (key2498, -2), (key2475, -2), (key2466, -2), (key2498, 2), (key2475, 2), (key2432, 2), (key2385, 2), (key2400, 2), (key2372, 2), (key2466, -2), (key2400, -2), (key2372, -2), (key2466, 6), (key2466, -2), (key2400, -2), (key2372, -2)]

def rawRow13365 : Integer.Sparse Key := [(key2606, 6), (key2622, -2), (key2622, -2), (key2622, -2), (key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2776, -2), (key2776, -2), (key2776, -2), (key2799, -2), (key2799, -2), (key2799, -2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

def rawRow13366 : Integer.Sparse Key := [(key2622, 6), (key2606, -2), (key2622, -2), (key2622, -2), (key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, -2), (key2849, -2), (key2849, -2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

def rawRow13367 : Integer.Sparse Key := [(key2622, 6), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, -2), (key2849, -2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

def rawRow13368 : Integer.Sparse Key := [(key2622, 6), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, -2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

def rawRow13369 : Integer.Sparse Key := [(key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2606, 6), (key2799, -2), (key2799, -2), (key2799, -2), (key2622, -2), (key2622, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2696, -2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

def rawRow13370 : Integer.Sparse Key := [(key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, 6), (key2606, -2), (key2799, -2), (key2799, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, -2), (key2849, -2), (key2849, -2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

def rawRow13371 : Integer.Sparse Key := [(key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 6), (key2799, -2), (key2606, -2), (key2799, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

def rawRow13372 : Integer.Sparse Key := [(key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, 6), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, -2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

def rawRow13373 : Integer.Sparse Key := [(key2776, 6), (key2799, -2), (key2849, -2), (key2849, -2), (key2622, 6), (key2696, -2), (key2849, -2), (key2849, -2), (key2606, -2), (key2622, -2), (key2622, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

def rawRow13374 : Integer.Sparse Key := [(key2776, 6), (key2849, -2), (key2799, -2), (key2849, -2), (key2622, 6), (key2849, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

def rawRow13375 : Integer.Sparse Key := [(key2776, 6), (key2849, -2), (key2849, -2), (key2799, -2), (key2622, 6), (key2849, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

def rawRow13376 : Integer.Sparse Key := [(key2799, 6), (key2776, -2), (key2849, -2), (key2849, -2), (key2696, 6), (key2622, -2), (key2849, -2), (key2849, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2606, -2), (key2799, -2), (key2799, -2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

def rawRow13377 : Integer.Sparse Key := [(key2799, 6), (key2849, -2), (key2776, -2), (key2849, -2), (key2696, 6), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, -2), (key2606, -2), (key2799, -2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

def rawRow13378 : Integer.Sparse Key := [(key2799, 6), (key2849, -2), (key2849, -2), (key2776, -2), (key2696, 6), (key2849, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

def rawRow13379 : Integer.Sparse Key := [(key2849, 6), (key2776, -2), (key2799, -2), (key2849, -2), (key2849, 6), (key2622, -2), (key2696, -2), (key2849, -2), (key2776, -2), (key2799, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2849, -2), (key2606, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, 2), (key2799, 2)]

def rawRow13380 : Integer.Sparse Key := [(key2849, 6), (key2776, -2), (key2849, -2), (key2799, -2), (key2849, 6), (key2622, -2), (key2849, -2), (key2696, -2), (key2776, -2), (key2849, -2), (key2799, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2622, 2), (key2606, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2776, 2)]

def rawRow13381 : Integer.Sparse Key := [(key2849, 6), (key2799, -2), (key2776, -2), (key2849, -2), (key2849, 6), (key2696, -2), (key2622, -2), (key2849, -2), (key2799, -2), (key2776, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2849, -2), (key2661, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2622, 2), (key2696, 2)]

def rawRow13382 : Integer.Sparse Key := [(key2849, 6), (key2799, -2), (key2849, -2), (key2776, -2), (key2849, 6), (key2696, -2), (key2849, -2), (key2622, -2), (key2799, -2), (key2849, -2), (key2776, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2696, 2), (key2661, 2), (key2799, 2), (key2606, 2), (key2696, 2), (key2622, 2)]

def rawRow13383 : Integer.Sparse Key := [(key2849, 6), (key2849, -2), (key2776, -2), (key2799, -2), (key2849, 6), (key2849, -2), (key2622, -2), (key2696, -2), (key2849, -2), (key2776, -2), (key2799, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2776, 2), (key2799, 2), (key2622, 2), (key2696, 2), (key2606, 2), (key2661, 2)]

def rawRow13384 : Integer.Sparse Key := [(key2849, 6), (key2849, -2), (key2799, -2), (key2776, -2), (key2849, 6), (key2849, -2), (key2696, -2), (key2622, -2), (key2849, -2), (key2799, -2), (key2776, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2799, 2), (key2776, 2), (key2696, 2), (key2622, 2), (key2661, 2), (key2606, 2)]

def rawRow13385 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1168, 4), (key1090, -2), (key1097, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1168, -2), (key1180, -2), (key1182, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1219, -2), (key1182, 4), (key1182, 4), (key1219, 4)]

def rawRow13386 : Integer.Sparse Key := [(key1090, 4), (key1168, 4), (key1090, 4), (key1097, -2), (key1090, -2), (key1168, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1182, -2), (key1180, -2), (key1219, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1182, 4), (key1219, 4), (key1182, 4)]

def rawRow13387 : Integer.Sparse Key := [(key1168, 4), (key1090, 4), (key1090, 4), (key1168, -2), (key1168, -2), (key1097, -2), (key1097, -2), (key1090, -2), (key1090, -2), (key1219, -2), (key1219, -2), (key1182, -2), (key1182, -2), (key1180, -2), (key1180, -2), (key1219, 4), (key1182, 4), (key1182, 4)]

def rawRow13388 : Integer.Sparse Key := [(key1097, 4), (key1097, 4), (key1097, 4), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

def rawRow13389 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1168, 4), (key1180, -2), (key1182, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1219, -2), (key1090, -2), (key1097, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1168, -2), (key1182, 4), (key1182, 4), (key1219, 4)]

def rawRow13390 : Integer.Sparse Key := [(key1090, 4), (key1168, 4), (key1090, 4), (key1182, -2), (key1180, -2), (key1219, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1097, -2), (key1090, -2), (key1168, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1182, 4), (key1219, 4), (key1182, 4)]

def rawRow13391 : Integer.Sparse Key := [(key1168, 4), (key1090, 4), (key1090, 4), (key1219, -2), (key1219, -2), (key1182, -2), (key1182, -2), (key1180, -2), (key1180, -2), (key1168, -2), (key1168, -2), (key1097, -2), (key1097, -2), (key1090, -2), (key1090, -2), (key1219, 4), (key1182, 4), (key1182, 4)]

def rawRow13392 : Integer.Sparse Key := [(key976, 4), (key1180, 4), (key1219, 4), (key976, -2), (key983, -2), (key1090, -2), (key1168, -2), (key1182, -2), (key1219, -2), (key976, -2), (key983, -2), (key1090, -2), (key1168, -2), (key1182, -2), (key1219, -2), (key983, 4), (key1097, 4), (key1168, 4)]

def rawRow13393 : Integer.Sparse Key := [(key976, 4), (key1219, 4), (key1180, 4), (key983, -2), (key976, -2), (key1168, -2), (key1090, -2), (key1219, -2), (key1182, -2), (key983, -2), (key976, -2), (key1168, -2), (key1090, -2), (key1219, -2), (key1182, -2), (key983, 4), (key1168, 4), (key1097, 4)]

def rawRow13394 : Integer.Sparse Key := [(key1180, 4), (key976, 4), (key1219, 4), (key1090, -2), (key1182, -2), (key976, -2), (key1219, -2), (key983, -2), (key1168, -2), (key1090, -2), (key1182, -2), (key976, -2), (key1219, -2), (key983, -2), (key1168, -2), (key1097, 4), (key983, 4), (key1168, 4)]

def rawRow13395 : Integer.Sparse Key := [(key1180, 4), (key1219, 4), (key976, 4), (key1182, -2), (key1090, -2), (key1219, -2), (key976, -2), (key1168, -2), (key983, -2), (key1182, -2), (key1090, -2), (key1219, -2), (key976, -2), (key1168, -2), (key983, -2), (key1097, 4), (key1168, 4), (key983, 4)]

def rawRow13396 : Integer.Sparse Key := [(key1219, 4), (key976, 4), (key1180, 4), (key1168, -2), (key1219, -2), (key983, -2), (key1182, -2), (key976, -2), (key1090, -2), (key1168, -2), (key1219, -2), (key983, -2), (key1182, -2), (key976, -2), (key1090, -2), (key1168, 4), (key983, 4), (key1097, 4)]

def rawRow13397 : Integer.Sparse Key := [(key1219, 4), (key1180, 4), (key976, 4), (key1219, -2), (key1168, -2), (key1182, -2), (key983, -2), (key1090, -2), (key976, -2), (key1219, -2), (key1168, -2), (key1182, -2), (key983, -2), (key1090, -2), (key976, -2), (key1168, 4), (key1097, 4), (key983, 4)]

def rawRow13398 : Integer.Sparse Key := [(key983, 4), (key1182, 4), (key1182, 4), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key983, -2), (key983, -2), (key1097, -2), (key1097, -2), (key1182, -2), (key1182, -2), (key976, 4), (key1090, 4), (key1090, 4)]

def rawRow13399 : Integer.Sparse Key := [(key1182, 4), (key983, 4), (key1182, 4), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1097, -2), (key1182, -2), (key983, -2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, 4), (key976, 4), (key1090, 4)]

def rawRow13400 : Integer.Sparse Key := [(key1182, 4), (key1182, 4), (key983, 4), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1182, -2), (key1097, -2), (key1182, -2), (key983, -2), (key1097, -2), (key983, -2), (key1090, 4), (key1090, 4), (key976, 4)]

def rawRow13401 : Integer.Sparse Key := [(key1097, 4), (key1097, 4), (key1097, 4), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

def rawRow13402 : Integer.Sparse Key := [(key983, 4), (key1182, 4), (key1182, 4), (key983, -2), (key983, -2), (key1097, -2), (key1097, -2), (key1182, -2), (key1182, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key976, 4), (key1090, 4), (key1090, 4)]

def rawRow13403 : Integer.Sparse Key := [(key1182, 4), (key983, 4), (key1182, 4), (key1097, -2), (key1182, -2), (key983, -2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, 4), (key976, 4), (key1090, 4)]

def rawRow13404 : Integer.Sparse Key := [(key1182, 4), (key1182, 4), (key983, 4), (key1182, -2), (key1097, -2), (key1182, -2), (key983, -2), (key1097, -2), (key983, -2), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1090, 4), (key1090, 4), (key976, 4)]

def rawRow13405 : Integer.Sparse Key := [(key2, -2), (key6, -2), (key6, -2), (key6, 6), (key85, -2), (key89, -2), (key89, -2), (key85, 2), (key89, 2), (key85, 2), (key166, 2), (key89, 2), (key166, 2), (key89, -2), (key89, -2), (key166, -2), (key150, 6), (key150, -2), (key150, -2), (key186, -2)]

def rawRow13406 : Integer.Sparse Key := [(key6, -2), (key2, -2), (key6, -2), (key6, 6), (key89, -2), (key85, -2), (key89, -2), (key89, 2), (key85, 2), (key166, 2), (key85, 2), (key166, 2), (key89, 2), (key89, -2), (key166, -2), (key89, -2), (key150, 6), (key150, -2), (key186, -2), (key150, -2)]

def rawRow13407 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key2, -2), (key6, 6), (key89, -2), (key89, -2), (key85, -2), (key166, 2), (key166, 2), (key89, 2), (key89, 2), (key85, 2), (key85, 2), (key166, -2), (key89, -2), (key89, -2), (key150, 6), (key186, -2), (key150, -2), (key150, -2)]

def rawRow13408 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key6, -2), (key2, 6), (key166, -2), (key166, -2), (key166, -2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key85, -2), (key85, -2), (key85, -2), (key186, 6), (key150, -2), (key150, -2), (key150, -2)]

def rawRow13409 : Integer.Sparse Key := [(key85, -2), (key89, -2), (key89, -2), (key150, 6), (key2, -2), (key6, -2), (key6, -2), (key85, 2), (key89, 2), (key85, 2), (key166, 2), (key89, 2), (key166, 2), (key150, -2), (key150, -2), (key186, -2), (key6, 6), (key89, -2), (key89, -2), (key166, -2)]

def rawRow13410 : Integer.Sparse Key := [(key89, -2), (key85, -2), (key89, -2), (key150, 6), (key6, -2), (key2, -2), (key6, -2), (key89, 2), (key85, 2), (key166, 2), (key85, 2), (key166, 2), (key89, 2), (key150, -2), (key186, -2), (key150, -2), (key6, 6), (key89, -2), (key166, -2), (key89, -2)]

def rawRow13411 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key85, -2), (key150, 6), (key6, -2), (key6, -2), (key2, -2), (key166, 2), (key166, 2), (key89, 2), (key89, 2), (key85, 2), (key85, 2), (key186, -2), (key150, -2), (key150, -2), (key6, 6), (key166, -2), (key89, -2), (key89, -2)]

def rawRow13412 : Integer.Sparse Key := [(key85, -2), (key89, -2), (key150, -2), (key89, 6), (key85, -2), (key89, -2), (key150, -2), (key2, 2), (key6, 2), (key85, 2), (key166, 2), (key150, 2), (key186, 2), (key6, -2), (key89, -2), (key166, -2), (key89, 6), (key6, -2), (key89, -2), (key166, -2)]

def rawRow13413 : Integer.Sparse Key := [(key89, -2), (key85, -2), (key150, -2), (key89, 6), (key89, -2), (key85, -2), (key150, -2), (key6, 2), (key2, 2), (key166, 2), (key85, 2), (key186, 2), (key150, 2), (key6, -2), (key166, -2), (key89, -2), (key89, 6), (key6, -2), (key166, -2), (key89, -2)]

def rawRow13414 : Integer.Sparse Key := [(key85, -2), (key150, -2), (key89, -2), (key89, 6), (key85, -2), (key150, -2), (key89, -2), (key85, 2), (key150, 2), (key2, 2), (key186, 2), (key6, 2), (key166, 2), (key89, -2), (key6, -2), (key166, -2), (key89, 6), (key89, -2), (key6, -2), (key166, -2)]

def rawRow13415 : Integer.Sparse Key := [(key150, -2), (key85, -2), (key89, -2), (key89, 6), (key150, -2), (key85, -2), (key89, -2), (key150, 2), (key85, 2), (key186, 2), (key2, 2), (key166, 2), (key6, 2), (key89, -2), (key166, -2), (key6, -2), (key89, 6), (key89, -2), (key166, -2), (key6, -2)]

def rawRow13416 : Integer.Sparse Key := [(key89, -2), (key150, -2), (key85, -2), (key89, 6), (key89, -2), (key150, -2), (key85, -2), (key166, 2), (key186, 2), (key6, 2), (key150, 2), (key2, 2), (key85, 2), (key166, -2), (key6, -2), (key89, -2), (key89, 6), (key166, -2), (key6, -2), (key89, -2)]

def rawRow13417 : Integer.Sparse Key := [(key150, -2), (key89, -2), (key85, -2), (key89, 6), (key150, -2), (key89, -2), (key85, -2), (key186, 2), (key166, 2), (key150, 2), (key6, 2), (key85, 2), (key2, 2), (key166, -2), (key89, -2), (key6, -2), (key89, 6), (key166, -2), (key89, -2), (key6, -2)]

def rawRow13418 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key150, -2), (key85, 6), (key166, -2), (key166, -2), (key186, -2), (key6, 2), (key6, 2), (key89, 2), (key89, 2), (key150, 2), (key150, 2), (key2, -2), (key85, -2), (key85, -2), (key166, 6), (key6, -2), (key89, -2), (key89, -2)]

def rawRow13419 : Integer.Sparse Key := [(key89, -2), (key150, -2), (key89, -2), (key85, 6), (key166, -2), (key186, -2), (key166, -2), (key89, 2), (key150, 2), (key6, 2), (key150, 2), (key6, 2), (key89, 2), (key85, -2), (key2, -2), (key85, -2), (key166, 6), (key89, -2), (key6, -2), (key89, -2)]

def rawRow13420 : Integer.Sparse Key := [(key150, -2), (key89, -2), (key89, -2), (key85, 6), (key186, -2), (key166, -2), (key166, -2), (key150, 2), (key89, 2), (key150, 2), (key6, 2), (key89, 2), (key6, 2), (key85, -2), (key85, -2), (key2, -2), (key166, 6), (key89, -2), (key89, -2), (key6, -2)]

def rawRow13421 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key166, -2), (key186, 6), (key6, -2), (key6, -2), (key6, -2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key150, -2), (key150, -2), (key150, -2), (key2, 6), (key85, -2), (key85, -2), (key85, -2)]

def rawRow13422 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key186, -2), (key166, 6), (key89, -2), (key89, -2), (key150, -2), (key6, 2), (key6, 2), (key89, 2), (key89, 2), (key150, 2), (key150, 2), (key6, -2), (key89, -2), (key89, -2), (key85, 6), (key2, -2), (key85, -2), (key85, -2)]

def rawRow13423 : Integer.Sparse Key := [(key166, -2), (key186, -2), (key166, -2), (key166, 6), (key89, -2), (key150, -2), (key89, -2), (key89, 2), (key150, 2), (key6, 2), (key150, 2), (key6, 2), (key89, 2), (key89, -2), (key6, -2), (key89, -2), (key85, 6), (key85, -2), (key2, -2), (key85, -2)]

def rawRow13424 : Integer.Sparse Key := [(key186, -2), (key166, -2), (key166, -2), (key166, 6), (key150, -2), (key89, -2), (key89, -2), (key150, 2), (key89, 2), (key150, 2), (key6, 2), (key89, 2), (key6, 2), (key89, -2), (key89, -2), (key6, -2), (key85, 6), (key85, -2), (key85, -2), (key2, -2)]

def rawRow13425 : Integer.Sparse Key := [(key972, -2), (key978, -2), (key978, -2), (key978, 6), (key1086, -2), (key1092, -2), (key1092, -2), (key1086, 2), (key1092, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1163, 2), (key1092, -2), (key1092, -2), (key1163, -2), (key1227, 6), (key1227, -2), (key1227, -2), (key1244, -2)]

def rawRow13426 : Integer.Sparse Key := [(key978, -2), (key972, -2), (key978, -2), (key978, 6), (key1092, -2), (key1086, -2), (key1092, -2), (key1092, 2), (key1086, 2), (key1163, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1092, -2), (key1163, -2), (key1092, -2), (key1227, 6), (key1227, -2), (key1244, -2), (key1227, -2)]

def rawRow13427 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key972, -2), (key978, 6), (key1092, -2), (key1092, -2), (key1086, -2), (key1163, 2), (key1163, 2), (key1092, 2), (key1092, 2), (key1086, 2), (key1086, 2), (key1163, -2), (key1092, -2), (key1092, -2), (key1227, 6), (key1244, -2), (key1227, -2), (key1227, -2)]

def rawRow13428 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key978, -2), (key972, 6), (key1163, -2), (key1163, -2), (key1163, -2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1244, 6), (key1227, -2), (key1227, -2), (key1227, -2)]

def rawRow13429 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1092, -2), (key1227, 6), (key972, -2), (key978, -2), (key978, -2), (key1086, 2), (key1092, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1163, 2), (key1227, -2), (key1227, -2), (key1244, -2), (key978, 6), (key1092, -2), (key1092, -2), (key1163, -2)]

def rawRow13430 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1092, -2), (key1227, 6), (key978, -2), (key972, -2), (key978, -2), (key1092, 2), (key1086, 2), (key1163, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1227, -2), (key1244, -2), (key1227, -2), (key978, 6), (key1092, -2), (key1163, -2), (key1092, -2)]

def rawRow13431 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1086, -2), (key1227, 6), (key978, -2), (key978, -2), (key972, -2), (key1163, 2), (key1163, 2), (key1092, 2), (key1092, 2), (key1086, 2), (key1086, 2), (key1244, -2), (key1227, -2), (key1227, -2), (key978, 6), (key1163, -2), (key1092, -2), (key1092, -2)]

def rawRow13432 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1227, -2), (key1092, 6), (key1086, -2), (key1092, -2), (key1227, -2), (key972, 2), (key978, 2), (key1086, 2), (key1163, 2), (key1227, 2), (key1244, 2), (key978, -2), (key1092, -2), (key1163, -2), (key1092, 6), (key978, -2), (key1092, -2), (key1163, -2)]

def rawRow13433 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1227, -2), (key1092, 6), (key1092, -2), (key1086, -2), (key1227, -2), (key978, 2), (key972, 2), (key1163, 2), (key1086, 2), (key1244, 2), (key1227, 2), (key978, -2), (key1163, -2), (key1092, -2), (key1092, 6), (key978, -2), (key1163, -2), (key1092, -2)]

def rawRow13434 : Integer.Sparse Key := [(key1086, -2), (key1227, -2), (key1092, -2), (key1092, 6), (key1086, -2), (key1227, -2), (key1092, -2), (key1086, 2), (key1227, 2), (key972, 2), (key1244, 2), (key978, 2), (key1163, 2), (key1092, -2), (key978, -2), (key1163, -2), (key1092, 6), (key1092, -2), (key978, -2), (key1163, -2)]

def rawRow13435 : Integer.Sparse Key := [(key1227, -2), (key1086, -2), (key1092, -2), (key1092, 6), (key1227, -2), (key1086, -2), (key1092, -2), (key1227, 2), (key1086, 2), (key1244, 2), (key972, 2), (key1163, 2), (key978, 2), (key1092, -2), (key1163, -2), (key978, -2), (key1092, 6), (key1092, -2), (key1163, -2), (key978, -2)]

def rawRow13436 : Integer.Sparse Key := [(key1092, -2), (key1227, -2), (key1086, -2), (key1092, 6), (key1092, -2), (key1227, -2), (key1086, -2), (key1163, 2), (key1244, 2), (key978, 2), (key1227, 2), (key972, 2), (key1086, 2), (key1163, -2), (key978, -2), (key1092, -2), (key1092, 6), (key1163, -2), (key978, -2), (key1092, -2)]

def rawRow13437 : Integer.Sparse Key := [(key1227, -2), (key1092, -2), (key1086, -2), (key1092, 6), (key1227, -2), (key1092, -2), (key1086, -2), (key1244, 2), (key1163, 2), (key1227, 2), (key978, 2), (key1086, 2), (key972, 2), (key1163, -2), (key1092, -2), (key978, -2), (key1092, 6), (key1163, -2), (key1092, -2), (key978, -2)]

def rawRow13438 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1227, -2), (key1086, 6), (key1163, -2), (key1163, -2), (key1244, -2), (key978, 2), (key978, 2), (key1092, 2), (key1092, 2), (key1227, 2), (key1227, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1163, 6), (key978, -2), (key1092, -2), (key1092, -2)]

def rawRow13439 : Integer.Sparse Key := [(key1092, -2), (key1227, -2), (key1092, -2), (key1086, 6), (key1163, -2), (key1244, -2), (key1163, -2), (key1092, 2), (key1227, 2), (key978, 2), (key1227, 2), (key978, 2), (key1092, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1163, 6), (key1092, -2), (key978, -2), (key1092, -2)]

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

def rawRow13440 : Integer.Sparse Key := [(key1227, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key1244, -2), (key1163, -2), (key1163, -2), (key1227, 2), (key1092, 2), (key1227, 2), (key978, 2), (key1092, 2), (key978, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1163, 6), (key1092, -2), (key1092, -2), (key978, -2)]

def rawRow13441 : Integer.Sparse Key := [(key1163, -2), (key1163, -2), (key1163, -2), (key1244, 6), (key978, -2), (key978, -2), (key978, -2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1227, -2), (key1227, -2), (key1227, -2), (key972, 6), (key1086, -2), (key1086, -2), (key1086, -2)]

def rawRow13442 : Integer.Sparse Key := [(key1163, -2), (key1163, -2), (key1244, -2), (key1163, 6), (key1092, -2), (key1092, -2), (key1227, -2), (key978, 2), (key978, 2), (key1092, 2), (key1092, 2), (key1227, 2), (key1227, 2), (key978, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key972, -2), (key1086, -2), (key1086, -2)]

def rawRow13443 : Integer.Sparse Key := [(key1163, -2), (key1244, -2), (key1163, -2), (key1163, 6), (key1092, -2), (key1227, -2), (key1092, -2), (key1092, 2), (key1227, 2), (key978, 2), (key1227, 2), (key978, 2), (key1092, 2), (key1092, -2), (key978, -2), (key1092, -2), (key1086, 6), (key1086, -2), (key972, -2), (key1086, -2)]

def rawRow13444 : Integer.Sparse Key := [(key1244, -2), (key1163, -2), (key1163, -2), (key1163, 6), (key1227, -2), (key1092, -2), (key1092, -2), (key1227, 2), (key1092, 2), (key1227, 2), (key978, 2), (key1092, 2), (key978, 2), (key1092, -2), (key1092, -2), (key978, -2), (key1086, 6), (key1086, -2), (key1086, -2), (key972, -2)]

def rawRow13445 : Integer.Sparse Key := [(key992, 6), (key992, -2), (key992, -2), (key1010, -2), (key1027, 6), (key1027, -2), (key1027, -2), (key1066, -2), (key1105, -2), (key1105, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, -2), (key1105, 2), (key1118, 2), (key1105, 2), (key1145, 2), (key1118, 2), (key1145, 2)]

def rawRow13446 : Integer.Sparse Key := [(key992, 6), (key992, -2), (key1010, -2), (key992, -2), (key1027, 6), (key1027, -2), (key1066, -2), (key1027, -2), (key1105, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, -2), (key1105, -2), (key1118, 2), (key1105, 2), (key1145, 2), (key1105, 2), (key1145, 2), (key1118, 2)]

def rawRow13447 : Integer.Sparse Key := [(key992, 6), (key1010, -2), (key992, -2), (key992, -2), (key1027, 6), (key1066, -2), (key1027, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, -2), (key1105, -2), (key1105, -2), (key1145, 2), (key1145, 2), (key1118, 2), (key1118, 2), (key1105, 2), (key1105, 2)]

def rawRow13448 : Integer.Sparse Key := [(key1010, 6), (key992, -2), (key992, -2), (key992, -2), (key1066, 6), (key1027, -2), (key1027, -2), (key1027, -2), (key1145, -2), (key1145, -2), (key1145, -2), (key1118, -2), (key1118, -2), (key1118, -2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2)]

def rawRow13449 : Integer.Sparse Key := [(key1027, 6), (key1105, -2), (key1105, -2), (key1118, -2), (key992, 6), (key1105, -2), (key1105, -2), (key1145, -2), (key992, -2), (key992, -2), (key1010, -2), (key1027, -2), (key1027, -2), (key1066, -2), (key1105, 2), (key1118, 2), (key1105, 2), (key1145, 2), (key1118, 2), (key1145, 2)]

def rawRow13450 : Integer.Sparse Key := [(key1027, 6), (key1105, -2), (key1118, -2), (key1105, -2), (key992, 6), (key1105, -2), (key1145, -2), (key1105, -2), (key992, -2), (key1010, -2), (key992, -2), (key1027, -2), (key1066, -2), (key1027, -2), (key1118, 2), (key1105, 2), (key1145, 2), (key1105, 2), (key1145, 2), (key1118, 2)]

def rawRow13451 : Integer.Sparse Key := [(key1027, 6), (key1118, -2), (key1105, -2), (key1105, -2), (key992, 6), (key1145, -2), (key1105, -2), (key1105, -2), (key1010, -2), (key992, -2), (key992, -2), (key1066, -2), (key1027, -2), (key1027, -2), (key1145, 2), (key1145, 2), (key1118, 2), (key1118, 2), (key1105, 2), (key1105, 2)]

def rawRow13452 : Integer.Sparse Key := [(key1105, 6), (key1027, -2), (key1105, -2), (key1118, -2), (key1105, 6), (key992, -2), (key1105, -2), (key1145, -2), (key1027, -2), (key1105, -2), (key1118, -2), (key992, -2), (key1105, -2), (key1145, -2), (key992, 2), (key1010, 2), (key1027, 2), (key1066, 2), (key1118, 2), (key1145, 2)]

def rawRow13453 : Integer.Sparse Key := [(key1105, 6), (key1027, -2), (key1118, -2), (key1105, -2), (key1105, 6), (key992, -2), (key1145, -2), (key1105, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1105, -2), (key1010, 2), (key992, 2), (key1066, 2), (key1027, 2), (key1145, 2), (key1118, 2)]

def rawRow13454 : Integer.Sparse Key := [(key1105, 6), (key1105, -2), (key1027, -2), (key1118, -2), (key1105, 6), (key1105, -2), (key992, -2), (key1145, -2), (key1105, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1027, 2), (key1118, 2), (key992, 2), (key1145, 2), (key1010, 2), (key1066, 2)]

def rawRow13455 : Integer.Sparse Key := [(key1105, 6), (key1105, -2), (key1118, -2), (key1027, -2), (key1105, 6), (key1105, -2), (key1145, -2), (key992, -2), (key1105, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1145, -2), (key992, -2), (key1118, 2), (key1027, 2), (key1145, 2), (key992, 2), (key1066, 2), (key1010, 2)]

def rawRow13456 : Integer.Sparse Key := [(key1105, 6), (key1118, -2), (key1027, -2), (key1105, -2), (key1105, 6), (key1145, -2), (key992, -2), (key1105, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1145, -2), (key992, -2), (key1105, -2), (key1066, 2), (key1145, 2), (key1010, 2), (key1118, 2), (key992, 2), (key1027, 2)]

def rawRow13457 : Integer.Sparse Key := [(key1105, 6), (key1118, -2), (key1105, -2), (key1027, -2), (key1105, 6), (key1145, -2), (key1105, -2), (key992, -2), (key1118, -2), (key1105, -2), (key1027, -2), (key1145, -2), (key1105, -2), (key992, -2), (key1145, 2), (key1066, 2), (key1118, 2), (key1010, 2), (key1027, 2), (key992, 2)]

def rawRow13458 : Integer.Sparse Key := [(key1118, 6), (key1027, -2), (key1105, -2), (key1105, -2), (key1145, 6), (key992, -2), (key1105, -2), (key1105, -2), (key1066, -2), (key1145, -2), (key1145, -2), (key1010, -2), (key1118, -2), (key1118, -2), (key992, 2), (key992, 2), (key1027, 2), (key1027, 2), (key1105, 2), (key1105, 2)]

def rawRow13459 : Integer.Sparse Key := [(key1118, 6), (key1105, -2), (key1027, -2), (key1105, -2), (key1145, 6), (key1105, -2), (key992, -2), (key1105, -2), (key1145, -2), (key1066, -2), (key1145, -2), (key1118, -2), (key1010, -2), (key1118, -2), (key1027, 2), (key1105, 2), (key992, 2), (key1105, 2), (key992, 2), (key1027, 2)]

def rawRow13460 : Integer.Sparse Key := [(key1118, 6), (key1105, -2), (key1105, -2), (key1027, -2), (key1145, 6), (key1105, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1145, -2), (key1066, -2), (key1118, -2), (key1118, -2), (key1010, -2), (key1105, 2), (key1027, 2), (key1105, 2), (key992, 2), (key1027, 2), (key992, 2)]

def rawRow13461 : Integer.Sparse Key := [(key1066, 6), (key1145, -2), (key1145, -2), (key1145, -2), (key1010, 6), (key1118, -2), (key1118, -2), (key1118, -2), (key992, -2), (key992, -2), (key992, -2), (key1027, -2), (key1027, -2), (key1027, -2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2), (key1105, 2)]

def rawRow13462 : Integer.Sparse Key := [(key1145, 6), (key1066, -2), (key1145, -2), (key1145, -2), (key1118, 6), (key1010, -2), (key1118, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, -2), (key1105, -2), (key1105, -2), (key992, 2), (key992, 2), (key1027, 2), (key1027, 2), (key1105, 2), (key1105, 2)]

def rawRow13463 : Integer.Sparse Key := [(key1145, 6), (key1145, -2), (key1066, -2), (key1145, -2), (key1118, 6), (key1118, -2), (key1010, -2), (key1118, -2), (key1105, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, -2), (key1105, -2), (key1027, 2), (key1105, 2), (key992, 2), (key1105, 2), (key992, 2), (key1027, 2)]

def rawRow13464 : Integer.Sparse Key := [(key1145, 6), (key1145, -2), (key1145, -2), (key1066, -2), (key1118, 6), (key1118, -2), (key1118, -2), (key1010, -2), (key1105, -2), (key1105, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, -2), (key1105, 2), (key1027, 2), (key1105, 2), (key992, 2), (key1027, 2), (key992, 2)]

def rawRow13465 : Integer.Sparse Key := [(key1, -2), (key4, -2), (key4, -2), (key4, 6), (key84, -2), (key87, -2), (key87, -2), (key84, 2), (key87, 2), (key84, 2), (key148, 2), (key87, 2), (key148, 2), (key87, -2), (key87, -2), (key148, -2), (key164, 6), (key164, -2), (key164, -2), (key184, -2)]

def rawRow13466 : Integer.Sparse Key := [(key4, -2), (key1, -2), (key4, -2), (key4, 6), (key87, -2), (key84, -2), (key87, -2), (key87, 2), (key84, 2), (key148, 2), (key84, 2), (key148, 2), (key87, 2), (key87, -2), (key148, -2), (key87, -2), (key164, 6), (key164, -2), (key184, -2), (key164, -2)]

def rawRow13467 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key1, -2), (key4, 6), (key87, -2), (key87, -2), (key84, -2), (key148, 2), (key148, 2), (key87, 2), (key87, 2), (key84, 2), (key84, 2), (key148, -2), (key87, -2), (key87, -2), (key164, 6), (key184, -2), (key164, -2), (key164, -2)]

def rawRow13468 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key4, -2), (key1, 6), (key148, -2), (key148, -2), (key148, -2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key84, -2), (key84, -2), (key84, -2), (key184, 6), (key164, -2), (key164, -2), (key164, -2)]

def rawRow13469 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key87, -2), (key148, 6), (key1, -2), (key4, -2), (key4, -2), (key84, 2), (key87, 2), (key84, 2), (key148, 2), (key87, 2), (key148, 2), (key164, -2), (key164, -2), (key184, -2), (key4, 6), (key87, -2), (key87, -2), (key148, -2)]

def rawRow13470 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key87, -2), (key148, 6), (key4, -2), (key1, -2), (key4, -2), (key87, 2), (key84, 2), (key148, 2), (key84, 2), (key148, 2), (key87, 2), (key164, -2), (key184, -2), (key164, -2), (key4, 6), (key87, -2), (key148, -2), (key87, -2)]

def rawRow13471 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key84, -2), (key148, 6), (key4, -2), (key4, -2), (key1, -2), (key148, 2), (key148, 2), (key87, 2), (key87, 2), (key84, 2), (key84, 2), (key184, -2), (key164, -2), (key164, -2), (key4, 6), (key148, -2), (key87, -2), (key87, -2)]

def rawRow13472 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key148, -2), (key87, 6), (key84, -2), (key87, -2), (key148, -2), (key1, 2), (key4, 2), (key84, 2), (key148, 2), (key164, 2), (key184, 2), (key4, -2), (key87, -2), (key148, -2), (key87, 6), (key4, -2), (key87, -2), (key148, -2)]

def rawRow13473 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key148, -2), (key87, 6), (key87, -2), (key84, -2), (key148, -2), (key4, 2), (key1, 2), (key148, 2), (key84, 2), (key184, 2), (key164, 2), (key4, -2), (key148, -2), (key87, -2), (key87, 6), (key4, -2), (key148, -2), (key87, -2)]

def rawRow13474 : Integer.Sparse Key := [(key84, -2), (key148, -2), (key87, -2), (key87, 6), (key84, -2), (key148, -2), (key87, -2), (key84, 2), (key148, 2), (key1, 2), (key184, 2), (key4, 2), (key148, 2), (key87, -2), (key4, -2), (key148, -2), (key87, 6), (key87, -2), (key4, -2), (key148, -2)]

def rawRow13475 : Integer.Sparse Key := [(key148, -2), (key84, -2), (key87, -2), (key87, 6), (key148, -2), (key84, -2), (key87, -2), (key148, 2), (key84, 2), (key184, 2), (key1, 2), (key148, 2), (key4, 2), (key87, -2), (key148, -2), (key4, -2), (key87, 6), (key87, -2), (key148, -2), (key4, -2)]

def rawRow13476 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key84, -2), (key87, 6), (key87, -2), (key148, -2), (key84, -2), (key164, 2), (key184, 2), (key4, 2), (key148, 2), (key1, 2), (key84, 2), (key148, -2), (key4, -2), (key87, -2), (key87, 6), (key148, -2), (key4, -2), (key87, -2)]

def rawRow13477 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key84, -2), (key87, 6), (key148, -2), (key87, -2), (key84, -2), (key184, 2), (key164, 2), (key148, 2), (key4, 2), (key84, 2), (key1, 2), (key148, -2), (key87, -2), (key4, -2), (key87, 6), (key148, -2), (key87, -2), (key4, -2)]

def rawRow13478 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key148, -2), (key84, 6), (key164, -2), (key164, -2), (key184, -2), (key4, 2), (key4, 2), (key87, 2), (key87, 2), (key148, 2), (key148, 2), (key1, -2), (key84, -2), (key84, -2), (key148, 6), (key4, -2), (key87, -2), (key87, -2)]

def rawRow13479 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key87, -2), (key84, 6), (key164, -2), (key184, -2), (key164, -2), (key87, 2), (key148, 2), (key4, 2), (key148, 2), (key4, 2), (key87, 2), (key84, -2), (key1, -2), (key84, -2), (key148, 6), (key87, -2), (key4, -2), (key87, -2)]

def rawRow13480 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key87, -2), (key84, 6), (key184, -2), (key164, -2), (key164, -2), (key148, 2), (key87, 2), (key148, 2), (key4, 2), (key87, 2), (key4, 2), (key84, -2), (key84, -2), (key1, -2), (key148, 6), (key87, -2), (key87, -2), (key4, -2)]

def rawRow13481 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key164, -2), (key184, 6), (key4, -2), (key4, -2), (key4, -2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key87, 2), (key148, -2), (key148, -2), (key148, -2), (key1, 6), (key84, -2), (key84, -2), (key84, -2)]

def rawRow13482 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key184, -2), (key164, 6), (key87, -2), (key87, -2), (key148, -2), (key4, 2), (key4, 2), (key87, 2), (key87, 2), (key148, 2), (key148, 2), (key4, -2), (key87, -2), (key87, -2), (key84, 6), (key1, -2), (key84, -2), (key84, -2)]

def rawRow13483 : Integer.Sparse Key := [(key164, -2), (key184, -2), (key164, -2), (key164, 6), (key87, -2), (key148, -2), (key87, -2), (key87, 2), (key148, 2), (key4, 2), (key148, 2), (key4, 2), (key87, 2), (key87, -2), (key4, -2), (key87, -2), (key84, 6), (key84, -2), (key1, -2), (key84, -2)]

def rawRow13484 : Integer.Sparse Key := [(key184, -2), (key164, -2), (key164, -2), (key164, 6), (key148, -2), (key87, -2), (key87, -2), (key148, 2), (key87, 2), (key148, 2), (key4, 2), (key87, 2), (key4, 2), (key87, -2), (key87, -2), (key4, -2), (key84, 6), (key84, -2), (key84, -2), (key1, -2)]

def rawRow13485 : Integer.Sparse Key := [(key982, 4), (key1222, 4), (key1222, 4), (key986, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key986, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key988, 4), (key1175, 4), (key1175, 4)]

def rawRow13486 : Integer.Sparse Key := [(key1222, 4), (key982, 4), (key1222, 4), (key1171, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1171, -2), (key1175, 4), (key988, 4), (key1175, 4)]

def rawRow13487 : Integer.Sparse Key := [(key1222, 4), (key1222, 4), (key982, 4), (key1224, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1171, -2), (key986, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1171, -2), (key986, -2), (key1175, 4), (key1175, 4), (key988, 4)]

def rawRow13488 : Integer.Sparse Key := [(key986, 4), (key1185, 4), (key1224, 4), (key982, -2), (key986, -2), (key1096, -2), (key1171, -2), (key1185, -2), (key1222, -2), (key986, -2), (key988, -2), (key1100, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key986, 4), (key1100, 4), (key1171, 4)]

def rawRow13489 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1185, 4), (key986, -2), (key982, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key988, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key1186, -2), (key986, 4), (key1171, 4), (key1100, 4)]

def rawRow13490 : Integer.Sparse Key := [(key1185, 4), (key986, 4), (key1224, 4), (key1096, -2), (key1185, -2), (key982, -2), (key1222, -2), (key986, -2), (key1171, -2), (key1100, -2), (key1186, -2), (key986, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1100, 4), (key986, 4), (key1171, 4)]

def rawRow13491 : Integer.Sparse Key := [(key1185, 4), (key1224, 4), (key986, 4), (key1185, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1171, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1175, -2), (key988, -2), (key1100, 4), (key1171, 4), (key986, 4)]

def rawRow13492 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1185, 4), (key1171, -2), (key1222, -2), (key986, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1175, -2), (key1224, -2), (key988, -2), (key1186, -2), (key986, -2), (key1100, -2), (key1171, 4), (key986, 4), (key1100, 4)]

def rawRow13493 : Integer.Sparse Key := [(key1224, 4), (key1185, 4), (key986, 4), (key1222, -2), (key1171, -2), (key1185, -2), (key986, -2), (key1096, -2), (key982, -2), (key1224, -2), (key1175, -2), (key1186, -2), (key988, -2), (key1100, -2), (key986, -2), (key1171, 4), (key1100, 4), (key986, 4)]

def rawRow13494 : Integer.Sparse Key := [(key986, 4), (key1185, 4), (key1224, 4), (key986, -2), (key988, -2), (key1100, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key982, -2), (key986, -2), (key1096, -2), (key1171, -2), (key1185, -2), (key1222, -2), (key986, 4), (key1100, 4), (key1171, 4)]

def rawRow13495 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1185, 4), (key988, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key1186, -2), (key986, -2), (key982, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key986, 4), (key1171, 4), (key1100, 4)]

def rawRow13496 : Integer.Sparse Key := [(key1185, 4), (key986, 4), (key1224, 4), (key1100, -2), (key1186, -2), (key986, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1096, -2), (key1185, -2), (key982, -2), (key1222, -2), (key986, -2), (key1171, -2), (key1100, 4), (key986, 4), (key1171, 4)]

def rawRow13497 : Integer.Sparse Key := [(key1185, 4), (key1224, 4), (key986, 4), (key1186, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1175, -2), (key988, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1171, -2), (key986, -2), (key1100, 4), (key1171, 4), (key986, 4)]

def rawRow13498 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1185, 4), (key1175, -2), (key1224, -2), (key988, -2), (key1186, -2), (key986, -2), (key1100, -2), (key1171, -2), (key1222, -2), (key986, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1171, 4), (key986, 4), (key1100, 4)]

def rawRow13499 : Integer.Sparse Key := [(key1224, 4), (key1185, 4), (key986, 4), (key1224, -2), (key1175, -2), (key1186, -2), (key988, -2), (key1100, -2), (key986, -2), (key1222, -2), (key1171, -2), (key1185, -2), (key986, -2), (key1096, -2), (key982, -2), (key1171, 4), (key1100, 4), (key986, 4)]

def rawRow13500 : Integer.Sparse Key := [(key988, 4), (key1186, 4), (key1186, 4), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key982, 4), (key1096, 4), (key1096, 4)]

def rawRow13501 : Integer.Sparse Key := [(key1186, 4), (key988, 4), (key1186, 4), (key1100, -2), (key1185, -2), (key986, -2), (key1185, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1185, -2), (key986, -2), (key1100, -2), (key1096, 4), (key982, 4), (key1096, 4)]

def rawRow13502 : Integer.Sparse Key := [(key1186, 4), (key1186, 4), (key988, 4), (key1185, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2), (key986, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, 4), (key1096, 4), (key982, 4)]

def rawRow13503 : Integer.Sparse Key := [(key88, -2), (key88, -2), (key156, -2), (key94, 6), (key88, -2), (key88, -2), (key156, -2), (key5, 2), (key9, 2), (key153, 2), (key153, 2), (key203, 2), (key203, 2), (key14, -2), (key161, -2), (key161, -2), (key97, 6), (key14, -2), (key161, -2), (key161, -2)]

def rawRow13504 : Integer.Sparse Key := [(key88, -2), (key156, -2), (key88, -2), (key94, 6), (key88, -2), (key156, -2), (key88, -2), (key165, 2), (key187, 2), (key5, 2), (key187, 2), (key9, 2), (key153, 2), (key161, -2), (key14, -2), (key161, -2), (key97, 6), (key161, -2), (key14, -2), (key161, -2)]

def rawRow13505 : Integer.Sparse Key := [(key156, -2), (key88, -2), (key88, -2), (key94, 6), (key156, -2), (key88, -2), (key88, -2), (key187, 2), (key165, 2), (key187, 2), (key5, 2), (key153, 2), (key9, 2), (key161, -2), (key161, -2), (key14, -2), (key97, 6), (key161, -2), (key161, -2), (key14, -2)]

def rawRow13506 : Integer.Sparse Key := [(key88, -2), (key94, -2), (key156, -2), (key88, 6), (key165, -2), (key167, -2), (key187, -2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key9, -2), (key92, -2), (key153, -2), (key161, 6), (key14, -2), (key97, -2), (key161, -2)]

def rawRow13507 : Integer.Sparse Key := [(key94, -2), (key88, -2), (key156, -2), (key88, 6), (key167, -2), (key165, -2), (key187, -2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key9, -2), (key153, -2), (key92, -2), (key161, 6), (key14, -2), (key161, -2), (key97, -2)]

def rawRow13508 : Integer.Sparse Key := [(key88, -2), (key156, -2), (key94, -2), (key88, 6), (key165, -2), (key187, -2), (key167, -2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key92, -2), (key9, -2), (key153, -2), (key161, 6), (key97, -2), (key14, -2), (key161, -2)]

def rawRow13509 : Integer.Sparse Key := [(key156, -2), (key88, -2), (key94, -2), (key88, 6), (key187, -2), (key165, -2), (key167, -2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key92, -2), (key153, -2), (key9, -2), (key161, 6), (key97, -2), (key161, -2), (key14, -2)]

def rawRow13510 : Integer.Sparse Key := [(key94, -2), (key156, -2), (key88, -2), (key88, 6), (key167, -2), (key187, -2), (key165, -2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key153, -2), (key9, -2), (key92, -2), (key161, 6), (key161, -2), (key14, -2), (key97, -2)]

def rawRow13511 : Integer.Sparse Key := [(key156, -2), (key94, -2), (key88, -2), (key88, 6), (key187, -2), (key167, -2), (key165, -2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key153, -2), (key92, -2), (key9, -2), (key161, 6), (key161, -2), (key97, -2), (key14, -2)]

def rawRow13512 : Integer.Sparse Key := [(key165, -2), (key167, -2), (key187, -2), (key167, 6), (key88, -2), (key94, -2), (key156, -2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key11, -2), (key94, -2), (key167, -2), (key92, 6), (key9, -2), (key92, -2), (key153, -2)]

def rawRow13513 : Integer.Sparse Key := [(key167, -2), (key165, -2), (key187, -2), (key167, 6), (key94, -2), (key88, -2), (key156, -2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key11, -2), (key167, -2), (key94, -2), (key92, 6), (key9, -2), (key153, -2), (key92, -2)]

def rawRow13514 : Integer.Sparse Key := [(key165, -2), (key187, -2), (key167, -2), (key167, 6), (key88, -2), (key156, -2), (key94, -2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key94, -2), (key11, -2), (key167, -2), (key92, 6), (key92, -2), (key9, -2), (key153, -2)]

def rawRow13515 : Integer.Sparse Key := [(key187, -2), (key165, -2), (key167, -2), (key167, 6), (key156, -2), (key88, -2), (key94, -2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key94, -2), (key167, -2), (key11, -2), (key92, 6), (key92, -2), (key153, -2), (key9, -2)]

def rawRow13516 : Integer.Sparse Key := [(key167, -2), (key187, -2), (key165, -2), (key167, 6), (key94, -2), (key156, -2), (key88, -2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key167, -2), (key11, -2), (key94, -2), (key92, 6), (key153, -2), (key9, -2), (key92, -2)]

def rawRow13517 : Integer.Sparse Key := [(key187, -2), (key167, -2), (key165, -2), (key167, 6), (key156, -2), (key94, -2), (key88, -2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key167, -2), (key94, -2), (key11, -2), (key92, 6), (key153, -2), (key92, -2), (key9, -2)]

def rawRow13518 : Integer.Sparse Key := [(key167, -2), (key167, -2), (key187, -2), (key165, 6), (key167, -2), (key167, -2), (key187, -2), (key11, 2), (key11, 2), (key94, 2), (key94, 2), (key156, 2), (key156, 2), (key5, -2), (key88, -2), (key88, -2), (key153, 6), (key9, -2), (key92, -2), (key92, -2)]

def rawRow13519 : Integer.Sparse Key := [(key167, -2), (key187, -2), (key167, -2), (key165, 6), (key167, -2), (key187, -2), (key167, -2), (key94, 2), (key156, 2), (key11, 2), (key156, 2), (key11, 2), (key94, 2), (key88, -2), (key5, -2), (key88, -2), (key153, 6), (key92, -2), (key9, -2), (key92, -2)]

def rawRow13520 : Integer.Sparse Key := [(key187, -2), (key167, -2), (key167, -2), (key165, 6), (key187, -2), (key167, -2), (key167, -2), (key156, 2), (key94, 2), (key156, 2), (key11, 2), (key94, 2), (key11, 2), (key88, -2), (key88, -2), (key5, -2), (key153, 6), (key92, -2), (key92, -2), (key9, -2)]

def rawRow13521 : Integer.Sparse Key := [(key1095, -2), (key1095, -2), (key1229, -2), (key1101, 6), (key1095, -2), (key1095, -2), (key1229, -2), (key981, 2), (key981, 2), (key1166, 2), (key1166, 2), (key1246, 2), (key1246, 2), (key987, -2), (key1173, -2), (key1173, -2), (key1101, 6), (key987, -2), (key1173, -2), (key1173, -2)]

def rawRow13522 : Integer.Sparse Key := [(key1095, -2), (key1229, -2), (key1095, -2), (key1101, 6), (key1095, -2), (key1229, -2), (key1095, -2), (key1166, 2), (key1246, 2), (key981, 2), (key1246, 2), (key981, 2), (key1166, 2), (key1173, -2), (key987, -2), (key1173, -2), (key1101, 6), (key1173, -2), (key987, -2), (key1173, -2)]

def rawRow13523 : Integer.Sparse Key := [(key1229, -2), (key1095, -2), (key1095, -2), (key1101, 6), (key1229, -2), (key1095, -2), (key1095, -2), (key1246, 2), (key1166, 2), (key1246, 2), (key981, 2), (key1166, 2), (key981, 2), (key1173, -2), (key1173, -2), (key987, -2), (key1101, 6), (key1173, -2), (key1173, -2), (key987, -2)]

def rawRow13524 : Integer.Sparse Key := [(key1095, -2), (key1101, -2), (key1229, -2), (key1095, 6), (key1166, -2), (key1173, -2), (key1246, -2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key981, -2), (key1095, -2), (key1166, -2), (key1173, 6), (key987, -2), (key1101, -2), (key1173, -2)]

def rawRow13525 : Integer.Sparse Key := [(key1101, -2), (key1095, -2), (key1229, -2), (key1095, 6), (key1173, -2), (key1166, -2), (key1246, -2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key981, -2), (key1166, -2), (key1095, -2), (key1173, 6), (key987, -2), (key1173, -2), (key1101, -2)]

def rawRow13526 : Integer.Sparse Key := [(key1095, -2), (key1229, -2), (key1101, -2), (key1095, 6), (key1166, -2), (key1246, -2), (key1173, -2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1095, -2), (key981, -2), (key1166, -2), (key1173, 6), (key1101, -2), (key987, -2), (key1173, -2)]

def rawRow13527 : Integer.Sparse Key := [(key1229, -2), (key1095, -2), (key1101, -2), (key1095, 6), (key1246, -2), (key1166, -2), (key1173, -2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1095, -2), (key1166, -2), (key981, -2), (key1173, 6), (key1101, -2), (key1173, -2), (key987, -2)]

def rawRow13528 : Integer.Sparse Key := [(key1101, -2), (key1229, -2), (key1095, -2), (key1095, 6), (key1173, -2), (key1246, -2), (key1166, -2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1166, -2), (key981, -2), (key1095, -2), (key1173, 6), (key1173, -2), (key987, -2), (key1101, -2)]

def rawRow13529 : Integer.Sparse Key := [(key1229, -2), (key1101, -2), (key1095, -2), (key1095, 6), (key1246, -2), (key1173, -2), (key1166, -2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1166, -2), (key1095, -2), (key981, -2), (key1173, 6), (key1173, -2), (key1101, -2), (key987, -2)]

def rawRow13530 : Integer.Sparse Key := [(key1166, -2), (key1173, -2), (key1246, -2), (key1173, 6), (key1095, -2), (key1101, -2), (key1229, -2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key987, -2), (key1101, -2), (key1173, -2), (key1095, 6), (key981, -2), (key1095, -2), (key1166, -2)]

def rawRow13531 : Integer.Sparse Key := [(key1173, -2), (key1166, -2), (key1246, -2), (key1173, 6), (key1101, -2), (key1095, -2), (key1229, -2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key987, -2), (key1173, -2), (key1101, -2), (key1095, 6), (key981, -2), (key1166, -2), (key1095, -2)]

def rawRow13532 : Integer.Sparse Key := [(key1166, -2), (key1246, -2), (key1173, -2), (key1173, 6), (key1095, -2), (key1229, -2), (key1101, -2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1101, -2), (key987, -2), (key1173, -2), (key1095, 6), (key1095, -2), (key981, -2), (key1166, -2)]

def rawRow13533 : Integer.Sparse Key := [(key1246, -2), (key1166, -2), (key1173, -2), (key1173, 6), (key1229, -2), (key1095, -2), (key1101, -2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1101, -2), (key1173, -2), (key987, -2), (key1095, 6), (key1095, -2), (key1166, -2), (key981, -2)]

def rawRow13534 : Integer.Sparse Key := [(key1173, -2), (key1246, -2), (key1166, -2), (key1173, 6), (key1101, -2), (key1229, -2), (key1095, -2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1173, -2), (key987, -2), (key1101, -2), (key1095, 6), (key1166, -2), (key981, -2), (key1095, -2)]

def rawRow13535 : Integer.Sparse Key := [(key1246, -2), (key1173, -2), (key1166, -2), (key1173, 6), (key1229, -2), (key1101, -2), (key1095, -2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1173, -2), (key1101, -2), (key987, -2), (key1095, 6), (key1166, -2), (key1095, -2), (key981, -2)]

def rawRow13536 : Integer.Sparse Key := [(key1173, -2), (key1173, -2), (key1246, -2), (key1166, 6), (key1173, -2), (key1173, -2), (key1246, -2), (key987, 2), (key987, 2), (key1101, 2), (key1101, 2), (key1229, 2), (key1229, 2), (key981, -2), (key1095, -2), (key1095, -2), (key1166, 6), (key981, -2), (key1095, -2), (key1095, -2)]

def rawRow13537 : Integer.Sparse Key := [(key1173, -2), (key1246, -2), (key1173, -2), (key1166, 6), (key1173, -2), (key1246, -2), (key1173, -2), (key1101, 2), (key1229, 2), (key987, 2), (key1229, 2), (key987, 2), (key1101, 2), (key1095, -2), (key981, -2), (key1095, -2), (key1166, 6), (key1095, -2), (key981, -2), (key1095, -2)]

def rawRow13538 : Integer.Sparse Key := [(key1246, -2), (key1173, -2), (key1173, -2), (key1166, 6), (key1246, -2), (key1173, -2), (key1173, -2), (key1229, 2), (key1101, 2), (key1229, 2), (key987, 2), (key1101, 2), (key987, 2), (key1095, -2), (key1095, -2), (key981, -2), (key1166, 6), (key1095, -2), (key1095, -2), (key981, -2)]

def rawRow13539 : Integer.Sparse Key := [(key1115, 6), (key1037, -2), (key1124, -2), (key1124, -2), (key1115, 6), (key1002, -2), (key1151, -2), (key1151, -2), (key1037, -2), (key1124, -2), (key1124, -2), (key1002, -2), (key1151, -2), (key1151, -2), (key1016, 2), (key1016, 2), (key1072, 2), (key1072, 2), (key1167, 2), (key1167, 2)]

def rawRow13540 : Integer.Sparse Key := [(key1115, 6), (key1124, -2), (key1037, -2), (key1124, -2), (key1115, 6), (key1151, -2), (key1002, -2), (key1151, -2), (key1124, -2), (key1037, -2), (key1124, -2), (key1151, -2), (key1002, -2), (key1151, -2), (key1072, 2), (key1167, 2), (key1016, 2), (key1167, 2), (key1016, 2), (key1072, 2)]

def rawRow13541 : Integer.Sparse Key := [(key1115, 6), (key1124, -2), (key1124, -2), (key1037, -2), (key1115, 6), (key1151, -2), (key1151, -2), (key1002, -2), (key1124, -2), (key1124, -2), (key1037, -2), (key1151, -2), (key1151, -2), (key1002, -2), (key1167, 2), (key1072, 2), (key1167, 2), (key1016, 2), (key1072, 2), (key1016, 2)]

def rawRow13542 : Integer.Sparse Key := [(key1124, 6), (key1037, -2), (key1115, -2), (key1124, -2), (key1151, 6), (key1002, -2), (key1115, -2), (key1151, -2), (key1072, -2), (key1151, -2), (key1167, -2), (key1016, -2), (key1124, -2), (key1167, -2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

def rawRow13543 : Integer.Sparse Key := [(key1124, 6), (key1037, -2), (key1124, -2), (key1115, -2), (key1151, 6), (key1002, -2), (key1151, -2), (key1115, -2), (key1072, -2), (key1167, -2), (key1151, -2), (key1016, -2), (key1167, -2), (key1124, -2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

def rawRow13544 : Integer.Sparse Key := [(key1124, 6), (key1115, -2), (key1037, -2), (key1124, -2), (key1151, 6), (key1115, -2), (key1002, -2), (key1151, -2), (key1151, -2), (key1072, -2), (key1167, -2), (key1124, -2), (key1016, -2), (key1167, -2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

def rawRow13545 : Integer.Sparse Key := [(key1124, 6), (key1115, -2), (key1124, -2), (key1037, -2), (key1151, 6), (key1115, -2), (key1151, -2), (key1002, -2), (key1151, -2), (key1167, -2), (key1072, -2), (key1124, -2), (key1167, -2), (key1016, -2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

def rawRow13546 : Integer.Sparse Key := [(key1124, 6), (key1124, -2), (key1037, -2), (key1115, -2), (key1151, 6), (key1151, -2), (key1002, -2), (key1115, -2), (key1167, -2), (key1072, -2), (key1151, -2), (key1167, -2), (key1016, -2), (key1124, -2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

def rawRow13547 : Integer.Sparse Key := [(key1124, 6), (key1124, -2), (key1115, -2), (key1037, -2), (key1151, 6), (key1151, -2), (key1115, -2), (key1002, -2), (key1167, -2), (key1151, -2), (key1072, -2), (key1167, -2), (key1124, -2), (key1016, -2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

def rawRow13548 : Integer.Sparse Key := [(key1151, 6), (key1072, -2), (key1151, -2), (key1167, -2), (key1124, 6), (key1016, -2), (key1124, -2), (key1167, -2), (key1037, -2), (key1115, -2), (key1124, -2), (key1002, -2), (key1115, -2), (key1151, -2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

def rawRow13549 : Integer.Sparse Key := [(key1151, 6), (key1072, -2), (key1167, -2), (key1151, -2), (key1124, 6), (key1016, -2), (key1167, -2), (key1124, -2), (key1037, -2), (key1124, -2), (key1115, -2), (key1002, -2), (key1151, -2), (key1115, -2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

def rawRow13550 : Integer.Sparse Key := [(key1151, 6), (key1151, -2), (key1072, -2), (key1167, -2), (key1124, 6), (key1124, -2), (key1016, -2), (key1167, -2), (key1115, -2), (key1037, -2), (key1124, -2), (key1115, -2), (key1002, -2), (key1151, -2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

def rawRow13551 : Integer.Sparse Key := [(key1151, 6), (key1151, -2), (key1167, -2), (key1072, -2), (key1124, 6), (key1124, -2), (key1167, -2), (key1016, -2), (key1115, -2), (key1124, -2), (key1037, -2), (key1115, -2), (key1151, -2), (key1002, -2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

def rawRow13552 : Integer.Sparse Key := [(key1151, 6), (key1167, -2), (key1072, -2), (key1151, -2), (key1124, 6), (key1167, -2), (key1016, -2), (key1124, -2), (key1124, -2), (key1037, -2), (key1115, -2), (key1151, -2), (key1002, -2), (key1115, -2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

def rawRow13553 : Integer.Sparse Key := [(key1151, 6), (key1167, -2), (key1151, -2), (key1072, -2), (key1124, 6), (key1167, -2), (key1124, -2), (key1016, -2), (key1124, -2), (key1115, -2), (key1037, -2), (key1151, -2), (key1115, -2), (key1002, -2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

def rawRow13554 : Integer.Sparse Key := [(key1167, 6), (key1072, -2), (key1151, -2), (key1151, -2), (key1167, 6), (key1016, -2), (key1124, -2), (key1124, -2), (key1072, -2), (key1151, -2), (key1151, -2), (key1016, -2), (key1124, -2), (key1124, -2), (key1002, 2), (key1002, 2), (key1037, 2), (key1037, 2), (key1115, 2), (key1115, 2)]

def rawRow13555 : Integer.Sparse Key := [(key1167, 6), (key1151, -2), (key1072, -2), (key1151, -2), (key1167, 6), (key1124, -2), (key1016, -2), (key1124, -2), (key1151, -2), (key1072, -2), (key1151, -2), (key1124, -2), (key1016, -2), (key1124, -2), (key1037, 2), (key1115, 2), (key1002, 2), (key1115, 2), (key1002, 2), (key1037, 2)]

def rawRow13556 : Integer.Sparse Key := [(key1167, 6), (key1151, -2), (key1151, -2), (key1072, -2), (key1167, 6), (key1124, -2), (key1124, -2), (key1016, -2), (key1151, -2), (key1151, -2), (key1072, -2), (key1124, -2), (key1124, -2), (key1016, -2), (key1115, 2), (key1037, 2), (key1115, 2), (key1002, 2), (key1037, 2), (key1002, 2)]

def rawRow13557 : Integer.Sparse Key := [(key92, -2), (key92, -2), (key168, -2), (key95, 6), (key92, -2), (key92, -2), (key168, -2), (key9, 2), (key9, 2), (key153, 2), (key153, 2), (key188, 2), (key188, 2), (key12, -2), (key157, -2), (key157, -2), (key95, 6), (key12, -2), (key157, -2), (key157, -2)]

def rawRow13558 : Integer.Sparse Key := [(key92, -2), (key168, -2), (key92, -2), (key95, 6), (key92, -2), (key168, -2), (key92, -2), (key153, 2), (key188, 2), (key9, 2), (key188, 2), (key9, 2), (key153, 2), (key157, -2), (key12, -2), (key157, -2), (key95, 6), (key157, -2), (key12, -2), (key157, -2)]

def rawRow13559 : Integer.Sparse Key := [(key168, -2), (key92, -2), (key92, -2), (key95, 6), (key168, -2), (key92, -2), (key92, -2), (key188, 2), (key153, 2), (key188, 2), (key9, 2), (key153, 2), (key9, 2), (key157, -2), (key157, -2), (key12, -2), (key95, 6), (key157, -2), (key157, -2), (key12, -2)]

def rawRow13560 : Integer.Sparse Key := [(key92, -2), (key95, -2), (key168, -2), (key92, 6), (key153, -2), (key157, -2), (key188, -2), (key9, 2), (key12, 2), (key92, 2), (key157, 2), (key168, 2), (key188, 2), (key9, -2), (key92, -2), (key153, -2), (key157, 6), (key12, -2), (key95, -2), (key157, -2)]

def rawRow13561 : Integer.Sparse Key := [(key95, -2), (key92, -2), (key168, -2), (key92, 6), (key157, -2), (key153, -2), (key188, -2), (key12, 2), (key9, 2), (key157, 2), (key92, 2), (key188, 2), (key168, 2), (key9, -2), (key153, -2), (key92, -2), (key157, 6), (key12, -2), (key157, -2), (key95, -2)]

def rawRow13562 : Integer.Sparse Key := [(key92, -2), (key168, -2), (key95, -2), (key92, 6), (key153, -2), (key188, -2), (key157, -2), (key92, 2), (key168, 2), (key9, 2), (key188, 2), (key12, 2), (key157, 2), (key92, -2), (key9, -2), (key153, -2), (key157, 6), (key95, -2), (key12, -2), (key157, -2)]

def rawRow13563 : Integer.Sparse Key := [(key168, -2), (key92, -2), (key95, -2), (key92, 6), (key188, -2), (key153, -2), (key157, -2), (key168, 2), (key92, 2), (key188, 2), (key9, 2), (key157, 2), (key12, 2), (key92, -2), (key153, -2), (key9, -2), (key157, 6), (key95, -2), (key157, -2), (key12, -2)]

def rawRow13564 : Integer.Sparse Key := [(key95, -2), (key168, -2), (key92, -2), (key92, 6), (key157, -2), (key188, -2), (key153, -2), (key157, 2), (key188, 2), (key12, 2), (key168, 2), (key9, 2), (key92, 2), (key153, -2), (key9, -2), (key92, -2), (key157, 6), (key157, -2), (key12, -2), (key95, -2)]

def rawRow13565 : Integer.Sparse Key := [(key168, -2), (key95, -2), (key92, -2), (key92, 6), (key188, -2), (key157, -2), (key153, -2), (key188, 2), (key157, 2), (key168, 2), (key12, 2), (key92, 2), (key9, 2), (key153, -2), (key92, -2), (key9, -2), (key157, 6), (key157, -2), (key95, -2), (key12, -2)]

def rawRow13566 : Integer.Sparse Key := [(key153, -2), (key157, -2), (key188, -2), (key157, 6), (key92, -2), (key95, -2), (key168, -2), (key9, 2), (key12, 2), (key92, 2), (key157, 2), (key168, 2), (key188, 2), (key12, -2), (key95, -2), (key157, -2), (key92, 6), (key9, -2), (key92, -2), (key153, -2)]

def rawRow13567 : Integer.Sparse Key := [(key157, -2), (key153, -2), (key188, -2), (key157, 6), (key95, -2), (key92, -2), (key168, -2), (key12, 2), (key9, 2), (key157, 2), (key92, 2), (key188, 2), (key168, 2), (key12, -2), (key157, -2), (key95, -2), (key92, 6), (key9, -2), (key153, -2), (key92, -2)]

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

def rawRow13568 : Integer.Sparse Key := [(key153, -2), (key188, -2), (key157, -2), (key157, 6), (key92, -2), (key168, -2), (key95, -2), (key92, 2), (key168, 2), (key9, 2), (key188, 2), (key12, 2), (key157, 2), (key95, -2), (key12, -2), (key157, -2), (key92, 6), (key92, -2), (key9, -2), (key153, -2)]

def rawRow13569 : Integer.Sparse Key := [(key188, -2), (key153, -2), (key157, -2), (key157, 6), (key168, -2), (key92, -2), (key95, -2), (key168, 2), (key92, 2), (key188, 2), (key9, 2), (key157, 2), (key12, 2), (key95, -2), (key157, -2), (key12, -2), (key92, 6), (key92, -2), (key153, -2), (key9, -2)]

def rawRow13570 : Integer.Sparse Key := [(key157, -2), (key188, -2), (key153, -2), (key157, 6), (key95, -2), (key168, -2), (key92, -2), (key157, 2), (key188, 2), (key12, 2), (key168, 2), (key9, 2), (key92, 2), (key157, -2), (key12, -2), (key95, -2), (key92, 6), (key153, -2), (key9, -2), (key92, -2)]

def rawRow13571 : Integer.Sparse Key := [(key188, -2), (key157, -2), (key153, -2), (key157, 6), (key168, -2), (key95, -2), (key92, -2), (key188, 2), (key157, 2), (key168, 2), (key12, 2), (key92, 2), (key9, 2), (key157, -2), (key95, -2), (key12, -2), (key92, 6), (key153, -2), (key92, -2), (key9, -2)]

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

def rawRow18454 : Integer.Sparse Key := [(key0, 24), (key83, 24), (key83, 24), (key83, 24), (key83, 24)]

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

def rawRow1287 : Integer.Sparse Key := [(key445, -1), (key435, -1), (key661, -1), (key316, -1), (key660, -1), (key321, -1), (key453, 2), (key662, 2), (key331, 2), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1), (key661, -1), (key657, -1), (key662, -1), (key655, -1), (key658, -1), (key656, -1), (key321, -2), (key331, -2), (key307, -2), (key445, 1), (key411, 1), (key453, 1), (key390, 1), (key421, 1), (key400, 1)]

def rawRow1288 : Integer.Sparse Key := [(key660, -1), (key661, -1), (key321, -1), (key445, -1), (key316, -1), (key435, -1), (key662, 2), (key331, 2), (key453, 2), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1), (key658, -1), (key662, -1), (key656, -1), (key661, -1), (key655, -1), (key657, -1), (key331, -2), (key307, -2), (key321, -2), (key421, 1), (key453, 1), (key400, 1), (key445, 1), (key390, 1), (key411, 1)]

def rawRow1289 : Integer.Sparse Key := [(key661, -1), (key660, -1), (key445, -1), (key321, -1), (key435, -1), (key316, -1), (key662, 2), (key453, 2), (key331, 2), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1), (key662, -1), (key658, -1), (key661, -1), (key656, -1), (key657, -1), (key655, -1), (key331, -2), (key321, -2), (key307, -2), (key453, 1), (key421, 1), (key445, 1), (key400, 1), (key411, 1), (key390, 1)]

def rawRow1290 : Integer.Sparse Key := [(key1433, -2), (key1439, -2), (key1439, -2), (key1477, 2), (key1479, 2), (key1479, 2), (key1582, 2), (key1588, 2), (key1588, 2), (key1688, -6), (key1908, -2), (key1910, -2), (key1910, -2), (key1925, 6)]

def rawRow1291 : Integer.Sparse Key := [(key1439, -2), (key1433, -2), (key1439, -2), (key1479, 2), (key1477, 2), (key1479, 2), (key1588, 2), (key1582, 2), (key1588, 2), (key1688, -6), (key1910, -2), (key1908, -2), (key1910, -2), (key1925, 6)]

def rawRow1292 : Integer.Sparse Key := [(key1439, -2), (key1439, -2), (key1433, -2), (key1479, 2), (key1479, 2), (key1477, 2), (key1588, 2), (key1588, 2), (key1582, 2), (key1688, -6), (key1910, -2), (key1910, -2), (key1908, -2), (key1925, 6)]

def rawRow1293 : Integer.Sparse Key := [(key1405, -2), (key1414, -2), (key1479, -2), (key1410, 2), (key1414, 2), (key1439, 2), (key1582, 2), (key1588, 2), (key1688, 2), (key1588, -6), (key1908, -2), (key1910, -2), (key1925, -2), (key1910, 6)]

def rawRow1294 : Integer.Sparse Key := [(key1414, -2), (key1405, -2), (key1479, -2), (key1414, 2), (key1410, 2), (key1439, 2), (key1588, 2), (key1582, 2), (key1688, 2), (key1588, -6), (key1910, -2), (key1908, -2), (key1925, -2), (key1910, 6)]

def rawRow1295 : Integer.Sparse Key := [(key1405, -2), (key1479, -2), (key1414, -2), (key1410, 2), (key1439, 2), (key1414, 2), (key1582, 2), (key1688, 2), (key1588, 2), (key1588, -6), (key1908, -2), (key1925, -2), (key1910, -2), (key1910, 6)]

def rawRow1296 : Integer.Sparse Key := [(key1479, -2), (key1405, -2), (key1414, -2), (key1439, 2), (key1410, 2), (key1414, 2), (key1688, 2), (key1582, 2), (key1588, 2), (key1588, -6), (key1925, -2), (key1908, -2), (key1910, -2), (key1910, 6)]

def rawRow1297 : Integer.Sparse Key := [(key1414, -2), (key1479, -2), (key1405, -2), (key1414, 2), (key1439, 2), (key1410, 2), (key1588, 2), (key1688, 2), (key1582, 2), (key1588, -6), (key1910, -2), (key1925, -2), (key1908, -2), (key1910, 6)]

def rawRow1298 : Integer.Sparse Key := [(key1479, -2), (key1414, -2), (key1405, -2), (key1439, 2), (key1414, 2), (key1410, 2), (key1688, 2), (key1588, 2), (key1582, 2), (key1588, -6), (key1925, -2), (key1910, -2), (key1908, -2), (key1910, 6)]

def rawRow1299 : Integer.Sparse Key := [(key1582, -2), (key1588, -2), (key1588, -2), (key1908, 2), (key1910, 2), (key1910, 2), (key1433, 2), (key1439, 2), (key1439, 2), (key1925, -6), (key1477, -2), (key1479, -2), (key1479, -2), (key1688, 6)]

def rawRow1300 : Integer.Sparse Key := [(key1588, -2), (key1582, -2), (key1588, -2), (key1910, 2), (key1908, 2), (key1910, 2), (key1439, 2), (key1433, 2), (key1439, 2), (key1925, -6), (key1479, -2), (key1477, -2), (key1479, -2), (key1688, 6)]

def rawRow1301 : Integer.Sparse Key := [(key1588, -2), (key1588, -2), (key1582, -2), (key1910, 2), (key1910, 2), (key1908, 2), (key1439, 2), (key1439, 2), (key1433, 2), (key1925, -6), (key1479, -2), (key1479, -2), (key1477, -2), (key1688, 6)]

def rawRow1302 : Integer.Sparse Key := [(key1405, -2), (key1414, -2), (key1910, -2), (key1410, 2), (key1414, 2), (key1588, 2), (key1433, 2), (key1439, 2), (key1925, 2), (key1439, -6), (key1477, -2), (key1479, -2), (key1688, -2), (key1479, 6)]

def rawRow1303 : Integer.Sparse Key := [(key1414, -2), (key1405, -2), (key1910, -2), (key1414, 2), (key1410, 2), (key1588, 2), (key1439, 2), (key1433, 2), (key1925, 2), (key1439, -6), (key1479, -2), (key1477, -2), (key1688, -2), (key1479, 6)]

def rawRow1304 : Integer.Sparse Key := [(key1405, -2), (key1910, -2), (key1414, -2), (key1410, 2), (key1588, 2), (key1414, 2), (key1433, 2), (key1925, 2), (key1439, 2), (key1439, -6), (key1477, -2), (key1688, -2), (key1479, -2), (key1479, 6)]

def rawRow1305 : Integer.Sparse Key := [(key1910, -2), (key1405, -2), (key1414, -2), (key1588, 2), (key1410, 2), (key1414, 2), (key1925, 2), (key1433, 2), (key1439, 2), (key1439, -6), (key1688, -2), (key1477, -2), (key1479, -2), (key1479, 6)]

def rawRow1306 : Integer.Sparse Key := [(key1414, -2), (key1910, -2), (key1405, -2), (key1414, 2), (key1588, 2), (key1410, 2), (key1439, 2), (key1925, 2), (key1433, 2), (key1439, -6), (key1479, -2), (key1688, -2), (key1477, -2), (key1479, 6)]

def rawRow1307 : Integer.Sparse Key := [(key1910, -2), (key1414, -2), (key1405, -2), (key1588, 2), (key1414, 2), (key1410, 2), (key1925, 2), (key1439, 2), (key1433, 2), (key1439, -6), (key1688, -2), (key1479, -2), (key1477, -2), (key1479, 6)]

def rawRow1308 : Integer.Sparse Key := [(key1582, -2), (key1588, -2), (key1688, -2), (key1908, 2), (key1910, 2), (key1925, 2), (key1405, 2), (key1414, 2), (key1479, 2), (key1910, -6), (key1410, -2), (key1414, -2), (key1439, -2), (key1588, 6)]

def rawRow1309 : Integer.Sparse Key := [(key1588, -2), (key1582, -2), (key1688, -2), (key1910, 2), (key1908, 2), (key1925, 2), (key1414, 2), (key1405, 2), (key1479, 2), (key1910, -6), (key1414, -2), (key1410, -2), (key1439, -2), (key1588, 6)]

def rawRow1310 : Integer.Sparse Key := [(key1582, -2), (key1688, -2), (key1588, -2), (key1908, 2), (key1925, 2), (key1910, 2), (key1405, 2), (key1479, 2), (key1414, 2), (key1910, -6), (key1410, -2), (key1439, -2), (key1414, -2), (key1588, 6)]

def rawRow1311 : Integer.Sparse Key := [(key1688, -2), (key1582, -2), (key1588, -2), (key1925, 2), (key1908, 2), (key1910, 2), (key1479, 2), (key1405, 2), (key1414, 2), (key1910, -6), (key1439, -2), (key1410, -2), (key1414, -2), (key1588, 6)]

def rawRow1312 : Integer.Sparse Key := [(key1588, -2), (key1688, -2), (key1582, -2), (key1910, 2), (key1925, 2), (key1908, 2), (key1414, 2), (key1479, 2), (key1405, 2), (key1910, -6), (key1414, -2), (key1439, -2), (key1410, -2), (key1588, 6)]

def rawRow1313 : Integer.Sparse Key := [(key1688, -2), (key1588, -2), (key1582, -2), (key1925, 2), (key1910, 2), (key1908, 2), (key1479, 2), (key1414, 2), (key1405, 2), (key1910, -6), (key1439, -2), (key1414, -2), (key1410, -2), (key1588, 6)]

def rawRow1314 : Integer.Sparse Key := [(key1433, -2), (key1439, -2), (key1925, -2), (key1477, 2), (key1479, 2), (key1688, 2), (key1405, 2), (key1414, 2), (key1910, 2), (key1479, -6), (key1410, -2), (key1414, -2), (key1588, -2), (key1439, 6)]

def rawRow1315 : Integer.Sparse Key := [(key1439, -2), (key1433, -2), (key1925, -2), (key1479, 2), (key1477, 2), (key1688, 2), (key1414, 2), (key1405, 2), (key1910, 2), (key1479, -6), (key1414, -2), (key1410, -2), (key1588, -2), (key1439, 6)]

def rawRow1316 : Integer.Sparse Key := [(key1433, -2), (key1925, -2), (key1439, -2), (key1477, 2), (key1688, 2), (key1479, 2), (key1405, 2), (key1910, 2), (key1414, 2), (key1479, -6), (key1410, -2), (key1588, -2), (key1414, -2), (key1439, 6)]

def rawRow1317 : Integer.Sparse Key := [(key1925, -2), (key1433, -2), (key1439, -2), (key1688, 2), (key1477, 2), (key1479, 2), (key1910, 2), (key1405, 2), (key1414, 2), (key1479, -6), (key1588, -2), (key1410, -2), (key1414, -2), (key1439, 6)]

def rawRow1318 : Integer.Sparse Key := [(key1439, -2), (key1925, -2), (key1433, -2), (key1479, 2), (key1688, 2), (key1477, 2), (key1414, 2), (key1910, 2), (key1405, 2), (key1479, -6), (key1414, -2), (key1588, -2), (key1410, -2), (key1439, 6)]

def rawRow1319 : Integer.Sparse Key := [(key1925, -2), (key1439, -2), (key1433, -2), (key1688, 2), (key1479, 2), (key1477, 2), (key1910, 2), (key1414, 2), (key1405, 2), (key1479, -6), (key1588, -2), (key1414, -2), (key1410, -2), (key1439, 6)]

def rawRow1320 : Integer.Sparse Key := [(key236, -2), (key241, -2), (key241, -2), (key248, 1), (key253, 1), (key248, 1), (key263, 1), (key253, 1), (key263, 1), (key302, 2), (key307, 2), (key307, 2), (key316, -1), (key321, -1), (key316, -1), (key331, -1), (key321, -1), (key331, -1), (key385, -1), (key390, -1), (key385, -1), (key400, -1), (key390, -1), (key400, -1), (key406, 1), (key411, 1), (key406, 1), (key421, 1), (key411, 1), (key421, 1)]

def rawRow1321 : Integer.Sparse Key := [(key241, -2), (key236, -2), (key241, -2), (key253, 1), (key248, 1), (key263, 1), (key248, 1), (key263, 1), (key253, 1), (key307, 2), (key302, 2), (key307, 2), (key321, -1), (key316, -1), (key331, -1), (key316, -1), (key331, -1), (key321, -1), (key390, -1), (key385, -1), (key400, -1), (key385, -1), (key400, -1), (key390, -1), (key411, 1), (key406, 1), (key421, 1), (key406, 1), (key421, 1), (key411, 1)]

def rawRow1322 : Integer.Sparse Key := [(key241, -2), (key241, -2), (key236, -2), (key263, 1), (key263, 1), (key253, 1), (key253, 1), (key248, 1), (key248, 1), (key307, 2), (key307, 2), (key302, 2), (key331, -1), (key331, -1), (key321, -1), (key321, -1), (key316, -1), (key316, -1), (key400, -1), (key400, -1), (key390, -1), (key390, -1), (key385, -1), (key385, -1), (key421, 1), (key421, 1), (key411, 1), (key411, 1), (key406, 1), (key406, 1)]

def rawRow1323 : Integer.Sparse Key := [(key248, -2), (key253, -2), (key263, -2), (key236, 1), (key241, 1), (key248, 1), (key263, 1), (key277, 1), (key278, 1), (key316, 2), (key321, 2), (key346, 2), (key302, -1), (key307, -1), (key316, -1), (key331, -1), (key346, -1), (key347, -1), (key406, -1), (key411, -1), (key435, -1), (key445, -1), (key487, -1), (key488, -1), (key385, 1), (key390, 1), (key435, 1), (key453, 1), (key487, 1), (key489, 1)]

def rawRow1324 : Integer.Sparse Key := [(key253, -2), (key248, -2), (key263, -2), (key241, 1), (key236, 1), (key263, 1), (key248, 1), (key278, 1), (key277, 1), (key321, 2), (key316, 2), (key346, 2), (key307, -1), (key302, -1), (key331, -1), (key316, -1), (key347, -1), (key346, -1), (key411, -1), (key406, -1), (key445, -1), (key435, -1), (key488, -1), (key487, -1), (key390, 1), (key385, 1), (key453, 1), (key435, 1), (key489, 1), (key487, 1)]

def rawRow1325 : Integer.Sparse Key := [(key248, -2), (key263, -2), (key253, -2), (key248, 1), (key263, 1), (key236, 1), (key278, 1), (key241, 1), (key263, 1), (key316, 2), (key346, 2), (key321, 2), (key316, -1), (key346, -1), (key302, -1), (key347, -1), (key307, -1), (key331, -1), (key435, -1), (key487, -1), (key406, -1), (key488, -1), (key411, -1), (key445, -1), (key435, 1), (key487, 1), (key385, 1), (key489, 1), (key390, 1), (key453, 1)]

def rawRow1326 : Integer.Sparse Key := [(key263, -2), (key248, -2), (key253, -2), (key263, 1), (key248, 1), (key278, 1), (key236, 1), (key263, 1), (key241, 1), (key346, 2), (key316, 2), (key321, 2), (key346, -1), (key316, -1), (key347, -1), (key302, -1), (key331, -1), (key307, -1), (key487, -1), (key435, -1), (key488, -1), (key406, -1), (key445, -1), (key411, -1), (key487, 1), (key435, 1), (key489, 1), (key385, 1), (key453, 1), (key390, 1)]

def rawRow1327 : Integer.Sparse Key := [(key253, -2), (key263, -2), (key248, -2), (key277, 1), (key278, 1), (key241, 1), (key263, 1), (key236, 1), (key248, 1), (key321, 2), (key346, 2), (key316, 2), (key331, -1), (key347, -1), (key307, -1), (key346, -1), (key302, -1), (key316, -1), (key445, -1), (key488, -1), (key411, -1), (key487, -1), (key406, -1), (key435, -1), (key453, 1), (key489, 1), (key390, 1), (key487, 1), (key385, 1), (key435, 1)]

def rawRow1328 : Integer.Sparse Key := [(key263, -2), (key253, -2), (key248, -2), (key278, 1), (key277, 1), (key263, 1), (key241, 1), (key248, 1), (key236, 1), (key346, 2), (key321, 2), (key316, 2), (key347, -1), (key331, -1), (key346, -1), (key307, -1), (key316, -1), (key302, -1), (key488, -1), (key445, -1), (key487, -1), (key411, -1), (key435, -1), (key406, -1), (key489, 1), (key453, 1), (key487, 1), (key390, 1), (key435, 1), (key385, 1)]

def rawRow1329 : Integer.Sparse Key := [(key302, -2), (key307, -2), (key307, -2), (key316, 1), (key321, 1), (key316, 1), (key346, 1), (key321, 1), (key346, 1), (key236, 2), (key241, 2), (key241, 2), (key406, -1), (key411, -1), (key406, -1), (key421, -1), (key411, -1), (key421, -1), (key248, -1), (key253, -1), (key248, -1), (key263, -1), (key253, -1), (key263, -1), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1)]

def rawRow1330 : Integer.Sparse Key := [(key307, -2), (key302, -2), (key307, -2), (key321, 1), (key316, 1), (key346, 1), (key316, 1), (key346, 1), (key321, 1), (key241, 2), (key236, 2), (key241, 2), (key411, -1), (key406, -1), (key421, -1), (key406, -1), (key421, -1), (key411, -1), (key253, -1), (key248, -1), (key263, -1), (key248, -1), (key263, -1), (key253, -1), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1)]

def rawRow1331 : Integer.Sparse Key := [(key307, -2), (key307, -2), (key302, -2), (key346, 1), (key346, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key241, 2), (key241, 2), (key236, 2), (key421, -1), (key421, -1), (key411, -1), (key411, -1), (key406, -1), (key406, -1), (key263, -1), (key263, -1), (key253, -1), (key253, -1), (key248, -1), (key248, -1), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1)]

def rawRow1332 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key302, 1), (key307, 1), (key316, 1), (key346, 1), (key331, 1), (key347, 1), (key406, 2), (key411, 2), (key421, 2), (key236, -1), (key241, -1), (key406, -1), (key421, -1), (key657, -1), (key658, -1), (key316, -1), (key321, -1), (key435, -1), (key445, -1), (key660, -1), (key661, -1), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1)]

def rawRow1333 : Integer.Sparse Key := [(key321, -2), (key316, -2), (key331, -2), (key307, 1), (key302, 1), (key346, 1), (key316, 1), (key347, 1), (key331, 1), (key411, 2), (key406, 2), (key421, 2), (key241, -1), (key236, -1), (key421, -1), (key406, -1), (key658, -1), (key657, -1), (key321, -1), (key316, -1), (key445, -1), (key435, -1), (key661, -1), (key660, -1), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1)]

def rawRow1334 : Integer.Sparse Key := [(key316, -2), (key331, -2), (key321, -2), (key316, 1), (key331, 1), (key302, 1), (key347, 1), (key307, 1), (key346, 1), (key406, 2), (key421, 2), (key411, 2), (key406, -1), (key421, -1), (key236, -1), (key658, -1), (key241, -1), (key421, -1), (key435, -1), (key660, -1), (key316, -1), (key661, -1), (key321, -1), (key445, -1), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1)]

def rawRow1335 : Integer.Sparse Key := [(key331, -2), (key316, -2), (key321, -2), (key331, 1), (key316, 1), (key347, 1), (key302, 1), (key346, 1), (key307, 1), (key421, 2), (key406, 2), (key411, 2), (key421, -1), (key406, -1), (key658, -1), (key236, -1), (key421, -1), (key241, -1), (key660, -1), (key435, -1), (key661, -1), (key316, -1), (key445, -1), (key321, -1), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1)]

def rawRow1336 : Integer.Sparse Key := [(key321, -2), (key331, -2), (key316, -2), (key346, 1), (key347, 1), (key307, 1), (key331, 1), (key302, 1), (key316, 1), (key411, 2), (key421, 2), (key406, 2), (key657, -1), (key658, -1), (key241, -1), (key421, -1), (key236, -1), (key406, -1), (key445, -1), (key661, -1), (key321, -1), (key660, -1), (key316, -1), (key435, -1), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1)]

def rawRow1337 : Integer.Sparse Key := [(key331, -2), (key321, -2), (key316, -2), (key347, 1), (key346, 1), (key331, 1), (key307, 1), (key316, 1), (key302, 1), (key421, 2), (key411, 2), (key406, 2), (key658, -1), (key657, -1), (key421, -1), (key241, -1), (key406, -1), (key236, -1), (key661, -1), (key445, -1), (key660, -1), (key321, -1), (key435, -1), (key316, -1), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1)]

def rawRow1338 : Integer.Sparse Key := [(key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key435, 1), (key487, 1), (key445, 1), (key488, 1), (key248, 2), (key253, 2), (key263, 2), (key316, -1), (key321, -1), (key435, -1), (key660, -1), (key445, -1), (key661, -1), (key236, -1), (key241, -1), (key248, -1), (key263, -1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1)]

def rawRow1339 : Integer.Sparse Key := [(key390, -2), (key385, -2), (key400, -2), (key411, 1), (key406, 1), (key487, 1), (key435, 1), (key488, 1), (key445, 1), (key253, 2), (key248, 2), (key263, 2), (key321, -1), (key316, -1), (key660, -1), (key435, -1), (key661, -1), (key445, -1), (key241, -1), (key236, -1), (key263, -1), (key248, -1), (key278, -1), (key277, -1), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1)]

def rawRow1340 : Integer.Sparse Key := [(key385, -2), (key400, -2), (key390, -2), (key435, 1), (key445, 1), (key406, 1), (key488, 1), (key411, 1), (key487, 1), (key248, 2), (key263, 2), (key253, 2), (key435, -1), (key445, -1), (key316, -1), (key661, -1), (key321, -1), (key660, -1), (key248, -1), (key263, -1), (key236, -1), (key278, -1), (key241, -1), (key263, -1), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1)]

def rawRow1341 : Integer.Sparse Key := [(key400, -2), (key385, -2), (key390, -2), (key445, 1), (key435, 1), (key488, 1), (key406, 1), (key487, 1), (key411, 1), (key263, 2), (key248, 2), (key253, 2), (key445, -1), (key435, -1), (key661, -1), (key316, -1), (key660, -1), (key321, -1), (key263, -1), (key248, -1), (key278, -1), (key236, -1), (key263, -1), (key241, -1), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1)]

def rawRow1342 : Integer.Sparse Key := [(key390, -2), (key400, -2), (key385, -2), (key487, 1), (key488, 1), (key411, 1), (key445, 1), (key406, 1), (key435, 1), (key253, 2), (key263, 2), (key248, 2), (key660, -1), (key661, -1), (key321, -1), (key445, -1), (key316, -1), (key435, -1), (key277, -1), (key278, -1), (key241, -1), (key263, -1), (key236, -1), (key248, -1), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1)]

def rawRow1343 : Integer.Sparse Key := [(key400, -2), (key390, -2), (key385, -2), (key488, 1), (key487, 1), (key445, 1), (key411, 1), (key435, 1), (key406, 1), (key263, 2), (key253, 2), (key248, 2), (key661, -1), (key660, -1), (key445, -1), (key321, -1), (key435, -1), (key316, -1), (key278, -1), (key277, -1), (key263, -1), (key241, -1), (key248, -1), (key236, -1), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1)]

def rawRow1344 : Integer.Sparse Key := [(key406, -2), (key411, -2), (key421, -2), (key385, 1), (key390, 1), (key435, 1), (key487, 1), (key453, 1), (key489, 1), (key316, 2), (key321, 2), (key331, 2), (key248, -1), (key253, -1), (key435, -1), (key660, -1), (key453, -1), (key662, -1), (key302, -1), (key307, -1), (key316, -1), (key346, -1), (key331, -1), (key347, -1), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1)]

def rawRow1345 : Integer.Sparse Key := [(key411, -2), (key406, -2), (key421, -2), (key390, 1), (key385, 1), (key487, 1), (key435, 1), (key489, 1), (key453, 1), (key321, 2), (key316, 2), (key331, 2), (key253, -1), (key248, -1), (key660, -1), (key435, -1), (key662, -1), (key453, -1), (key307, -1), (key302, -1), (key346, -1), (key316, -1), (key347, -1), (key331, -1), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1)]

def rawRow1346 : Integer.Sparse Key := [(key406, -2), (key421, -2), (key411, -2), (key435, 1), (key453, 1), (key385, 1), (key489, 1), (key390, 1), (key487, 1), (key316, 2), (key331, 2), (key321, 2), (key435, -1), (key453, -1), (key248, -1), (key662, -1), (key253, -1), (key660, -1), (key316, -1), (key331, -1), (key302, -1), (key347, -1), (key307, -1), (key346, -1), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1)]

def rawRow1347 : Integer.Sparse Key := [(key421, -2), (key406, -2), (key411, -2), (key453, 1), (key435, 1), (key489, 1), (key385, 1), (key487, 1), (key390, 1), (key331, 2), (key316, 2), (key321, 2), (key453, -1), (key435, -1), (key662, -1), (key248, -1), (key660, -1), (key253, -1), (key331, -1), (key316, -1), (key347, -1), (key302, -1), (key346, -1), (key307, -1), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1)]

def rawRow1348 : Integer.Sparse Key := [(key411, -2), (key421, -2), (key406, -2), (key487, 1), (key489, 1), (key390, 1), (key453, 1), (key385, 1), (key435, 1), (key321, 2), (key331, 2), (key316, 2), (key660, -1), (key662, -1), (key253, -1), (key453, -1), (key248, -1), (key435, -1), (key346, -1), (key347, -1), (key307, -1), (key331, -1), (key302, -1), (key316, -1), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1)]

def rawRow1349 : Integer.Sparse Key := [(key421, -2), (key411, -2), (key406, -2), (key489, 1), (key487, 1), (key453, 1), (key390, 1), (key435, 1), (key385, 1), (key331, 2), (key321, 2), (key316, 2), (key662, -1), (key660, -1), (key453, -1), (key253, -1), (key435, -1), (key248, -1), (key347, -1), (key346, -1), (key331, -1), (key307, -1), (key316, -1), (key302, -1), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1)]

def rawRow1350 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1033, 1), (key1040, 1), (key1033, 1), (key1075, 1), (key1040, 1), (key1075, 1), (key1111, 2), (key1111, 2), (key1154, 2), (key1111, -1), (key1126, -1), (key1111, -1), (key1154, -1), (key1126, -1), (key1154, -1), (key1190, -1), (key1192, -1), (key1190, -1), (key1211, -1), (key1192, -1), (key1211, -1), (key1190, 1), (key1198, 1), (key1190, 1), (key1211, 1), (key1198, 1), (key1211, 1)]

def rawRow1351 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 1), (key1033, 1), (key1075, 1), (key1033, 1), (key1075, 1), (key1040, 1), (key1111, 2), (key1154, 2), (key1111, 2), (key1126, -1), (key1111, -1), (key1154, -1), (key1111, -1), (key1154, -1), (key1126, -1), (key1192, -1), (key1190, -1), (key1211, -1), (key1190, -1), (key1211, -1), (key1192, -1), (key1198, 1), (key1190, 1), (key1211, 1), (key1190, 1), (key1211, 1), (key1198, 1)]

def rawRow1352 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1075, 1), (key1075, 1), (key1040, 1), (key1040, 1), (key1033, 1), (key1033, 1), (key1154, 2), (key1111, 2), (key1111, 2), (key1154, -1), (key1154, -1), (key1126, -1), (key1126, -1), (key1111, -1), (key1111, -1), (key1211, -1), (key1211, -1), (key1192, -1), (key1192, -1), (key1190, -1), (key1190, -1), (key1211, 1), (key1211, 1), (key1198, 1), (key1198, 1), (key1190, 1), (key1190, 1)]

def rawRow1353 : Integer.Sparse Key := [(key1040, -2), (key1040, -2), (key1040, -2), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1126, 2), (key1126, 2), (key1126, 2), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1192, 1), (key1192, 1), (key1192, 1), (key1192, 1), (key1192, 1), (key1192, 1)]

def rawRow1354 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1190, 1), (key1192, 1), (key1190, 1), (key1211, 1), (key1192, 1), (key1211, 1), (key1033, 2), (key1033, 2), (key1075, 2), (key1190, -1), (key1198, -1), (key1190, -1), (key1211, -1), (key1198, -1), (key1211, -1), (key1033, -1), (key1040, -1), (key1033, -1), (key1075, -1), (key1040, -1), (key1075, -1), (key1111, 1), (key1126, 1), (key1111, 1), (key1154, 1), (key1126, 1), (key1154, 1)]

def rawRow1355 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1192, 1), (key1190, 1), (key1211, 1), (key1190, 1), (key1211, 1), (key1192, 1), (key1033, 2), (key1075, 2), (key1033, 2), (key1198, -1), (key1190, -1), (key1211, -1), (key1190, -1), (key1211, -1), (key1198, -1), (key1040, -1), (key1033, -1), (key1075, -1), (key1033, -1), (key1075, -1), (key1040, -1), (key1126, 1), (key1111, 1), (key1154, 1), (key1111, 1), (key1154, 1), (key1126, 1)]

def rawRow1356 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1211, 1), (key1211, 1), (key1192, 1), (key1192, 1), (key1190, 1), (key1190, 1), (key1075, 2), (key1033, 2), (key1033, 2), (key1211, -1), (key1211, -1), (key1198, -1), (key1198, -1), (key1190, -1), (key1190, -1), (key1075, -1), (key1075, -1), (key1040, -1), (key1040, -1), (key1033, -1), (key1033, -1), (key1154, 1), (key1154, 1), (key1126, 1), (key1126, 1), (key1111, 1), (key1111, 1)]

def rawRow1357 : Integer.Sparse Key := [(key1005, -2), (key1192, -2), (key1192, -2), (key998, 1), (key998, 1), (key1111, 1), (key1111, 1), (key1190, 1), (key1190, 1), (key1018, 2), (key1198, 2), (key1198, 2), (key998, -1), (key998, -1), (key1033, -1), (key1033, -1), (key1190, -1), (key1190, -1), (key1018, -1), (key1018, -1), (key1126, -1), (key1126, -1), (key1198, -1), (key1198, -1), (key1005, 1), (key1005, 1), (key1040, 1), (key1040, 1), (key1192, 1), (key1192, 1)]

end MUB6.Certificate.GramRows

end OAI
end


