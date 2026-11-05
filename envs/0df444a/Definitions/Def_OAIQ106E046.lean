-- Prove2me | Definitions.Def_OAIQ106E046
-- name    : OAIQ106E046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:59:16.069283+00:00
-- url     : https://prove2.me/theorems/bf55ca28-8c48-4cf3-91fb-7e9435216bc8
-- title:
--   Definitions bundle OAIQ106E046 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1937 declarations of OpenAI's Lean: 1937 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow1300`, `OAI.MUB6.Certificate.GramRows.rawRow13000`, `OAI.MUB6.Certificate.GramRows.rawRow13001`, `OAI.MUB6.Certificate.GramRows.rawRow13002`, `OAI.MUB6.Certificate.GramRows.rawRow13003`, `OAI.MUB6.Certificate.GramRows.rawRow13004`, `OAI.MUB6.Certificate.GramRows.rawRow13005`, `OAI.MUB6.Certificate.GramRows.rawRow13006`, `OAI.MUB6.Certificate.GramRows.rawRow13007`, `OAI.MUB6.Certificate.GramRows.rawRow13008`, `OAI.MUB6.Certificate.GramRows.rawRow13009`, `OAI.MUB6.Certificate.GramRows.rawRow1301`, `OAI.MUB6.Certificate.GramRows.rawRow13010`, `OAI.MUB6.Certificate.GramRows.rawRow13011`, `OAI.MUB6.Certificate.GramRows.rawRow13012`, `OAI.MUB6.Certificate.GramRows.rawRow13013`, `OAI.MUB6.Certificate.GramRows.rawRow13014`, `OAI.MUB6.Certificate.GramRows.rawRow13015`, `OAI.MUB6.Certificate.GramRows.rawRow13016`, `OAI.MUB6.Certificate.GramRows.rawRow13017`, `OAI.MUB6.Certificate.GramRows.rawRow13018`, `OAI.MUB6.Certificate.GramRows.rawRow13019`, `OAI.MUB6.Certificate.GramRows.rawRow1302`, `OAI.MUB6.Certificate.GramRows.rawRow13020`, `OAI.MUB6.Certificate.GramRows.rawRow13021`, `OAI.MUB6.Certificate.GramRows.rawRow13022`, `OAI.MUB6.Certificate.GramRows.rawRow13023`, `OAI.MUB6.Certificate.GramRows.rawRow13024`, `OAI.MUB6.Certificate.GramRows.rawRow13025`, `OAI.MUB6.Certificate.GramRows.rawRow13026`, `OAI.MUB6.Certificate.GramRows.rawRow13027`, `OAI.MUB6.Certificate.GramRows.rawRow13028`, `OAI.MUB6.Certificate.GramRows.rawRow13029`, `OAI.MUB6.Certificate.GramRows.rawRow1303`, `OAI.MUB6.Certificate.GramRows.rawRow13030`, `OAI.MUB6.Certificate.GramRows.rawRow13031`, `OAI.MUB6.Certificate.GramRows.rawRow13032`, `OAI.MUB6.Certificate.GramRows.rawRow13033`, `OAI.MUB6.Certificate.GramRows.rawRow13034`, `OAI.MUB6.Certificate.GramRows.rawRow13035` and 1897 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block125`, `MutuallyUnbiased_GramRows_Block126`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block128`, `MutuallyUnbiased_GramRows_Block129`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block133`, `MutuallyUnbiased_GramRows_Block134`, `MutuallyUnbiased_GramRows_Block135`, `MutuallyUnbiased_GramRows_Block136`, `MutuallyUnbiased_GramRows_Block137`, `MutuallyUnbiased_GramRows_Block138`, `MutuallyUnbiased_GramRows_Block139`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block34`, `MutuallyUnbiased_GramRows_Block35`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14 : Integer.Sparse Key := [(key319, -1), (key316, -1), (key328, 2), (key305, 1), (key302, 1), (key340, -1), (key328, -1), (key305, -2), (key335, 1), (key319, 1), (key409, 1), (key406, 1), (key418, -2), (key239, -1), (key236, -1), (key583, 1), (key578, 1), (key239, 2), (key418, -1), (key409, -1), (key319, -1), (key316, -1), (key595, 1), (key593, 1), (key251, 1), (key248, 1), (key601, -1), (key593, -1), (key260, -1), (key251, -1), (key328, 1), (key319, 1), (key335, 2), (key469, -1), (key467, -1), (key267, -2), (key475, 1), (key467, 1), (key271, 1), (key267, 1), (key340, -1), (key335, -1)]

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

def rawRow131 : Integer.Sparse Key := [(key1318, -1), (key1326, -1), (key1312, 2), (key1351, 1), (key1354, 1), (key1292, -1), (key1312, -1), (key1351, -2), (key1298, 1), (key1318, 1), (key1548, 1), (key1556, 1), (key1542, -2), (key1896, -1), (key1899, -1), (key1387, 1), (key1542, 1), (key1896, 2), (key1393, -1), (key1548, -1), (key1681, -1), (key1683, -1), (key1569, 1), (key1618, 1), (key1918, 1), (key1920, 1), (key1420, -1), (key1618, -1), (key1903, -1), (key1918, -1), (key1472, 1), (key1681, 1), (key1689, 2), (key1593, -1), (key1633, -1), (key1926, -2), (key1444, 1), (key1633, 1), (key1911, 1), (key1926, 1), (key1480, -1), (key1689, -1)]

def rawRow132 : Integer.Sparse Key := [(key1326, -1), (key1318, -1), (key1312, 2), (key1354, 1), (key1351, 1), (key1312, -1), (key1292, -1), (key1351, -2), (key1318, 1), (key1298, 1), (key1556, 1), (key1548, 1), (key1542, -2), (key1899, -1), (key1896, -1), (key1542, 1), (key1387, 1), (key1896, 2), (key1548, -1), (key1393, -1), (key1683, -1), (key1681, -1), (key1618, 1), (key1569, 1), (key1920, 1), (key1918, 1), (key1618, -1), (key1420, -1), (key1918, -1), (key1903, -1), (key1681, 1), (key1472, 1), (key1689, 2), (key1633, -1), (key1593, -1), (key1926, -2), (key1633, 1), (key1444, 1), (key1926, 1), (key1911, 1), (key1689, -1), (key1480, -1)]

def rawRow133 : Integer.Sparse Key := [(key1351, -1), (key1351, -1), (key1354, 2), (key1298, 1), (key1298, 1), (key1326, -1), (key1326, -1), (key1292, -2), (key1312, 1), (key1312, 1), (key1896, 1), (key1896, 1), (key1899, -2), (key1393, -1), (key1393, -1), (key1556, 1), (key1556, 1), (key1387, 2), (key1542, -1), (key1542, -1), (key1903, -1), (key1903, -1), (key1920, 1), (key1920, 1), (key1472, 1), (key1472, 1), (key1683, -1), (key1683, -1), (key1420, -1), (key1420, -1), (key1569, 1), (key1569, 1), (key1911, 2), (key1926, -1), (key1926, -1), (key1480, -2), (key1689, 1), (key1689, 1), (key1444, 1), (key1444, 1), (key1593, -1), (key1593, -1)]

def rawRow134 : Integer.Sparse Key := [(key1351, -1), (key1354, -1), (key1351, 2), (key1318, 1), (key1326, 1), (key1298, -1), (key1318, -1), (key1312, -2), (key1292, 1), (key1312, 1), (key1896, 1), (key1899, 1), (key1896, -2), (key1548, -1), (key1556, -1), (key1393, 1), (key1548, 1), (key1542, 2), (key1387, -1), (key1542, -1), (key1918, -1), (key1920, -1), (key1903, 1), (key1918, 1), (key1681, 1), (key1683, 1), (key1472, -1), (key1681, -1), (key1569, -1), (key1618, -1), (key1420, 1), (key1618, 1), (key1926, 2), (key1911, -1), (key1926, -1), (key1689, -2), (key1480, 1), (key1689, 1), (key1593, 1), (key1633, 1), (key1444, -1), (key1633, -1)]

def rawRow135 : Integer.Sparse Key := [(key1354, -1), (key1351, -1), (key1351, 2), (key1326, 1), (key1318, 1), (key1318, -1), (key1298, -1), (key1312, -2), (key1312, 1), (key1292, 1), (key1899, 1), (key1896, 1), (key1896, -2), (key1556, -1), (key1548, -1), (key1548, 1), (key1393, 1), (key1542, 2), (key1542, -1), (key1387, -1), (key1920, -1), (key1918, -1), (key1918, 1), (key1903, 1), (key1683, 1), (key1681, 1), (key1681, -1), (key1472, -1), (key1618, -1), (key1569, -1), (key1618, 1), (key1420, 1), (key1926, 2), (key1926, -1), (key1911, -1), (key1689, -2), (key1689, 1), (key1480, 1), (key1633, 1), (key1593, 1), (key1633, -1), (key1444, -1)]

def rawRow136 : Integer.Sparse Key := [(key1387, -1), (key1393, -1), (key1393, 2), (key1420, 1), (key1426, 1), (key1426, -1), (key1472, -1), (key1444, -2), (key1444, 1), (key1480, 1), (key1292, 1), (key1298, 1), (key1298, -2), (key1569, -1), (key1575, -1), (key1575, 1), (key1903, 1), (key1593, 2), (key1593, -1), (key1911, -1), (key1312, -1), (key1318, -1), (key1318, 1), (key1351, 1), (key1542, 1), (key1548, 1), (key1548, -1), (key1896, -1), (key1633, -1), (key1689, -1), (key1633, 1), (key1926, 1), (key1326, 2), (key1326, -1), (key1354, -1), (key1556, -2), (key1556, 1), (key1899, 1), (key1624, 1), (key1683, 1), (key1624, -1), (key1920, -1)]

def rawRow137 : Integer.Sparse Key := [(key1393, -1), (key1387, -1), (key1393, 2), (key1426, 1), (key1420, 1), (key1472, -1), (key1426, -1), (key1444, -2), (key1480, 1), (key1444, 1), (key1298, 1), (key1292, 1), (key1298, -2), (key1575, -1), (key1569, -1), (key1903, 1), (key1575, 1), (key1593, 2), (key1911, -1), (key1593, -1), (key1318, -1), (key1312, -1), (key1351, 1), (key1318, 1), (key1548, 1), (key1542, 1), (key1896, -1), (key1548, -1), (key1689, -1), (key1633, -1), (key1926, 1), (key1633, 1), (key1326, 2), (key1354, -1), (key1326, -1), (key1556, -2), (key1899, 1), (key1556, 1), (key1683, 1), (key1624, 1), (key1920, -1), (key1624, -1)]

def rawRow138 : Integer.Sparse Key := [(key1393, -1), (key1393, -1), (key1387, 2), (key1472, 1), (key1472, 1), (key1420, -1), (key1420, -1), (key1480, -2), (key1444, 1), (key1444, 1), (key1298, 1), (key1298, 1), (key1292, -2), (key1903, -1), (key1903, -1), (key1569, 1), (key1569, 1), (key1911, 2), (key1593, -1), (key1593, -1), (key1351, -1), (key1351, -1), (key1312, 1), (key1312, 1), (key1896, 1), (key1896, 1), (key1542, -1), (key1542, -1), (key1926, -1), (key1926, -1), (key1689, 1), (key1689, 1), (key1354, 2), (key1326, -1), (key1326, -1), (key1899, -2), (key1556, 1), (key1556, 1), (key1920, 1), (key1920, 1), (key1683, -1), (key1683, -1)]

def rawRow139 : Integer.Sparse Key := [(key1420, -1), (key1426, -1), (key1444, 2), (key1387, 1), (key1393, 1), (key1444, -1), (key1480, -1), (key1393, -2), (key1426, 1), (key1472, 1), (key1569, 1), (key1575, 1), (key1593, -2), (key1292, -1), (key1298, -1), (key1593, 1), (key1911, 1), (key1298, 2), (key1575, -1), (key1903, -1), (key1542, -1), (key1548, -1), (key1633, 1), (key1689, 1), (key1312, 1), (key1318, 1), (key1633, -1), (key1926, -1), (key1318, -1), (key1351, -1), (key1548, 1), (key1896, 1), (key1556, 2), (key1624, -1), (key1683, -1), (key1326, -2), (key1624, 1), (key1920, 1), (key1326, 1), (key1354, 1), (key1556, -1), (key1899, -1)]

def rawRow140 : Integer.Sparse Key := [(key1426, -1), (key1420, -1), (key1444, 2), (key1393, 1), (key1387, 1), (key1480, -1), (key1444, -1), (key1393, -2), (key1472, 1), (key1426, 1), (key1575, 1), (key1569, 1), (key1593, -2), (key1298, -1), (key1292, -1), (key1911, 1), (key1593, 1), (key1298, 2), (key1903, -1), (key1575, -1), (key1548, -1), (key1542, -1), (key1689, 1), (key1633, 1), (key1318, 1), (key1312, 1), (key1926, -1), (key1633, -1), (key1351, -1), (key1318, -1), (key1896, 1), (key1548, 1), (key1556, 2), (key1683, -1), (key1624, -1), (key1326, -2), (key1920, 1), (key1624, 1), (key1354, 1), (key1326, 1), (key1899, -1), (key1556, -1)]

def rawRow141 : Integer.Sparse Key := [(key1426, -1), (key1444, -1), (key1420, 2), (key1472, 1), (key1480, 1), (key1387, -1), (key1420, -1), (key1472, -2), (key1393, 1), (key1426, 1), (key1575, 1), (key1593, 1), (key1569, -2), (key1903, -1), (key1911, -1), (key1292, 1), (key1569, 1), (key1903, 2), (key1298, -1), (key1575, -1), (key1681, -1), (key1689, -1), (key1542, 1), (key1618, 1), (key1918, 1), (key1926, 1), (key1312, -1), (key1618, -1), (key1896, -1), (key1918, -1), (key1351, 1), (key1681, 1), (key1683, 2), (key1556, -1), (key1624, -1), (key1920, -2), (key1326, 1), (key1624, 1), (key1899, 1), (key1920, 1), (key1354, -1), (key1683, -1)]

def rawRow142 : Integer.Sparse Key := [(key1444, -1), (key1426, -1), (key1420, 2), (key1480, 1), (key1472, 1), (key1420, -1), (key1387, -1), (key1472, -2), (key1426, 1), (key1393, 1), (key1593, 1), (key1575, 1), (key1569, -2), (key1911, -1), (key1903, -1), (key1569, 1), (key1292, 1), (key1903, 2), (key1575, -1), (key1298, -1), (key1689, -1), (key1681, -1), (key1618, 1), (key1542, 1), (key1926, 1), (key1918, 1), (key1618, -1), (key1312, -1), (key1918, -1), (key1896, -1), (key1681, 1), (key1351, 1), (key1683, 2), (key1624, -1), (key1556, -1), (key1920, -2), (key1624, 1), (key1326, 1), (key1920, 1), (key1899, 1), (key1683, -1), (key1354, -1)]

def rawRow143 : Integer.Sparse Key := [(key1472, -1), (key1472, -1), (key1480, 2), (key1393, 1), (key1393, 1), (key1444, -1), (key1444, -1), (key1387, -2), (key1420, 1), (key1420, 1), (key1903, 1), (key1903, 1), (key1911, -2), (key1298, -1), (key1298, -1), (key1593, 1), (key1593, 1), (key1292, 2), (key1569, -1), (key1569, -1), (key1896, -1), (key1896, -1), (key1926, 1), (key1926, 1), (key1351, 1), (key1351, 1), (key1689, -1), (key1689, -1), (key1312, -1), (key1312, -1), (key1542, 1), (key1542, 1), (key1899, 2), (key1920, -1), (key1920, -1), (key1354, -2), (key1683, 1), (key1683, 1), (key1326, 1), (key1326, 1), (key1556, -1), (key1556, -1)]

def rawRow144 : Integer.Sparse Key := [(key1472, -1), (key1480, -1), (key1472, 2), (key1426, 1), (key1444, 1), (key1393, -1), (key1426, -1), (key1420, -2), (key1387, 1), (key1420, 1), (key1903, 1), (key1911, 1), (key1903, -2), (key1575, -1), (key1593, -1), (key1298, 1), (key1575, 1), (key1569, 2), (key1292, -1), (key1569, -1), (key1918, -1), (key1926, -1), (key1896, 1), (key1918, 1), (key1681, 1), (key1689, 1), (key1351, -1), (key1681, -1), (key1542, -1), (key1618, -1), (key1312, 1), (key1618, 1), (key1920, 2), (key1899, -1), (key1920, -1), (key1683, -2), (key1354, 1), (key1683, 1), (key1556, 1), (key1624, 1), (key1326, -1), (key1624, -1)]

def rawRow145 : Integer.Sparse Key := [(key1480, -1), (key1472, -1), (key1472, 2), (key1444, 1), (key1426, 1), (key1426, -1), (key1393, -1), (key1420, -2), (key1420, 1), (key1387, 1), (key1911, 1), (key1903, 1), (key1903, -2), (key1593, -1), (key1575, -1), (key1575, 1), (key1298, 1), (key1569, 2), (key1569, -1), (key1292, -1), (key1926, -1), (key1918, -1), (key1918, 1), (key1896, 1), (key1689, 1), (key1681, 1), (key1681, -1), (key1351, -1), (key1618, -1), (key1542, -1), (key1618, 1), (key1312, 1), (key1920, 2), (key1920, -1), (key1899, -1), (key1683, -2), (key1683, 1), (key1354, 1), (key1624, 1), (key1556, 1), (key1624, -1), (key1326, -1)]

def rawRow146 : Integer.Sparse Key := [(key1542, -1), (key1548, -1), (key1556, 2), (key1569, 1), (key1575, 1), (key1624, -1), (key1683, -1), (key1593, -2), (key1633, 1), (key1689, 1), (key1312, 1), (key1318, 1), (key1326, -2), (key1420, -1), (key1426, -1), (key1624, 1), (key1920, 1), (key1444, 2), (key1633, -1), (key1926, -1), (key1292, -1), (key1298, -1), (key1326, 1), (key1354, 1), (key1387, 1), (key1393, 1), (key1556, -1), (key1899, -1), (key1444, -1), (key1480, -1), (key1593, 1), (key1911, 1), (key1298, 2), (key1318, -1), (key1351, -1), (key1393, -2), (key1548, 1), (key1896, 1), (key1426, 1), (key1472, 1), (key1575, -1), (key1903, -1)]

def rawRow147 : Integer.Sparse Key := [(key1548, -1), (key1542, -1), (key1556, 2), (key1575, 1), (key1569, 1), (key1683, -1), (key1624, -1), (key1593, -2), (key1689, 1), (key1633, 1), (key1318, 1), (key1312, 1), (key1326, -2), (key1426, -1), (key1420, -1), (key1920, 1), (key1624, 1), (key1444, 2), (key1926, -1), (key1633, -1), (key1298, -1), (key1292, -1), (key1354, 1), (key1326, 1), (key1393, 1), (key1387, 1), (key1899, -1), (key1556, -1), (key1480, -1), (key1444, -1), (key1911, 1), (key1593, 1), (key1298, 2), (key1351, -1), (key1318, -1), (key1393, -2), (key1896, 1), (key1548, 1), (key1472, 1), (key1426, 1), (key1903, -1), (key1575, -1)]

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

def rawRow13572 : Integer.Sparse Key := [(key157, -2), (key157, -2), (key188, -2), (key153, 6), (key157, -2), (key157, -2), (key188, -2), (key12, 2), (key12, 2), (key95, 2), (key95, 2), (key168, 2), (key168, 2), (key9, -2), (key92, -2), (key92, -2), (key153, 6), (key9, -2), (key92, -2), (key92, -2)]

def rawRow13573 : Integer.Sparse Key := [(key157, -2), (key188, -2), (key157, -2), (key153, 6), (key157, -2), (key188, -2), (key157, -2), (key95, 2), (key168, 2), (key12, 2), (key168, 2), (key12, 2), (key95, 2), (key92, -2), (key9, -2), (key92, -2), (key153, 6), (key92, -2), (key9, -2), (key92, -2)]

def rawRow13574 : Integer.Sparse Key := [(key188, -2), (key157, -2), (key157, -2), (key153, 6), (key188, -2), (key157, -2), (key157, -2), (key168, 2), (key95, 2), (key168, 2), (key12, 2), (key95, 2), (key12, 2), (key92, -2), (key92, -2), (key9, -2), (key153, 6), (key92, -2), (key92, -2), (key9, -2)]

def rawRow13575 : Integer.Sparse Key := [(key10, 4), (key189, 4), (key189, 4), (key13, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key192, -2), (key13, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key192, -2), (key15, 4), (key163, 4), (key163, 4)]

def rawRow13576 : Integer.Sparse Key := [(key189, 4), (key10, 4), (key189, 4), (key158, -2), (key192, -2), (key13, -2), (key192, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key13, -2), (key192, -2), (key13, -2), (key158, -2), (key163, 4), (key15, 4), (key163, 4)]

def rawRow13577 : Integer.Sparse Key := [(key189, 4), (key189, 4), (key10, 4), (key192, -2), (key158, -2), (key192, -2), (key13, -2), (key158, -2), (key13, -2), (key192, -2), (key158, -2), (key192, -2), (key13, -2), (key158, -2), (key13, -2), (key163, 4), (key163, 4), (key15, 4)]

def rawRow13578 : Integer.Sparse Key := [(key13, 4), (key158, 4), (key192, 4), (key10, -2), (key13, -2), (key93, -2), (key158, -2), (key169, -2), (key189, -2), (key13, -2), (key15, -2), (key96, -2), (key163, -2), (key170, -2), (key192, -2), (key13, 4), (key96, 4), (key158, 4)]

def rawRow13579 : Integer.Sparse Key := [(key13, 4), (key192, 4), (key158, 4), (key13, -2), (key10, -2), (key158, -2), (key93, -2), (key189, -2), (key169, -2), (key15, -2), (key13, -2), (key163, -2), (key96, -2), (key192, -2), (key170, -2), (key13, 4), (key158, 4), (key96, 4)]

def rawRow13580 : Integer.Sparse Key := [(key158, 4), (key13, 4), (key192, 4), (key93, -2), (key158, -2), (key10, -2), (key189, -2), (key13, -2), (key158, -2), (key96, -2), (key170, -2), (key13, -2), (key192, -2), (key15, -2), (key163, -2), (key96, 4), (key13, 4), (key158, 4)]

def rawRow13581 : Integer.Sparse Key := [(key158, 4), (key192, 4), (key13, 4), (key158, -2), (key93, -2), (key189, -2), (key10, -2), (key158, -2), (key13, -2), (key170, -2), (key96, -2), (key192, -2), (key13, -2), (key163, -2), (key15, -2), (key96, 4), (key158, 4), (key13, 4)]

def rawRow13582 : Integer.Sparse Key := [(key192, 4), (key13, 4), (key158, 4), (key169, -2), (key189, -2), (key13, -2), (key158, -2), (key10, -2), (key93, -2), (key163, -2), (key192, -2), (key15, -2), (key170, -2), (key13, -2), (key96, -2), (key158, 4), (key13, 4), (key96, 4)]

def rawRow13583 : Integer.Sparse Key := [(key192, 4), (key158, 4), (key13, 4), (key189, -2), (key169, -2), (key158, -2), (key13, -2), (key93, -2), (key10, -2), (key192, -2), (key163, -2), (key170, -2), (key15, -2), (key96, -2), (key13, -2), (key158, 4), (key96, 4), (key13, 4)]

def rawRow13584 : Integer.Sparse Key := [(key13, 4), (key158, 4), (key192, 4), (key13, -2), (key15, -2), (key96, -2), (key170, -2), (key163, -2), (key192, -2), (key10, -2), (key13, -2), (key93, -2), (key158, -2), (key169, -2), (key189, -2), (key13, 4), (key96, 4), (key158, 4)]

def rawRow13585 : Integer.Sparse Key := [(key13, 4), (key192, 4), (key158, 4), (key15, -2), (key13, -2), (key170, -2), (key96, -2), (key192, -2), (key163, -2), (key13, -2), (key10, -2), (key158, -2), (key93, -2), (key189, -2), (key169, -2), (key13, 4), (key158, 4), (key96, 4)]

def rawRow13586 : Integer.Sparse Key := [(key158, 4), (key13, 4), (key192, 4), (key96, -2), (key163, -2), (key13, -2), (key192, -2), (key15, -2), (key170, -2), (key93, -2), (key158, -2), (key10, -2), (key189, -2), (key13, -2), (key158, -2), (key96, 4), (key13, 4), (key158, 4)]

def rawRow13587 : Integer.Sparse Key := [(key158, 4), (key192, 4), (key13, 4), (key163, -2), (key96, -2), (key192, -2), (key13, -2), (key170, -2), (key15, -2), (key158, -2), (key93, -2), (key189, -2), (key10, -2), (key158, -2), (key13, -2), (key96, 4), (key158, 4), (key13, 4)]

def rawRow13588 : Integer.Sparse Key := [(key192, 4), (key13, 4), (key158, 4), (key170, -2), (key192, -2), (key15, -2), (key163, -2), (key13, -2), (key96, -2), (key169, -2), (key189, -2), (key13, -2), (key158, -2), (key10, -2), (key93, -2), (key158, 4), (key13, 4), (key96, 4)]

def rawRow13589 : Integer.Sparse Key := [(key192, 4), (key158, 4), (key13, 4), (key192, -2), (key170, -2), (key163, -2), (key15, -2), (key96, -2), (key13, -2), (key189, -2), (key169, -2), (key158, -2), (key13, -2), (key93, -2), (key10, -2), (key158, 4), (key96, 4), (key13, 4)]

def rawRow13590 : Integer.Sparse Key := [(key15, 4), (key163, 4), (key163, 4), (key13, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key13, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key10, 4), (key93, 4), (key93, 4)]

def rawRow13591 : Integer.Sparse Key := [(key163, 4), (key15, 4), (key163, 4), (key96, -2), (key158, -2), (key13, -2), (key158, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key13, -2), (key158, -2), (key13, -2), (key96, -2), (key93, 4), (key10, 4), (key93, 4)]

def rawRow13592 : Integer.Sparse Key := [(key163, 4), (key163, 4), (key15, 4), (key158, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2), (key13, -2), (key158, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2), (key13, -2), (key93, 4), (key93, 4), (key10, 4)]

def rawRow13593 : Integer.Sparse Key := [(key2587, 4), (key2966, 4), (key2989, 4), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow13594 : Integer.Sparse Key := [(key2587, 4), (key2989, 4), (key2966, 4), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow13595 : Integer.Sparse Key := [(key2966, 4), (key2587, 4), (key2989, 4), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow13596 : Integer.Sparse Key := [(key2966, 4), (key2989, 4), (key2587, 4), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow13597 : Integer.Sparse Key := [(key2989, 4), (key2587, 4), (key2966, 4), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow13598 : Integer.Sparse Key := [(key2989, 4), (key2966, 4), (key2587, 4), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow13599 : Integer.Sparse Key := [(key2593, 4), (key2968, 4), (key2968, 4), (key2587, -2), (key2587, -2), (key2843, -2), (key2843, -2), (key2966, -2), (key2966, -2), (key2600, -2), (key2600, -2), (key2889, -2), (key2889, -2), (key2995, -2), (key2995, -2), (key2598, 4), (key2887, 4), (key2887, 4)]

def rawRow13600 : Integer.Sparse Key := [(key2968, 4), (key2593, 4), (key2968, 4), (key2843, -2), (key2966, -2), (key2587, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2887, 4), (key2598, 4), (key2887, 4)]

def rawRow13601 : Integer.Sparse Key := [(key2968, 4), (key2968, 4), (key2593, 4), (key2966, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2587, -2), (key2995, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2600, -2), (key2887, 4), (key2887, 4), (key2598, 4)]

def rawRow13602 : Integer.Sparse Key := [(key2587, 4), (key2966, 4), (key2989, 4), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow13603 : Integer.Sparse Key := [(key2587, 4), (key2989, 4), (key2966, 4), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow13604 : Integer.Sparse Key := [(key2966, 4), (key2587, 4), (key2989, 4), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow13605 : Integer.Sparse Key := [(key2966, 4), (key2989, 4), (key2587, 4), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow13606 : Integer.Sparse Key := [(key2989, 4), (key2587, 4), (key2966, 4), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow13607 : Integer.Sparse Key := [(key2989, 4), (key2966, 4), (key2587, 4), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow13608 : Integer.Sparse Key := [(key2390, 4), (key2929, 4), (key3002, 4), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2593, 4), (key2772, 4), (key2880, 4)]

def rawRow13609 : Integer.Sparse Key := [(key2390, 4), (key3002, 4), (key2929, 4), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2593, 4), (key2880, 4), (key2772, 4)]

def rawRow13610 : Integer.Sparse Key := [(key2437, 4), (key2598, 4), (key3002, 4), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2772, 4), (key2593, 4), (key2880, 4)]

def rawRow13611 : Integer.Sparse Key := [(key2437, 4), (key3002, 4), (key2598, 4), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2772, 4), (key2880, 4), (key2593, 4)]

def rawRow13612 : Integer.Sparse Key := [(key2580, 4), (key2390, 4), (key2437, 4), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2880, 4), (key2593, 4), (key2772, 4)]

def rawRow13613 : Integer.Sparse Key := [(key2580, 4), (key2437, 4), (key2390, 4), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2880, 4), (key2772, 4), (key2593, 4)]

def rawRow13614 : Integer.Sparse Key := [(key2394, 4), (key2443, 4), (key2524, 4), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2889, -2), (key2931, -2), (key2968, -2), (key2587, 4), (key2766, 4), (key2843, 4)]

def rawRow13615 : Integer.Sparse Key := [(key2394, 4), (key2524, 4), (key2443, 4), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2600, -2), (key2593, -2), (key2889, -2), (key2772, -2), (key2968, -2), (key2931, -2), (key2587, 4), (key2843, 4), (key2766, 4)]

def rawRow13616 : Integer.Sparse Key := [(key2443, 4), (key2394, 4), (key2524, 4), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2772, -2), (key2931, -2), (key2593, -2), (key2968, -2), (key2600, -2), (key2889, -2), (key2766, 4), (key2587, 4), (key2843, 4)]

def rawRow13617 : Integer.Sparse Key := [(key2443, 4), (key2524, 4), (key2394, 4), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2931, -2), (key2772, -2), (key2968, -2), (key2593, -2), (key2889, -2), (key2600, -2), (key2766, 4), (key2843, 4), (key2587, 4)]

def rawRow13618 : Integer.Sparse Key := [(key2524, 4), (key2394, 4), (key2443, 4), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2889, -2), (key2968, -2), (key2600, -2), (key2931, -2), (key2593, -2), (key2772, -2), (key2843, 4), (key2587, 4), (key2766, 4)]

def rawRow13619 : Integer.Sparse Key := [(key2524, 4), (key2443, 4), (key2394, 4), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2968, -2), (key2889, -2), (key2931, -2), (key2600, -2), (key2772, -2), (key2593, -2), (key2843, 4), (key2766, 4), (key2587, 4)]

def rawRow13620 : Integer.Sparse Key := [(key2383, 4), (key2509, 4), (key2509, 4), (key2394, -2), (key2394, -2), (key2484, -2), (key2484, -2), (key2524, -2), (key2524, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow13621 : Integer.Sparse Key := [(key2509, 4), (key2383, 4), (key2509, 4), (key2484, -2), (key2524, -2), (key2394, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow13622 : Integer.Sparse Key := [(key2509, 4), (key2509, 4), (key2383, 4), (key2524, -2), (key2484, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2394, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow13623 : Integer.Sparse Key := [(key2394, 4), (key2443, 4), (key2524, 4), (key2383, -2), (key2394, -2), (key2411, -2), (key2484, -2), (key2443, -2), (key2509, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

def rawRow13624 : Integer.Sparse Key := [(key2394, 4), (key2524, 4), (key2443, 4), (key2394, -2), (key2383, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2443, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

def rawRow13625 : Integer.Sparse Key := [(key2443, 4), (key2394, 4), (key2524, 4), (key2411, -2), (key2443, -2), (key2383, -2), (key2509, -2), (key2394, -2), (key2484, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

def rawRow13626 : Integer.Sparse Key := [(key2443, 4), (key2524, 4), (key2394, 4), (key2443, -2), (key2411, -2), (key2509, -2), (key2383, -2), (key2484, -2), (key2394, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

def rawRow13627 : Integer.Sparse Key := [(key2524, 4), (key2394, 4), (key2443, 4), (key2484, -2), (key2509, -2), (key2394, -2), (key2443, -2), (key2383, -2), (key2411, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

def rawRow13628 : Integer.Sparse Key := [(key2524, 4), (key2443, 4), (key2394, 4), (key2509, -2), (key2484, -2), (key2443, -2), (key2394, -2), (key2411, -2), (key2383, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

def rawRow13629 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1071, -2), (key1036, 6), (key1106, -2), (key1114, -2), (key1150, -2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1001, -2), (key1114, -2), (key1232, -2), (key1123, 6), (key1015, -2), (key1123, -2), (key1235, -2)]

def rawRow13630 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1071, -2), (key1036, 6), (key1114, -2), (key1106, -2), (key1150, -2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1001, -2), (key1232, -2), (key1114, -2), (key1123, 6), (key1015, -2), (key1235, -2), (key1123, -2)]

def rawRow13631 : Integer.Sparse Key := [(key1028, -2), (key1071, -2), (key1036, -2), (key1036, 6), (key1106, -2), (key1150, -2), (key1114, -2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1114, -2), (key1001, -2), (key1232, -2), (key1123, 6), (key1123, -2), (key1015, -2), (key1235, -2)]

def rawRow13632 : Integer.Sparse Key := [(key1071, -2), (key1028, -2), (key1036, -2), (key1036, 6), (key1150, -2), (key1106, -2), (key1114, -2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1114, -2), (key1232, -2), (key1001, -2), (key1123, 6), (key1123, -2), (key1235, -2), (key1015, -2)]

def rawRow13633 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1028, -2), (key1036, 6), (key1114, -2), (key1150, -2), (key1106, -2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1232, -2), (key1001, -2), (key1114, -2), (key1123, 6), (key1235, -2), (key1015, -2), (key1123, -2)]

def rawRow13634 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1028, -2), (key1036, 6), (key1150, -2), (key1114, -2), (key1106, -2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1232, -2), (key1114, -2), (key1001, -2), (key1123, 6), (key1235, -2), (key1123, -2), (key1015, -2)]

def rawRow13635 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1071, -2), (key1028, 6), (key1232, -2), (key1232, -2), (key1242, -2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1235, 6), (key1015, -2), (key1123, -2), (key1123, -2)]

def rawRow13636 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1036, -2), (key1028, 6), (key1232, -2), (key1242, -2), (key1232, -2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1235, 6), (key1123, -2), (key1015, -2), (key1123, -2)]

def rawRow13637 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1036, -2), (key1028, 6), (key1242, -2), (key1232, -2), (key1232, -2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1235, 6), (key1123, -2), (key1123, -2), (key1015, -2)]

def rawRow13638 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1150, -2), (key1123, 6), (key1028, -2), (key1036, -2), (key1071, -2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1015, -2), (key1123, -2), (key1235, -2), (key1036, 6), (key1001, -2), (key1114, -2), (key1232, -2)]

def rawRow13639 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1150, -2), (key1123, 6), (key1036, -2), (key1028, -2), (key1071, -2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1015, -2), (key1235, -2), (key1123, -2), (key1036, 6), (key1001, -2), (key1232, -2), (key1114, -2)]

def rawRow13640 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1114, -2), (key1123, 6), (key1028, -2), (key1071, -2), (key1036, -2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1123, -2), (key1015, -2), (key1235, -2), (key1036, 6), (key1114, -2), (key1001, -2), (key1232, -2)]

def rawRow13641 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1114, -2), (key1123, 6), (key1071, -2), (key1028, -2), (key1036, -2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1123, -2), (key1235, -2), (key1015, -2), (key1036, 6), (key1114, -2), (key1232, -2), (key1001, -2)]

def rawRow13642 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1106, -2), (key1123, 6), (key1036, -2), (key1071, -2), (key1028, -2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1235, -2), (key1015, -2), (key1123, -2), (key1036, 6), (key1232, -2), (key1001, -2), (key1114, -2)]

def rawRow13643 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1106, -2), (key1123, 6), (key1071, -2), (key1036, -2), (key1028, -2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1235, -2), (key1123, -2), (key1015, -2), (key1036, 6), (key1232, -2), (key1114, -2), (key1001, -2)]

def rawRow13644 : Integer.Sparse Key := [(key1106, -2), (key1123, -2), (key1150, -2), (key1114, 6), (key1106, -2), (key1123, -2), (key1150, -2), (key993, 2), (key1015, 2), (key1028, 2), (key1235, 2), (key1071, 2), (key1242, 2), (key1001, -2), (key1036, -2), (key1232, -2), (key1114, 6), (key1001, -2), (key1036, -2), (key1232, -2)]

def rawRow13645 : Integer.Sparse Key := [(key1123, -2), (key1106, -2), (key1150, -2), (key1114, 6), (key1123, -2), (key1106, -2), (key1150, -2), (key1015, 2), (key993, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key1071, 2), (key1001, -2), (key1232, -2), (key1036, -2), (key1114, 6), (key1001, -2), (key1232, -2), (key1036, -2)]

def rawRow13646 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1123, -2), (key1114, 6), (key1106, -2), (key1150, -2), (key1123, -2), (key1028, 2), (key1071, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key1036, -2), (key1001, -2), (key1232, -2), (key1114, 6), (key1036, -2), (key1001, -2), (key1232, -2)]

def rawRow13647 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1123, -2), (key1114, 6), (key1150, -2), (key1106, -2), (key1123, -2), (key1071, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1235, 2), (key1015, 2), (key1036, -2), (key1232, -2), (key1001, -2), (key1114, 6), (key1036, -2), (key1232, -2), (key1001, -2)]

def rawRow13648 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1106, -2), (key1114, 6), (key1123, -2), (key1150, -2), (key1106, -2), (key1235, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key993, 2), (key1028, 2), (key1232, -2), (key1001, -2), (key1036, -2), (key1114, 6), (key1232, -2), (key1001, -2), (key1036, -2)]

def rawRow13649 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1106, -2), (key1114, 6), (key1150, -2), (key1123, -2), (key1106, -2), (key1242, 2), (key1235, 2), (key1071, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1232, -2), (key1036, -2), (key1001, -2), (key1114, 6), (key1232, -2), (key1036, -2), (key1001, -2)]

def rawRow13650 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1150, -2), (key1106, 6), (key1232, -2), (key1235, -2), (key1242, -2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1232, 6), (key1001, -2), (key1036, -2), (key1114, -2)]

def rawRow13651 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1150, -2), (key1106, 6), (key1235, -2), (key1232, -2), (key1242, -2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1232, 6), (key1001, -2), (key1114, -2), (key1036, -2)]

def rawRow13652 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1123, -2), (key1106, 6), (key1232, -2), (key1242, -2), (key1235, -2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1232, 6), (key1036, -2), (key1001, -2), (key1114, -2)]

def rawRow13653 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1123, -2), (key1106, 6), (key1242, -2), (key1232, -2), (key1235, -2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1232, 6), (key1036, -2), (key1114, -2), (key1001, -2)]

def rawRow13654 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1114, -2), (key1106, 6), (key1235, -2), (key1242, -2), (key1232, -2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1232, 6), (key1114, -2), (key1001, -2), (key1036, -2)]

def rawRow13655 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1114, -2), (key1106, 6), (key1242, -2), (key1235, -2), (key1232, -2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1232, 6), (key1114, -2), (key1036, -2), (key1001, -2)]

def rawRow13656 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1242, -2), (key1235, 6), (key1036, -2), (key1036, -2), (key1071, -2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key1015, -2), (key1123, -2), (key1123, -2), (key1028, 6), (key993, -2), (key1106, -2), (key1106, -2)]

def rawRow13657 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1232, -2), (key1235, 6), (key1036, -2), (key1071, -2), (key1036, -2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, -2), (key1015, -2), (key1123, -2), (key1028, 6), (key1106, -2), (key993, -2), (key1106, -2)]

def rawRow13658 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1232, -2), (key1235, 6), (key1071, -2), (key1036, -2), (key1036, -2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1123, -2), (key1123, -2), (key1015, -2), (key1028, 6), (key1106, -2), (key1106, -2), (key993, -2)]

def rawRow13659 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1242, -2), (key1232, 6), (key1114, -2), (key1123, -2), (key1150, -2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1001, -2), (key1036, -2), (key1114, -2), (key1106, 6), (key993, -2), (key1028, -2), (key1106, -2)]

def rawRow13660 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1242, -2), (key1232, 6), (key1123, -2), (key1114, -2), (key1150, -2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key1001, -2), (key1114, -2), (key1036, -2), (key1106, 6), (key993, -2), (key1106, -2), (key1028, -2)]

def rawRow13661 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1235, -2), (key1232, 6), (key1114, -2), (key1150, -2), (key1123, -2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1036, -2), (key1001, -2), (key1114, -2), (key1106, 6), (key1028, -2), (key993, -2), (key1106, -2)]

def rawRow13662 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1235, -2), (key1232, 6), (key1150, -2), (key1114, -2), (key1123, -2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1036, -2), (key1114, -2), (key1001, -2), (key1106, 6), (key1028, -2), (key1106, -2), (key993, -2)]

def rawRow13663 : Integer.Sparse Key := [(key1235, -2), (key1242, -2), (key1232, -2), (key1232, 6), (key1123, -2), (key1150, -2), (key1114, -2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1114, -2), (key1001, -2), (key1036, -2), (key1106, 6), (key1106, -2), (key993, -2), (key1028, -2)]

def rawRow13664 : Integer.Sparse Key := [(key1242, -2), (key1235, -2), (key1232, -2), (key1232, 6), (key1150, -2), (key1123, -2), (key1114, -2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1114, -2), (key1036, -2), (key1001, -2), (key1106, 6), (key1106, -2), (key1028, -2), (key993, -2)]

def rawRow13665 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2404, 6), (key2839, -2), (key2845, -2), (key3019, -2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2589, -2), (key2845, -2), (key2876, -2), (key2916, 6), (key2604, -2), (key2916, -2), (key2925, -2)]

def rawRow13666 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2435, -2), (key2404, 6), (key2845, -2), (key2839, -2), (key3019, -2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2589, -2), (key2876, -2), (key2845, -2), (key2916, 6), (key2604, -2), (key2925, -2), (key2916, -2)]

def rawRow13667 : Integer.Sparse Key := [(key2398, -2), (key2435, -2), (key2404, -2), (key2404, 6), (key2839, -2), (key3019, -2), (key2845, -2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2845, -2), (key2589, -2), (key2876, -2), (key2916, 6), (key2916, -2), (key2604, -2), (key2925, -2)]

def rawRow13668 : Integer.Sparse Key := [(key2435, -2), (key2398, -2), (key2404, -2), (key2404, 6), (key3019, -2), (key2839, -2), (key2845, -2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2845, -2), (key2876, -2), (key2589, -2), (key2916, 6), (key2916, -2), (key2925, -2), (key2604, -2)]

def rawRow13669 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2398, -2), (key2404, 6), (key2845, -2), (key3019, -2), (key2839, -2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2876, -2), (key2589, -2), (key2845, -2), (key2916, 6), (key2925, -2), (key2604, -2), (key2916, -2)]

def rawRow13670 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2398, -2), (key2404, 6), (key3019, -2), (key2845, -2), (key2839, -2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2876, -2), (key2845, -2), (key2589, -2), (key2916, 6), (key2925, -2), (key2916, -2), (key2604, -2)]

def rawRow13671 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2435, -2), (key2398, 6), (key2876, -2), (key2876, -2), (key3028, -2), (key2589, 2), (key2589, 2), (key2845, 2), (key2845, 2), (key3019, 2), (key3019, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2925, 6), (key2604, -2), (key2916, -2), (key2916, -2)]

def rawRow13672 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2404, -2), (key2398, 6), (key2876, -2), (key3028, -2), (key2876, -2), (key2845, 2), (key3019, 2), (key2589, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2925, 6), (key2916, -2), (key2604, -2), (key2916, -2)]

def rawRow13673 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2404, -2), (key2398, 6), (key3028, -2), (key2876, -2), (key2876, -2), (key3019, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2589, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2925, 6), (key2916, -2), (key2916, -2), (key2604, -2)]

def rawRow13674 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2501, -2), (key2478, 6), (key2398, -2), (key2404, -2), (key2435, -2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2604, -2), (key2916, -2), (key2925, -2), (key2768, 6), (key2589, -2), (key2845, -2), (key2876, -2)]

def rawRow13675 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2501, -2), (key2478, 6), (key2404, -2), (key2398, -2), (key2435, -2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2604, -2), (key2925, -2), (key2916, -2), (key2768, 6), (key2589, -2), (key2876, -2), (key2845, -2)]

def rawRow13676 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2470, -2), (key2478, 6), (key2398, -2), (key2435, -2), (key2404, -2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2916, -2), (key2604, -2), (key2925, -2), (key2768, 6), (key2845, -2), (key2589, -2), (key2876, -2)]

def rawRow13677 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2435, -2), (key2398, -2), (key2404, -2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2916, -2), (key2925, -2), (key2604, -2), (key2768, 6), (key2845, -2), (key2876, -2), (key2589, -2)]

def rawRow13678 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2464, -2), (key2478, 6), (key2404, -2), (key2435, -2), (key2398, -2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2925, -2), (key2604, -2), (key2916, -2), (key2768, 6), (key2876, -2), (key2589, -2), (key2845, -2)]

def rawRow13679 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2464, -2), (key2478, 6), (key2435, -2), (key2404, -2), (key2398, -2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2925, -2), (key2916, -2), (key2604, -2), (key2768, 6), (key2876, -2), (key2845, -2), (key2589, -2)]

def rawRow13680 : Integer.Sparse Key := [(key2464, -2), (key2478, -2), (key2501, -2), (key2470, 6), (key2464, -2), (key2478, -2), (key2501, -2), (key2370, 2), (key2388, 2), (key2762, 2), (key2925, 2), (key3005, 2), (key3028, 2), (key2589, -2), (key2768, -2), (key2876, -2), (key2845, 6), (key2589, -2), (key2768, -2), (key2876, -2)]

def rawRow13681 : Integer.Sparse Key := [(key2478, -2), (key2464, -2), (key2501, -2), (key2470, 6), (key2478, -2), (key2464, -2), (key2501, -2), (key2388, 2), (key2370, 2), (key2925, 2), (key2762, 2), (key3028, 2), (key3005, 2), (key2589, -2), (key2876, -2), (key2768, -2), (key2845, 6), (key2589, -2), (key2876, -2), (key2768, -2)]

def rawRow13682 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2478, -2), (key2470, 6), (key2464, -2), (key2501, -2), (key2478, -2), (key2398, 2), (key2435, 2), (key2583, 2), (key3028, 2), (key2604, 2), (key2925, 2), (key2768, -2), (key2589, -2), (key2876, -2), (key2845, 6), (key2768, -2), (key2589, -2), (key2876, -2)]

def rawRow13683 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2478, -2), (key2470, 6), (key2501, -2), (key2464, -2), (key2478, -2), (key2435, 2), (key2398, 2), (key3028, 2), (key2583, 2), (key2925, 2), (key2604, 2), (key2768, -2), (key2876, -2), (key2589, -2), (key2845, 6), (key2768, -2), (key2876, -2), (key2589, -2)]

def rawRow13684 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2464, -2), (key2470, 6), (key2478, -2), (key2501, -2), (key2464, -2), (key2570, 2), (key2575, 2), (key2388, 2), (key2435, 2), (key2370, 2), (key2762, 2), (key2876, -2), (key2589, -2), (key2768, -2), (key2845, 6), (key2876, -2), (key2589, -2), (key2768, -2)]

def rawRow13685 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2464, -2), (key2470, 6), (key2501, -2), (key2478, -2), (key2464, -2), (key2575, 2), (key2570, 2), (key2435, 2), (key2388, 2), (key2398, 2), (key2583, 2), (key2876, -2), (key2768, -2), (key2589, -2), (key2845, 6), (key2876, -2), (key2768, -2), (key2589, -2)]

def rawRow13686 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2501, -2), (key2464, 6), (key2568, -2), (key2570, -2), (key2575, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2876, 6), (key2589, -2), (key2768, -2), (key2845, -2)]

def rawRow13687 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2501, -2), (key2464, 6), (key2570, -2), (key2568, -2), (key2575, -2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2876, 6), (key2589, -2), (key2845, -2), (key2768, -2)]

def rawRow13688 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2478, -2), (key2464, 6), (key2568, -2), (key2575, -2), (key2570, -2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2876, 6), (key2768, -2), (key2589, -2), (key2845, -2)]

def rawRow13689 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2478, -2), (key2464, 6), (key2575, -2), (key2568, -2), (key2570, -2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2876, 6), (key2768, -2), (key2845, -2), (key2589, -2)]

def rawRow13690 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2470, -2), (key2464, 6), (key2570, -2), (key2575, -2), (key2568, -2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2876, 6), (key2845, -2), (key2589, -2), (key2768, -2)]

def rawRow13691 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2470, -2), (key2464, 6), (key2575, -2), (key2570, -2), (key2568, -2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2876, 6), (key2845, -2), (key2768, -2), (key2589, -2)]

def rawRow13692 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2575, -2), (key2570, 6), (key2404, -2), (key2404, -2), (key2435, -2), (key2376, 2), (key2376, 2), (key2470, 2), (key2470, 2), (key2501, 2), (key2501, 2), (key2388, -2), (key2478, -2), (key2478, -2), (key2398, 6), (key2583, -2), (key2839, -2), (key2839, -2)]

def rawRow13693 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2568, -2), (key2570, 6), (key2404, -2), (key2435, -2), (key2404, -2), (key2470, 2), (key2501, 2), (key2376, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2478, -2), (key2388, -2), (key2478, -2), (key2398, 6), (key2839, -2), (key2583, -2), (key2839, -2)]

def rawRow13694 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2568, -2), (key2570, 6), (key2435, -2), (key2404, -2), (key2404, -2), (key2501, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2376, 2), (key2478, -2), (key2478, -2), (key2388, -2), (key2398, 6), (key2839, -2), (key2839, -2), (key2583, -2)]

def rawRow13695 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2575, -2), (key2568, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2376, -2), (key2404, -2), (key2470, -2), (key2464, 6), (key2370, -2), (key2762, -2), (key2839, -2)]

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

def rawRow13696 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2575, -2), (key2568, 6), (key2478, -2), (key2470, -2), (key2501, -2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2376, -2), (key2470, -2), (key2404, -2), (key2464, 6), (key2370, -2), (key2839, -2), (key2762, -2)]

def rawRow13697 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2570, -2), (key2568, 6), (key2470, -2), (key2501, -2), (key2478, -2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2404, -2), (key2376, -2), (key2470, -2), (key2464, 6), (key2398, -2), (key2583, -2), (key2839, -2)]

def rawRow13698 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2570, -2), (key2568, 6), (key2501, -2), (key2470, -2), (key2478, -2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2404, -2), (key2470, -2), (key2376, -2), (key2464, 6), (key2398, -2), (key2839, -2), (key2583, -2)]

def rawRow13699 : Integer.Sparse Key := [(key2570, -2), (key2575, -2), (key2568, -2), (key2568, 6), (key2478, -2), (key2501, -2), (key2470, -2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2470, -2), (key2376, -2), (key2404, -2), (key2464, 6), (key2464, -2), (key2370, -2), (key2762, -2)]

def rawRow13700 : Integer.Sparse Key := [(key2575, -2), (key2570, -2), (key2568, -2), (key2568, 6), (key2501, -2), (key2478, -2), (key2470, -2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2470, -2), (key2404, -2), (key2376, -2), (key2464, 6), (key2464, -2), (key2398, -2), (key2583, -2)]

def rawRow13701 : Integer.Sparse Key := [(key2780, 6), (key2665, -2), (key2780, -2), (key2789, -2), (key2803, 6), (key2610, -2), (key2803, -2), (key2824, -2), (key2700, -2), (key2853, -2), (key2855, -2), (key2626, -2), (key2853, -2), (key2865, -2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

def rawRow13702 : Integer.Sparse Key := [(key2780, 6), (key2665, -2), (key2789, -2), (key2780, -2), (key2803, 6), (key2610, -2), (key2824, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, -2), (key2865, -2), (key2853, -2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

def rawRow13703 : Integer.Sparse Key := [(key2780, 6), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, 6), (key2803, -2), (key2610, -2), (key2824, -2), (key2853, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, -2), (key2865, -2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

def rawRow13704 : Integer.Sparse Key := [(key2780, 6), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, 6), (key2803, -2), (key2824, -2), (key2610, -2), (key2853, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, -2), (key2626, -2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

def rawRow13705 : Integer.Sparse Key := [(key2780, 6), (key2789, -2), (key2665, -2), (key2780, -2), (key2803, 6), (key2824, -2), (key2610, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, -2), (key2626, -2), (key2853, -2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

def rawRow13706 : Integer.Sparse Key := [(key2780, 6), (key2789, -2), (key2780, -2), (key2665, -2), (key2803, 6), (key2824, -2), (key2803, -2), (key2610, -2), (key2855, -2), (key2853, -2), (key2700, -2), (key2865, -2), (key2853, -2), (key2626, -2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

def rawRow13707 : Integer.Sparse Key := [(key2789, 6), (key2665, -2), (key2780, -2), (key2780, -2), (key2824, 6), (key2610, -2), (key2803, -2), (key2803, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2635, -2), (key2855, -2), (key2855, -2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

def rawRow13708 : Integer.Sparse Key := [(key2789, 6), (key2780, -2), (key2665, -2), (key2780, -2), (key2824, 6), (key2803, -2), (key2610, -2), (key2803, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

def rawRow13709 : Integer.Sparse Key := [(key2789, 6), (key2780, -2), (key2780, -2), (key2665, -2), (key2824, 6), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

def rawRow13710 : Integer.Sparse Key := [(key2803, 6), (key2700, -2), (key2853, -2), (key2855, -2), (key2780, 6), (key2626, -2), (key2853, -2), (key2865, -2), (key2665, -2), (key2780, -2), (key2789, -2), (key2610, -2), (key2803, -2), (key2824, -2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

def rawRow13711 : Integer.Sparse Key := [(key2803, 6), (key2700, -2), (key2855, -2), (key2853, -2), (key2780, 6), (key2626, -2), (key2865, -2), (key2853, -2), (key2665, -2), (key2789, -2), (key2780, -2), (key2610, -2), (key2824, -2), (key2803, -2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

def rawRow13712 : Integer.Sparse Key := [(key2803, 6), (key2853, -2), (key2700, -2), (key2855, -2), (key2780, 6), (key2853, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, -2), (key2610, -2), (key2824, -2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

def rawRow13713 : Integer.Sparse Key := [(key2803, 6), (key2853, -2), (key2855, -2), (key2700, -2), (key2780, 6), (key2853, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

def rawRow13714 : Integer.Sparse Key := [(key2803, 6), (key2855, -2), (key2700, -2), (key2853, -2), (key2780, 6), (key2865, -2), (key2626, -2), (key2853, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

def rawRow13715 : Integer.Sparse Key := [(key2803, 6), (key2855, -2), (key2853, -2), (key2700, -2), (key2780, 6), (key2865, -2), (key2853, -2), (key2626, -2), (key2789, -2), (key2780, -2), (key2665, -2), (key2824, -2), (key2803, -2), (key2610, -2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

def rawRow13716 : Integer.Sparse Key := [(key2853, 6), (key2700, -2), (key2803, -2), (key2855, -2), (key2853, 6), (key2626, -2), (key2780, -2), (key2865, -2), (key2700, -2), (key2803, -2), (key2855, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2610, 2), (key2635, 2), (key2665, 2), (key2721, 2), (key2789, 2), (key2824, 2)]

def rawRow13717 : Integer.Sparse Key := [(key2853, 6), (key2700, -2), (key2855, -2), (key2803, -2), (key2853, 6), (key2626, -2), (key2865, -2), (key2780, -2), (key2700, -2), (key2855, -2), (key2803, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2635, 2), (key2610, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2789, 2)]

def rawRow13718 : Integer.Sparse Key := [(key2853, 6), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, 6), (key2780, -2), (key2626, -2), (key2865, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2665, 2), (key2789, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2721, 2)]

def rawRow13719 : Integer.Sparse Key := [(key2853, 6), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, 6), (key2780, -2), (key2865, -2), (key2626, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2780, -2), (key2865, -2), (key2626, -2), (key2789, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2721, 2), (key2635, 2)]

def rawRow13720 : Integer.Sparse Key := [(key2853, 6), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, 6), (key2865, -2), (key2626, -2), (key2780, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2721, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2610, 2), (key2665, 2)]

def rawRow13721 : Integer.Sparse Key := [(key2853, 6), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, 6), (key2865, -2), (key2780, -2), (key2626, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2865, -2), (key2780, -2), (key2626, -2), (key2824, 2), (key2721, 2), (key2789, 2), (key2635, 2), (key2665, 2), (key2610, 2)]

def rawRow13722 : Integer.Sparse Key := [(key2855, 6), (key2700, -2), (key2803, -2), (key2853, -2), (key2865, 6), (key2626, -2), (key2780, -2), (key2853, -2), (key2721, -2), (key2824, -2), (key2865, -2), (key2635, -2), (key2789, -2), (key2855, -2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

def rawRow13723 : Integer.Sparse Key := [(key2855, 6), (key2700, -2), (key2853, -2), (key2803, -2), (key2865, 6), (key2626, -2), (key2853, -2), (key2780, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2635, -2), (key2855, -2), (key2789, -2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

def rawRow13724 : Integer.Sparse Key := [(key2855, 6), (key2803, -2), (key2700, -2), (key2853, -2), (key2865, 6), (key2780, -2), (key2626, -2), (key2853, -2), (key2824, -2), (key2721, -2), (key2865, -2), (key2789, -2), (key2635, -2), (key2855, -2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

def rawRow13725 : Integer.Sparse Key := [(key2855, 6), (key2803, -2), (key2853, -2), (key2700, -2), (key2865, 6), (key2780, -2), (key2853, -2), (key2626, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2789, -2), (key2855, -2), (key2635, -2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

def rawRow13726 : Integer.Sparse Key := [(key2855, 6), (key2853, -2), (key2700, -2), (key2803, -2), (key2865, 6), (key2853, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, -2), (key2635, -2), (key2789, -2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

def rawRow13727 : Integer.Sparse Key := [(key2855, 6), (key2853, -2), (key2803, -2), (key2700, -2), (key2865, 6), (key2853, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, -2), (key2789, -2), (key2635, -2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow13728 : Integer.Sparse Key := [(key2824, 6), (key2721, -2), (key2865, -2), (key2865, -2), (key2789, 6), (key2635, -2), (key2855, -2), (key2855, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

def rawRow13729 : Integer.Sparse Key := [(key2824, 6), (key2865, -2), (key2721, -2), (key2865, -2), (key2789, 6), (key2855, -2), (key2635, -2), (key2855, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2803, -2), (key2610, -2), (key2803, -2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

def rawRow13730 : Integer.Sparse Key := [(key2824, 6), (key2865, -2), (key2865, -2), (key2721, -2), (key2789, 6), (key2855, -2), (key2855, -2), (key2635, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2803, -2), (key2803, -2), (key2610, -2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

def rawRow13731 : Integer.Sparse Key := [(key2865, 6), (key2721, -2), (key2824, -2), (key2865, -2), (key2855, 6), (key2635, -2), (key2789, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, -2), (key2780, -2), (key2853, -2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

def rawRow13732 : Integer.Sparse Key := [(key2865, 6), (key2721, -2), (key2865, -2), (key2824, -2), (key2855, 6), (key2635, -2), (key2855, -2), (key2789, -2), (key2700, -2), (key2853, -2), (key2803, -2), (key2626, -2), (key2853, -2), (key2780, -2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

def rawRow13733 : Integer.Sparse Key := [(key2865, 6), (key2824, -2), (key2721, -2), (key2865, -2), (key2855, 6), (key2789, -2), (key2635, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, -2), (key2626, -2), (key2853, -2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

def rawRow13734 : Integer.Sparse Key := [(key2865, 6), (key2824, -2), (key2865, -2), (key2721, -2), (key2855, 6), (key2789, -2), (key2855, -2), (key2635, -2), (key2803, -2), (key2853, -2), (key2700, -2), (key2780, -2), (key2853, -2), (key2626, -2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

def rawRow13735 : Integer.Sparse Key := [(key2865, 6), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, 6), (key2855, -2), (key2635, -2), (key2789, -2), (key2853, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, -2), (key2780, -2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

def rawRow13736 : Integer.Sparse Key := [(key2865, 6), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, 6), (key2855, -2), (key2789, -2), (key2635, -2), (key2853, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, -2), (key2626, -2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow13737 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1070, -2), (key1035, 6), (key1107, -2), (key1113, -2), (key1149, -2), (key994, 2), (key1000, 2), (key1107, 2), (key1231, 2), (key1149, 2), (key1241, 2), (key1000, -2), (key1113, -2), (key1231, -2), (key1122, 6), (key1014, -2), (key1122, -2), (key1234, -2)]

def rawRow13738 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1070, -2), (key1035, 6), (key1113, -2), (key1107, -2), (key1149, -2), (key1000, 2), (key994, 2), (key1231, 2), (key1107, 2), (key1241, 2), (key1149, 2), (key1000, -2), (key1231, -2), (key1113, -2), (key1122, 6), (key1014, -2), (key1234, -2), (key1122, -2)]

def rawRow13739 : Integer.Sparse Key := [(key1029, -2), (key1070, -2), (key1035, -2), (key1035, 6), (key1107, -2), (key1149, -2), (key1113, -2), (key1107, 2), (key1149, 2), (key994, 2), (key1241, 2), (key1000, 2), (key1231, 2), (key1113, -2), (key1000, -2), (key1231, -2), (key1122, 6), (key1122, -2), (key1014, -2), (key1234, -2)]

def rawRow13740 : Integer.Sparse Key := [(key1070, -2), (key1029, -2), (key1035, -2), (key1035, 6), (key1149, -2), (key1107, -2), (key1113, -2), (key1149, 2), (key1107, 2), (key1241, 2), (key994, 2), (key1231, 2), (key1000, 2), (key1113, -2), (key1231, -2), (key1000, -2), (key1122, 6), (key1122, -2), (key1234, -2), (key1014, -2)]

def rawRow13741 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1029, -2), (key1035, 6), (key1113, -2), (key1149, -2), (key1107, -2), (key1231, 2), (key1241, 2), (key1000, 2), (key1149, 2), (key994, 2), (key1107, 2), (key1231, -2), (key1000, -2), (key1113, -2), (key1122, 6), (key1234, -2), (key1014, -2), (key1122, -2)]

def rawRow13742 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1029, -2), (key1035, 6), (key1149, -2), (key1113, -2), (key1107, -2), (key1241, 2), (key1231, 2), (key1149, 2), (key1000, 2), (key1107, 2), (key994, 2), (key1231, -2), (key1113, -2), (key1000, -2), (key1122, 6), (key1234, -2), (key1122, -2), (key1014, -2)]

def rawRow13743 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1070, -2), (key1029, 6), (key1231, -2), (key1231, -2), (key1241, -2), (key1000, 2), (key1000, 2), (key1113, 2), (key1113, 2), (key1149, 2), (key1149, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1234, 6), (key1014, -2), (key1122, -2), (key1122, -2)]

def rawRow13744 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1035, -2), (key1029, 6), (key1231, -2), (key1241, -2), (key1231, -2), (key1113, 2), (key1149, 2), (key1000, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1234, 6), (key1122, -2), (key1014, -2), (key1122, -2)]

def rawRow13745 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1035, -2), (key1029, 6), (key1241, -2), (key1231, -2), (key1231, -2), (key1149, 2), (key1113, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1000, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1234, 6), (key1122, -2), (key1122, -2), (key1014, -2)]

def rawRow13746 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1149, -2), (key1122, 6), (key1029, -2), (key1035, -2), (key1070, -2), (key994, 2), (key1000, 2), (key1107, 2), (key1231, 2), (key1149, 2), (key1241, 2), (key1014, -2), (key1122, -2), (key1234, -2), (key1035, 6), (key1000, -2), (key1113, -2), (key1231, -2)]

def rawRow13747 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1149, -2), (key1122, 6), (key1035, -2), (key1029, -2), (key1070, -2), (key1000, 2), (key994, 2), (key1231, 2), (key1107, 2), (key1241, 2), (key1149, 2), (key1014, -2), (key1234, -2), (key1122, -2), (key1035, 6), (key1000, -2), (key1231, -2), (key1113, -2)]

def rawRow13748 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1113, -2), (key1122, 6), (key1029, -2), (key1070, -2), (key1035, -2), (key1107, 2), (key1149, 2), (key994, 2), (key1241, 2), (key1000, 2), (key1231, 2), (key1122, -2), (key1014, -2), (key1234, -2), (key1035, 6), (key1113, -2), (key1000, -2), (key1231, -2)]

def rawRow13749 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1113, -2), (key1122, 6), (key1070, -2), (key1029, -2), (key1035, -2), (key1149, 2), (key1107, 2), (key1241, 2), (key994, 2), (key1231, 2), (key1000, 2), (key1122, -2), (key1234, -2), (key1014, -2), (key1035, 6), (key1113, -2), (key1231, -2), (key1000, -2)]

def rawRow13750 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1107, -2), (key1122, 6), (key1035, -2), (key1070, -2), (key1029, -2), (key1231, 2), (key1241, 2), (key1000, 2), (key1149, 2), (key994, 2), (key1107, 2), (key1234, -2), (key1014, -2), (key1122, -2), (key1035, 6), (key1231, -2), (key1000, -2), (key1113, -2)]

def rawRow13751 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1107, -2), (key1122, 6), (key1070, -2), (key1035, -2), (key1029, -2), (key1241, 2), (key1231, 2), (key1149, 2), (key1000, 2), (key1107, 2), (key994, 2), (key1234, -2), (key1122, -2), (key1014, -2), (key1035, 6), (key1231, -2), (key1113, -2), (key1000, -2)]

def rawRow13752 : Integer.Sparse Key := [(key1107, -2), (key1122, -2), (key1149, -2), (key1113, 6), (key1107, -2), (key1122, -2), (key1149, -2), (key994, 2), (key1014, 2), (key1029, 2), (key1234, 2), (key1070, 2), (key1241, 2), (key1000, -2), (key1035, -2), (key1231, -2), (key1113, 6), (key1000, -2), (key1035, -2), (key1231, -2)]

def rawRow13753 : Integer.Sparse Key := [(key1122, -2), (key1107, -2), (key1149, -2), (key1113, 6), (key1122, -2), (key1107, -2), (key1149, -2), (key1014, 2), (key994, 2), (key1234, 2), (key1029, 2), (key1241, 2), (key1070, 2), (key1000, -2), (key1231, -2), (key1035, -2), (key1113, 6), (key1000, -2), (key1231, -2), (key1035, -2)]

def rawRow13754 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1122, -2), (key1113, 6), (key1107, -2), (key1149, -2), (key1122, -2), (key1029, 2), (key1070, 2), (key994, 2), (key1241, 2), (key1014, 2), (key1234, 2), (key1035, -2), (key1000, -2), (key1231, -2), (key1113, 6), (key1035, -2), (key1000, -2), (key1231, -2)]

def rawRow13755 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1122, -2), (key1113, 6), (key1149, -2), (key1107, -2), (key1122, -2), (key1070, 2), (key1029, 2), (key1241, 2), (key994, 2), (key1234, 2), (key1014, 2), (key1035, -2), (key1231, -2), (key1000, -2), (key1113, 6), (key1035, -2), (key1231, -2), (key1000, -2)]

def rawRow13756 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1107, -2), (key1113, 6), (key1122, -2), (key1149, -2), (key1107, -2), (key1234, 2), (key1241, 2), (key1014, 2), (key1070, 2), (key994, 2), (key1029, 2), (key1231, -2), (key1000, -2), (key1035, -2), (key1113, 6), (key1231, -2), (key1000, -2), (key1035, -2)]

def rawRow13757 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1107, -2), (key1113, 6), (key1149, -2), (key1122, -2), (key1107, -2), (key1241, 2), (key1234, 2), (key1070, 2), (key1014, 2), (key1029, 2), (key994, 2), (key1231, -2), (key1035, -2), (key1000, -2), (key1113, 6), (key1231, -2), (key1035, -2), (key1000, -2)]

def rawRow13758 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1149, -2), (key1107, 6), (key1231, -2), (key1234, -2), (key1241, -2), (key1000, 2), (key1014, 2), (key1035, 2), (key1122, 2), (key1070, 2), (key1149, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1231, 6), (key1000, -2), (key1035, -2), (key1113, -2)]

def rawRow13759 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1149, -2), (key1107, 6), (key1234, -2), (key1231, -2), (key1241, -2), (key1014, 2), (key1000, 2), (key1122, 2), (key1035, 2), (key1149, 2), (key1070, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1231, 6), (key1000, -2), (key1113, -2), (key1035, -2)]

def rawRow13760 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1122, -2), (key1107, 6), (key1231, -2), (key1241, -2), (key1234, -2), (key1035, 2), (key1070, 2), (key1000, 2), (key1149, 2), (key1014, 2), (key1122, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1231, 6), (key1035, -2), (key1000, -2), (key1113, -2)]

def rawRow13761 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1122, -2), (key1107, 6), (key1241, -2), (key1231, -2), (key1234, -2), (key1070, 2), (key1035, 2), (key1149, 2), (key1000, 2), (key1122, 2), (key1014, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1231, 6), (key1035, -2), (key1113, -2), (key1000, -2)]

def rawRow13762 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1113, -2), (key1107, 6), (key1234, -2), (key1241, -2), (key1231, -2), (key1122, 2), (key1149, 2), (key1014, 2), (key1070, 2), (key1000, 2), (key1035, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1231, 6), (key1113, -2), (key1000, -2), (key1035, -2)]

def rawRow13763 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1113, -2), (key1107, 6), (key1241, -2), (key1234, -2), (key1231, -2), (key1149, 2), (key1122, 2), (key1070, 2), (key1014, 2), (key1035, 2), (key1000, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1231, 6), (key1113, -2), (key1035, -2), (key1000, -2)]

def rawRow13764 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1241, -2), (key1234, 6), (key1035, -2), (key1035, -2), (key1070, -2), (key1000, 2), (key1000, 2), (key1113, 2), (key1113, 2), (key1149, 2), (key1149, 2), (key1014, -2), (key1122, -2), (key1122, -2), (key1029, 6), (key994, -2), (key1107, -2), (key1107, -2)]

def rawRow13765 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1231, -2), (key1234, 6), (key1035, -2), (key1070, -2), (key1035, -2), (key1113, 2), (key1149, 2), (key1000, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1122, -2), (key1014, -2), (key1122, -2), (key1029, 6), (key1107, -2), (key994, -2), (key1107, -2)]

def rawRow13766 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1231, -2), (key1234, 6), (key1070, -2), (key1035, -2), (key1035, -2), (key1149, 2), (key1113, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1000, 2), (key1122, -2), (key1122, -2), (key1014, -2), (key1029, 6), (key1107, -2), (key1107, -2), (key994, -2)]

def rawRow13767 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1241, -2), (key1231, 6), (key1113, -2), (key1122, -2), (key1149, -2), (key1000, 2), (key1014, 2), (key1035, 2), (key1122, 2), (key1070, 2), (key1149, 2), (key1000, -2), (key1035, -2), (key1113, -2), (key1107, 6), (key994, -2), (key1029, -2), (key1107, -2)]

def rawRow13768 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1241, -2), (key1231, 6), (key1122, -2), (key1113, -2), (key1149, -2), (key1014, 2), (key1000, 2), (key1122, 2), (key1035, 2), (key1149, 2), (key1070, 2), (key1000, -2), (key1113, -2), (key1035, -2), (key1107, 6), (key994, -2), (key1107, -2), (key1029, -2)]

def rawRow13769 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1234, -2), (key1231, 6), (key1113, -2), (key1149, -2), (key1122, -2), (key1035, 2), (key1070, 2), (key1000, 2), (key1149, 2), (key1014, 2), (key1122, 2), (key1035, -2), (key1000, -2), (key1113, -2), (key1107, 6), (key1029, -2), (key994, -2), (key1107, -2)]

def rawRow13770 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1234, -2), (key1231, 6), (key1149, -2), (key1113, -2), (key1122, -2), (key1070, 2), (key1035, 2), (key1149, 2), (key1000, 2), (key1122, 2), (key1014, 2), (key1035, -2), (key1113, -2), (key1000, -2), (key1107, 6), (key1029, -2), (key1107, -2), (key994, -2)]

def rawRow13771 : Integer.Sparse Key := [(key1234, -2), (key1241, -2), (key1231, -2), (key1231, 6), (key1122, -2), (key1149, -2), (key1113, -2), (key1122, 2), (key1149, 2), (key1014, 2), (key1070, 2), (key1000, 2), (key1035, 2), (key1113, -2), (key1000, -2), (key1035, -2), (key1107, 6), (key1107, -2), (key994, -2), (key1029, -2)]

def rawRow13772 : Integer.Sparse Key := [(key1241, -2), (key1234, -2), (key1231, -2), (key1231, 6), (key1149, -2), (key1122, -2), (key1113, -2), (key1149, 2), (key1122, 2), (key1070, 2), (key1014, 2), (key1035, 2), (key1000, 2), (key1113, -2), (key1035, -2), (key1000, -2), (key1107, 6), (key1107, -2), (key1029, -2), (key994, -2)]

def rawRow13773 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1243, 4), (key1003, -2), (key1009, -2), (key1116, -2), (key1233, -2), (key1159, -2), (key1243, -2), (key1017, -2), (key1022, -2), (key1125, -2), (key1236, -2), (key1174, -2), (key1247, -2), (key1022, 4), (key1130, 4), (key1236, 4)]

def rawRow13774 : Integer.Sparse Key := [(key1003, 4), (key1243, 4), (key1152, 4), (key1009, -2), (key1003, -2), (key1233, -2), (key1116, -2), (key1243, -2), (key1159, -2), (key1022, -2), (key1017, -2), (key1236, -2), (key1125, -2), (key1247, -2), (key1174, -2), (key1022, 4), (key1236, 4), (key1130, 4)]

def rawRow13775 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1243, 4), (key1116, -2), (key1159, -2), (key1003, -2), (key1243, -2), (key1009, -2), (key1233, -2), (key1125, -2), (key1174, -2), (key1017, -2), (key1247, -2), (key1022, -2), (key1236, -2), (key1130, 4), (key1022, 4), (key1236, 4)]

def rawRow13776 : Integer.Sparse Key := [(key1152, 4), (key1243, 4), (key1003, 4), (key1159, -2), (key1116, -2), (key1243, -2), (key1003, -2), (key1233, -2), (key1009, -2), (key1174, -2), (key1125, -2), (key1247, -2), (key1017, -2), (key1236, -2), (key1022, -2), (key1130, 4), (key1236, 4), (key1022, 4)]

def rawRow13777 : Integer.Sparse Key := [(key1243, 4), (key1003, 4), (key1152, 4), (key1233, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1003, -2), (key1116, -2), (key1236, -2), (key1247, -2), (key1022, -2), (key1174, -2), (key1017, -2), (key1125, -2), (key1236, 4), (key1022, 4), (key1130, 4)]

def rawRow13778 : Integer.Sparse Key := [(key1243, 4), (key1152, 4), (key1003, 4), (key1243, -2), (key1233, -2), (key1159, -2), (key1009, -2), (key1116, -2), (key1003, -2), (key1247, -2), (key1236, -2), (key1174, -2), (key1022, -2), (key1125, -2), (key1017, -2), (key1236, 4), (key1130, 4), (key1022, 4)]

def rawRow13779 : Integer.Sparse Key := [(key1009, 4), (key1159, 4), (key1159, 4), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1022, -2), (key1022, -2), (key1130, -2), (key1130, -2), (key1174, -2), (key1174, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

def rawRow13780 : Integer.Sparse Key := [(key1159, 4), (key1009, 4), (key1159, 4), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

def rawRow13781 : Integer.Sparse Key := [(key1159, 4), (key1159, 4), (key1009, 4), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1174, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1022, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

def rawRow13782 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1243, 4), (key1017, -2), (key1022, -2), (key1125, -2), (key1236, -2), (key1174, -2), (key1247, -2), (key1003, -2), (key1009, -2), (key1116, -2), (key1233, -2), (key1159, -2), (key1243, -2), (key1022, 4), (key1130, 4), (key1236, 4)]

def rawRow13783 : Integer.Sparse Key := [(key1003, 4), (key1243, 4), (key1152, 4), (key1022, -2), (key1017, -2), (key1236, -2), (key1125, -2), (key1247, -2), (key1174, -2), (key1009, -2), (key1003, -2), (key1233, -2), (key1116, -2), (key1243, -2), (key1159, -2), (key1022, 4), (key1236, 4), (key1130, 4)]

def rawRow13784 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1243, 4), (key1125, -2), (key1174, -2), (key1017, -2), (key1247, -2), (key1022, -2), (key1236, -2), (key1116, -2), (key1159, -2), (key1003, -2), (key1243, -2), (key1009, -2), (key1233, -2), (key1130, 4), (key1022, 4), (key1236, 4)]

def rawRow13785 : Integer.Sparse Key := [(key1152, 4), (key1243, 4), (key1003, 4), (key1174, -2), (key1125, -2), (key1247, -2), (key1017, -2), (key1236, -2), (key1022, -2), (key1159, -2), (key1116, -2), (key1243, -2), (key1003, -2), (key1233, -2), (key1009, -2), (key1130, 4), (key1236, 4), (key1022, 4)]

def rawRow13786 : Integer.Sparse Key := [(key1243, 4), (key1003, 4), (key1152, 4), (key1236, -2), (key1247, -2), (key1022, -2), (key1174, -2), (key1017, -2), (key1125, -2), (key1233, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1003, -2), (key1116, -2), (key1236, 4), (key1022, 4), (key1130, 4)]

def rawRow13787 : Integer.Sparse Key := [(key1243, 4), (key1152, 4), (key1003, 4), (key1247, -2), (key1236, -2), (key1174, -2), (key1022, -2), (key1125, -2), (key1017, -2), (key1243, -2), (key1233, -2), (key1159, -2), (key1009, -2), (key1116, -2), (key1003, -2), (key1236, 4), (key1130, 4), (key1022, 4)]

def rawRow13788 : Integer.Sparse Key := [(key1017, 4), (key1073, 4), (key1247, 4), (key1003, -2), (key1022, -2), (key1038, -2), (key1236, -2), (key1080, -2), (key1243, -2), (key1003, -2), (key1022, -2), (key1038, -2), (key1236, -2), (key1080, -2), (key1243, -2), (key1009, 4), (key1044, 4), (key1233, 4)]

def rawRow13789 : Integer.Sparse Key := [(key1017, 4), (key1247, 4), (key1073, 4), (key1022, -2), (key1003, -2), (key1236, -2), (key1038, -2), (key1243, -2), (key1080, -2), (key1022, -2), (key1003, -2), (key1236, -2), (key1038, -2), (key1243, -2), (key1080, -2), (key1009, 4), (key1233, 4), (key1044, 4)]

def rawRow13790 : Integer.Sparse Key := [(key1073, 4), (key1017, 4), (key1247, 4), (key1038, -2), (key1080, -2), (key1003, -2), (key1243, -2), (key1022, -2), (key1236, -2), (key1038, -2), (key1080, -2), (key1003, -2), (key1243, -2), (key1022, -2), (key1236, -2), (key1044, 4), (key1009, 4), (key1233, 4)]

def rawRow13791 : Integer.Sparse Key := [(key1073, 4), (key1247, 4), (key1017, 4), (key1080, -2), (key1038, -2), (key1243, -2), (key1003, -2), (key1236, -2), (key1022, -2), (key1080, -2), (key1038, -2), (key1243, -2), (key1003, -2), (key1236, -2), (key1022, -2), (key1044, 4), (key1233, 4), (key1009, 4)]

def rawRow13792 : Integer.Sparse Key := [(key1247, 4), (key1017, 4), (key1073, 4), (key1236, -2), (key1243, -2), (key1022, -2), (key1080, -2), (key1003, -2), (key1038, -2), (key1236, -2), (key1243, -2), (key1022, -2), (key1080, -2), (key1003, -2), (key1038, -2), (key1233, 4), (key1009, 4), (key1044, 4)]

def rawRow13793 : Integer.Sparse Key := [(key1247, 4), (key1073, 4), (key1017, 4), (key1243, -2), (key1236, -2), (key1080, -2), (key1022, -2), (key1038, -2), (key1003, -2), (key1243, -2), (key1236, -2), (key1080, -2), (key1022, -2), (key1038, -2), (key1003, -2), (key1233, 4), (key1044, 4), (key1009, 4)]

def rawRow13794 : Integer.Sparse Key := [(key1022, 4), (key1080, 4), (key1174, 4), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1009, -2), (key1022, -2), (key1044, -2), (key1130, -2), (key1080, -2), (key1159, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

def rawRow13795 : Integer.Sparse Key := [(key1022, 4), (key1174, 4), (key1080, 4), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1022, -2), (key1009, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1080, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

def rawRow13796 : Integer.Sparse Key := [(key1080, 4), (key1022, 4), (key1174, 4), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1044, -2), (key1080, -2), (key1009, -2), (key1159, -2), (key1022, -2), (key1130, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

def rawRow13797 : Integer.Sparse Key := [(key1080, 4), (key1174, 4), (key1022, 4), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1080, -2), (key1044, -2), (key1159, -2), (key1009, -2), (key1130, -2), (key1022, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

def rawRow13798 : Integer.Sparse Key := [(key1174, 4), (key1022, 4), (key1080, 4), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1130, -2), (key1159, -2), (key1022, -2), (key1080, -2), (key1009, -2), (key1044, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

def rawRow13799 : Integer.Sparse Key := [(key1174, 4), (key1080, 4), (key1022, 4), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1159, -2), (key1130, -2), (key1080, -2), (key1022, -2), (key1044, -2), (key1009, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

def rawRow13800 : Integer.Sparse Key := [(key1009, 4), (key1159, 4), (key1159, 4), (key1022, -2), (key1022, -2), (key1130, -2), (key1130, -2), (key1174, -2), (key1174, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

def rawRow13801 : Integer.Sparse Key := [(key1159, 4), (key1009, 4), (key1159, 4), (key1130, -2), (key1174, -2), (key1022, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

def rawRow13802 : Integer.Sparse Key := [(key1159, 4), (key1159, 4), (key1009, 4), (key1174, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1022, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

def rawRow13803 : Integer.Sparse Key := [(key1022, 4), (key1080, 4), (key1174, 4), (key1009, -2), (key1022, -2), (key1044, -2), (key1130, -2), (key1080, -2), (key1159, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

def rawRow13804 : Integer.Sparse Key := [(key1022, 4), (key1174, 4), (key1080, 4), (key1022, -2), (key1009, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1080, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

def rawRow13805 : Integer.Sparse Key := [(key1080, 4), (key1022, 4), (key1174, 4), (key1044, -2), (key1080, -2), (key1009, -2), (key1159, -2), (key1022, -2), (key1130, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

def rawRow13806 : Integer.Sparse Key := [(key1080, 4), (key1174, 4), (key1022, 4), (key1080, -2), (key1044, -2), (key1159, -2), (key1009, -2), (key1130, -2), (key1022, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

def rawRow13807 : Integer.Sparse Key := [(key1174, 4), (key1022, 4), (key1080, 4), (key1130, -2), (key1159, -2), (key1022, -2), (key1080, -2), (key1009, -2), (key1044, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

def rawRow13808 : Integer.Sparse Key := [(key1174, 4), (key1080, 4), (key1022, 4), (key1159, -2), (key1130, -2), (key1080, -2), (key1022, -2), (key1044, -2), (key1009, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

def rawRow13809 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key2868, -1), (key3021, -1), (key3025, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1), (key2657, 2), (key2918, 2), (key2922, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1)]

def rawRow13810 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2630, -1), (key2624, -1), (key2868, -1), (key2851, -1), (key3025, -1), (key3021, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1), (key2657, 2), (key2922, 2), (key2918, 2), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1)]

def rawRow13811 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, -1), (key3021, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2918, 2), (key2657, 2), (key2922, 2), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1)]

def rawRow13812 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key2868, -1), (key2630, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1), (key2918, 2), (key2922, 2), (key2657, 2), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1)]

def rawRow13813 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2868, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2624, -1), (key2851, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1), (key2922, 2), (key2657, 2), (key2918, 2), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1)]

def rawRow13814 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key3025, -1), (key2868, -1), (key3021, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2922, 2), (key2918, 2), (key2657, 2), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1)]

def rawRow13815 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2638, -1), (key2638, -1), (key2858, -1), (key2858, -1), (key3022, -1), (key3022, -1), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2657, -1), (key2657, -1), (key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1)]

def rawRow13816 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2858, -1), (key3022, -1), (key2638, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2752, -1), (key2918, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2752, -1)]

def rawRow13817 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key3022, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2918, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2752, -1), (key2657, -1)]

def rawRow13818 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2638, 2), (key2858, 2), (key3022, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1)]

def rawRow13819 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2638, 2), (key3022, 2), (key2858, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1)]

def rawRow13820 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2858, 2), (key2638, 2), (key3022, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1)]

def rawRow13821 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2858, 2), (key3022, 2), (key2638, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1)]

def rawRow13822 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key3022, 2), (key2638, 2), (key2858, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1)]

def rawRow13823 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3022, 2), (key2858, 2), (key2638, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1)]

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

def rawRow13824 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2630, 2), (key2704, 2), (key3021, 2), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2), (key2614, -1), (key2638, -1), (key2669, -1), (key2724, -1), (key2792, -1), (key2827, -1), (key2630, 2), (key2784, 2), (key2868, 2), (key2614, -1), (key2638, -1), (key2669, -1), (key2724, -1), (key2792, -1), (key2827, -1)]

def rawRow13825 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2630, 2), (key3021, 2), (key2704, 2), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2), (key2638, -1), (key2614, -1), (key2724, -1), (key2669, -1), (key2827, -1), (key2792, -1), (key2630, 2), (key2868, 2), (key2784, 2), (key2638, -1), (key2614, -1), (key2724, -1), (key2669, -1), (key2827, -1), (key2792, -1)]

def rawRow13826 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2704, 2), (key2630, 2), (key3021, 2), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, -1), (key2724, -1), (key2784, 2), (key2630, 2), (key2868, 2), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, -1), (key2724, -1)]

def rawRow13827 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, -1), (key2638, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, -1), (key2638, -1)]

def rawRow13828 : Integer.Sparse Key := [(key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3021, 2), (key2630, 2), (key2704, 2), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, -1), (key2669, -1), (key2868, 2), (key2630, 2), (key2784, 2), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, -1), (key2669, -1)]

def rawRow13829 : Integer.Sparse Key := [(key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3021, 2), (key2704, 2), (key2630, 2), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2630, 2), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, -1), (key2614, -1)]

def rawRow13830 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2638, 2), (key2792, 2), (key2858, 2), (key2614, -1), (key2630, -1), (key2669, -1), (key2704, -1), (key2784, -1), (key2807, -1)]

def rawRow13831 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2638, 2), (key2858, 2), (key2792, 2), (key2630, -1), (key2614, -1), (key2704, -1), (key2669, -1), (key2807, -1), (key2784, -1)]

def rawRow13832 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2792, 2), (key2638, 2), (key2858, 2), (key2669, -1), (key2784, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2704, -1)]

def rawRow13833 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2792, 2), (key2858, 2), (key2638, 2), (key2784, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2704, -1), (key2630, -1)]

def rawRow13834 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2858, 2), (key2638, 2), (key2792, 2), (key2704, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2614, -1), (key2669, -1)]

def rawRow13835 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2858, 2), (key2792, 2), (key2638, 2), (key2807, -1), (key2704, -1), (key2784, -1), (key2630, -1), (key2669, -1), (key2614, -1)]

def rawRow13836 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2), (key2638, -1), (key2638, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1)]

def rawRow13837 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2792, -1), (key2858, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1)]

def rawRow13838 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2), (key2858, -1), (key2792, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2638, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1)]

def rawRow13839 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2657, 2), (key2752, 2), (key2918, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2614, -1), (key2630, -1), (key2669, -1), (key2784, -1), (key2704, -1), (key2807, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1)]

def rawRow13840 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2657, 2), (key2918, 2), (key2752, 2), (key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2630, -1), (key2614, -1), (key2784, -1), (key2669, -1), (key2807, -1), (key2704, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1)]

def rawRow13841 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2752, 2), (key2657, 2), (key2918, 2), (key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2669, -1), (key2704, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1)]

def rawRow13842 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2918, 2), (key2657, 2), (key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2704, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2784, -1), (key2630, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1)]

def rawRow13843 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2784, -1), (key2807, -1), (key2630, -1), (key2704, -1), (key2614, -1), (key2669, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1)]

def rawRow13844 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2807, -1), (key2784, -1), (key2704, -1), (key2630, -1), (key2669, -1), (key2614, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1)]

def rawRow13845 : Integer.Sparse Key := [(key2420, 4), (key2495, 4), (key2495, 4), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2438, 4), (key2504, 4), (key2504, 4)]

def rawRow13846 : Integer.Sparse Key := [(key2495, 4), (key2420, 4), (key2495, 4), (key2495, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2504, 4), (key2438, 4), (key2504, 4)]

def rawRow13847 : Integer.Sparse Key := [(key2495, 4), (key2495, 4), (key2420, 4), (key2504, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2504, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2504, 4), (key2504, 4), (key2438, 4)]

def rawRow13848 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2504, 4), (key2420, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2427, 4), (key2427, 4), (key2495, 4)]

def rawRow13849 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2427, 4), (key2427, -2), (key2420, -2), (key2495, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2427, 4), (key2495, 4), (key2427, 4)]

def rawRow13850 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2427, 4), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2504, -2), (key2504, -2), (key2438, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, 4), (key2427, 4), (key2427, 4)]

def rawRow13851 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2504, 4), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2420, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2495, -2), (key2427, 4), (key2427, 4), (key2495, 4)]

def rawRow13852 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2427, 4), (key2438, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2427, 4), (key2495, 4), (key2427, 4)]

def rawRow13853 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2427, 4), (key2504, -2), (key2504, -2), (key2438, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2495, 4), (key2427, 4), (key2427, 4)]

def rawRow13854 : Integer.Sparse Key := [(key2438, 4), (key2438, 4), (key2438, 4), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2420, 4), (key2420, 4), (key2420, 4)]

def rawRow13855 : Integer.Sparse Key := [(key1050, -2), (key1050, -2), (key1058, -2), (key1058, 6), (key1050, -2), (key1050, -2), (key1058, -2), (key1050, 2), (key1050, 2), (key1136, 2), (key1136, 2), (key1138, 2), (key1138, 2), (key1058, -2), (key1138, -2), (key1138, -2), (key1058, 6), (key1058, -2), (key1138, -2), (key1138, -2)]

def rawRow13856 : Integer.Sparse Key := [(key1050, -2), (key1058, -2), (key1050, -2), (key1058, 6), (key1050, -2), (key1058, -2), (key1050, -2), (key1136, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1138, -2), (key1058, -2), (key1138, -2), (key1058, 6), (key1138, -2), (key1058, -2), (key1138, -2)]

def rawRow13857 : Integer.Sparse Key := [(key1058, -2), (key1050, -2), (key1050, -2), (key1058, 6), (key1058, -2), (key1050, -2), (key1050, -2), (key1138, 2), (key1136, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1050, 2), (key1138, -2), (key1138, -2), (key1058, -2), (key1058, 6), (key1138, -2), (key1138, -2), (key1058, -2)]

def rawRow13858 : Integer.Sparse Key := [(key1050, -2), (key1058, -2), (key1058, -2), (key1050, 6), (key1136, -2), (key1138, -2), (key1138, -2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1050, -2), (key1050, -2), (key1136, -2), (key1138, 6), (key1058, -2), (key1058, -2), (key1138, -2)]

def rawRow13859 : Integer.Sparse Key := [(key1058, -2), (key1050, -2), (key1058, -2), (key1050, 6), (key1138, -2), (key1136, -2), (key1138, -2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1050, -2), (key1136, -2), (key1050, -2), (key1138, 6), (key1058, -2), (key1138, -2), (key1058, -2)]

def rawRow13860 : Integer.Sparse Key := [(key1058, -2), (key1058, -2), (key1050, -2), (key1050, 6), (key1138, -2), (key1138, -2), (key1136, -2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1136, -2), (key1050, -2), (key1050, -2), (key1138, 6), (key1138, -2), (key1058, -2), (key1058, -2)]

def rawRow13861 : Integer.Sparse Key := [(key1136, -2), (key1138, -2), (key1138, -2), (key1138, 6), (key1050, -2), (key1058, -2), (key1058, -2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1058, -2), (key1058, -2), (key1138, -2), (key1050, 6), (key1050, -2), (key1050, -2), (key1136, -2)]

def rawRow13862 : Integer.Sparse Key := [(key1138, -2), (key1136, -2), (key1138, -2), (key1138, 6), (key1058, -2), (key1050, -2), (key1058, -2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1058, -2), (key1138, -2), (key1058, -2), (key1050, 6), (key1050, -2), (key1136, -2), (key1050, -2)]

def rawRow13863 : Integer.Sparse Key := [(key1138, -2), (key1138, -2), (key1136, -2), (key1138, 6), (key1058, -2), (key1058, -2), (key1050, -2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1138, -2), (key1058, -2), (key1058, -2), (key1050, 6), (key1136, -2), (key1050, -2), (key1050, -2)]

def rawRow13864 : Integer.Sparse Key := [(key1138, -2), (key1138, -2), (key1138, -2), (key1136, 6), (key1138, -2), (key1138, -2), (key1138, -2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1050, -2), (key1050, -2), (key1050, -2), (key1136, 6), (key1050, -2), (key1050, -2), (key1050, -2)]

def rawRow13865 : Integer.Sparse Key := [(key2416, -2), (key2416, -2), (key2423, -2), (key2423, 6), (key2416, -2), (key2416, -2), (key2423, -2), (key2416, 2), (key2416, 2), (key2489, 2), (key2489, 2), (key2491, 2), (key2491, 2), (key2423, -2), (key2491, -2), (key2491, -2), (key2423, 6), (key2423, -2), (key2491, -2), (key2491, -2)]

def rawRow13866 : Integer.Sparse Key := [(key2416, -2), (key2423, -2), (key2416, -2), (key2423, 6), (key2416, -2), (key2423, -2), (key2416, -2), (key2489, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2491, -2), (key2423, -2), (key2491, -2), (key2423, 6), (key2491, -2), (key2423, -2), (key2491, -2)]

def rawRow13867 : Integer.Sparse Key := [(key2423, -2), (key2416, -2), (key2416, -2), (key2423, 6), (key2423, -2), (key2416, -2), (key2416, -2), (key2491, 2), (key2489, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2416, 2), (key2491, -2), (key2491, -2), (key2423, -2), (key2423, 6), (key2491, -2), (key2491, -2), (key2423, -2)]

def rawRow13868 : Integer.Sparse Key := [(key2416, -2), (key2423, -2), (key2423, -2), (key2416, 6), (key2489, -2), (key2491, -2), (key2491, -2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2416, -2), (key2416, -2), (key2489, -2), (key2491, 6), (key2423, -2), (key2423, -2), (key2491, -2)]

def rawRow13869 : Integer.Sparse Key := [(key2423, -2), (key2416, -2), (key2423, -2), (key2416, 6), (key2491, -2), (key2489, -2), (key2491, -2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2416, -2), (key2489, -2), (key2416, -2), (key2491, 6), (key2423, -2), (key2491, -2), (key2423, -2)]

def rawRow13870 : Integer.Sparse Key := [(key2423, -2), (key2423, -2), (key2416, -2), (key2416, 6), (key2491, -2), (key2491, -2), (key2489, -2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2489, -2), (key2416, -2), (key2416, -2), (key2491, 6), (key2491, -2), (key2423, -2), (key2423, -2)]

def rawRow13871 : Integer.Sparse Key := [(key2489, -2), (key2491, -2), (key2491, -2), (key2491, 6), (key2416, -2), (key2423, -2), (key2423, -2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2423, -2), (key2423, -2), (key2491, -2), (key2416, 6), (key2416, -2), (key2416, -2), (key2489, -2)]

def rawRow13872 : Integer.Sparse Key := [(key2491, -2), (key2489, -2), (key2491, -2), (key2491, 6), (key2423, -2), (key2416, -2), (key2423, -2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2423, -2), (key2491, -2), (key2423, -2), (key2416, 6), (key2416, -2), (key2489, -2), (key2416, -2)]

def rawRow13873 : Integer.Sparse Key := [(key2491, -2), (key2491, -2), (key2489, -2), (key2491, 6), (key2423, -2), (key2423, -2), (key2416, -2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2491, -2), (key2423, -2), (key2423, -2), (key2416, 6), (key2489, -2), (key2416, -2), (key2416, -2)]

def rawRow13874 : Integer.Sparse Key := [(key2491, -2), (key2491, -2), (key2491, -2), (key2489, 6), (key2491, -2), (key2491, -2), (key2491, -2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2416, -2), (key2416, -2), (key2416, -2), (key2489, 6), (key2416, -2), (key2416, -2), (key2416, -2)]

def rawRow13875 : Integer.Sparse Key := [(key2677, 6), (key2677, -2), (key2708, -2), (key2708, -2), (key2677, 6), (key3045, -2), (key3094, -2), (key3094, -2), (key3045, -2), (key3059, -2), (key3059, -2), (key3045, -2), (key3094, -2), (key3094, -2), (key3059, 2), (key3059, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3122, 2)]

def rawRow13876 : Integer.Sparse Key := [(key2677, 6), (key2708, -2), (key2677, -2), (key2708, -2), (key2677, 6), (key3094, -2), (key3045, -2), (key3094, -2), (key3059, -2), (key3045, -2), (key3059, -2), (key3094, -2), (key3045, -2), (key3094, -2), (key3094, 2), (key3122, 2), (key3059, 2), (key3122, 2), (key3059, 2), (key3094, 2)]

def rawRow13877 : Integer.Sparse Key := [(key2677, 6), (key2708, -2), (key2708, -2), (key2677, -2), (key2677, 6), (key3094, -2), (key3094, -2), (key3045, -2), (key3059, -2), (key3059, -2), (key3045, -2), (key3094, -2), (key3094, -2), (key3045, -2), (key3122, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3094, 2), (key3059, 2)]

def rawRow13878 : Integer.Sparse Key := [(key2708, 6), (key2677, -2), (key2677, -2), (key2708, -2), (key2811, 6), (key2677, -2), (key3045, -2), (key3094, -2), (key3094, -2), (key3094, -2), (key3122, -2), (key3059, -2), (key3059, -2), (key3122, -2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

def rawRow13879 : Integer.Sparse Key := [(key2708, 6), (key2677, -2), (key2708, -2), (key2677, -2), (key2811, 6), (key2677, -2), (key3094, -2), (key3045, -2), (key3094, -2), (key3122, -2), (key3094, -2), (key3059, -2), (key3122, -2), (key3059, -2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

def rawRow13880 : Integer.Sparse Key := [(key2708, 6), (key2708, -2), (key2677, -2), (key2677, -2), (key2811, 6), (key2811, -2), (key2677, -2), (key3045, -2), (key3122, -2), (key3094, -2), (key3094, -2), (key3122, -2), (key3059, -2), (key3059, -2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

def rawRow13881 : Integer.Sparse Key := [(key2811, 6), (key2811, -2), (key2811, -2), (key2861, -2), (key2708, 6), (key2708, -2), (key2708, -2), (key2861, -2), (key2677, -2), (key2677, -2), (key2708, -2), (key2677, -2), (key3045, -2), (key3094, -2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

def rawRow13882 : Integer.Sparse Key := [(key2811, 6), (key2811, -2), (key2861, -2), (key2811, -2), (key2708, 6), (key2708, -2), (key2861, -2), (key2708, -2), (key2677, -2), (key2708, -2), (key2677, -2), (key2677, -2), (key3094, -2), (key3045, -2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

def rawRow13883 : Integer.Sparse Key := [(key2811, 6), (key2861, -2), (key2811, -2), (key2811, -2), (key2708, 6), (key2861, -2), (key2708, -2), (key2708, -2), (key2708, -2), (key2677, -2), (key2677, -2), (key2811, -2), (key2677, -2), (key3045, -2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

def rawRow13884 : Integer.Sparse Key := [(key2861, 6), (key2811, -2), (key2811, -2), (key2811, -2), (key2861, 6), (key2708, -2), (key2708, -2), (key2708, -2), (key2811, -2), (key2811, -2), (key2811, -2), (key2708, -2), (key2708, -2), (key2708, -2), (key2677, 2), (key2677, 2), (key2677, 2), (key3045, 2), (key3045, 2), (key3045, 2)]

def rawRow13885 : Integer.Sparse Key := [(key1047, -2), (key1047, -2), (key1057, -2), (key1057, 6), (key1047, -2), (key1047, -2), (key1057, -2), (key1047, 2), (key1047, 2), (key1133, 2), (key1133, 2), (key1137, 2), (key1137, 2), (key1057, -2), (key1137, -2), (key1137, -2), (key1057, 6), (key1057, -2), (key1137, -2), (key1137, -2)]

def rawRow13886 : Integer.Sparse Key := [(key1047, -2), (key1057, -2), (key1047, -2), (key1057, 6), (key1047, -2), (key1057, -2), (key1047, -2), (key1133, 2), (key1137, 2), (key1047, 2), (key1137, 2), (key1047, 2), (key1133, 2), (key1137, -2), (key1057, -2), (key1137, -2), (key1057, 6), (key1137, -2), (key1057, -2), (key1137, -2)]

def rawRow13887 : Integer.Sparse Key := [(key1057, -2), (key1047, -2), (key1047, -2), (key1057, 6), (key1057, -2), (key1047, -2), (key1047, -2), (key1137, 2), (key1133, 2), (key1137, 2), (key1047, 2), (key1133, 2), (key1047, 2), (key1137, -2), (key1137, -2), (key1057, -2), (key1057, 6), (key1137, -2), (key1137, -2), (key1057, -2)]

def rawRow13888 : Integer.Sparse Key := [(key1047, -2), (key1057, -2), (key1057, -2), (key1047, 6), (key1133, -2), (key1137, -2), (key1137, -2), (key1047, 2), (key1057, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1137, 2), (key1047, -2), (key1047, -2), (key1133, -2), (key1137, 6), (key1057, -2), (key1057, -2), (key1137, -2)]

def rawRow13889 : Integer.Sparse Key := [(key1057, -2), (key1047, -2), (key1057, -2), (key1047, 6), (key1137, -2), (key1133, -2), (key1137, -2), (key1057, 2), (key1047, 2), (key1137, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1047, -2), (key1133, -2), (key1047, -2), (key1137, 6), (key1057, -2), (key1137, -2), (key1057, -2)]

def rawRow13890 : Integer.Sparse Key := [(key1057, -2), (key1057, -2), (key1047, -2), (key1047, 6), (key1137, -2), (key1137, -2), (key1133, -2), (key1137, 2), (key1137, 2), (key1057, 2), (key1057, 2), (key1047, 2), (key1047, 2), (key1133, -2), (key1047, -2), (key1047, -2), (key1137, 6), (key1137, -2), (key1057, -2), (key1057, -2)]

def rawRow13891 : Integer.Sparse Key := [(key1133, -2), (key1137, -2), (key1137, -2), (key1137, 6), (key1047, -2), (key1057, -2), (key1057, -2), (key1047, 2), (key1057, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1137, 2), (key1057, -2), (key1057, -2), (key1137, -2), (key1047, 6), (key1047, -2), (key1047, -2), (key1133, -2)]

def rawRow13892 : Integer.Sparse Key := [(key1137, -2), (key1133, -2), (key1137, -2), (key1137, 6), (key1057, -2), (key1047, -2), (key1057, -2), (key1057, 2), (key1047, 2), (key1137, 2), (key1047, 2), (key1137, 2), (key1057, 2), (key1057, -2), (key1137, -2), (key1057, -2), (key1047, 6), (key1047, -2), (key1133, -2), (key1047, -2)]

def rawRow13893 : Integer.Sparse Key := [(key1137, -2), (key1137, -2), (key1133, -2), (key1137, 6), (key1057, -2), (key1057, -2), (key1047, -2), (key1137, 2), (key1137, 2), (key1057, 2), (key1057, 2), (key1047, 2), (key1047, 2), (key1137, -2), (key1057, -2), (key1057, -2), (key1047, 6), (key1133, -2), (key1047, -2), (key1047, -2)]

def rawRow13894 : Integer.Sparse Key := [(key1137, -2), (key1137, -2), (key1137, -2), (key1133, 6), (key1137, -2), (key1137, -2), (key1137, -2), (key1057, 2), (key1057, 2), (key1057, 2), (key1057, 2), (key1057, 2), (key1057, 2), (key1047, -2), (key1047, -2), (key1047, -2), (key1133, 6), (key1047, -2), (key1047, -2), (key1047, -2)]

def rawRow13895 : Integer.Sparse Key := [(key1055, 4), (key1143, 4), (key1143, 4), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1074, 4), (key1153, 4), (key1153, 4)]

def rawRow13896 : Integer.Sparse Key := [(key1143, 4), (key1055, 4), (key1143, 4), (key1143, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1153, 4), (key1074, 4), (key1153, 4)]

def rawRow13897 : Integer.Sparse Key := [(key1143, 4), (key1143, 4), (key1055, 4), (key1153, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1153, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1153, 4), (key1153, 4), (key1074, 4)]

def rawRow13898 : Integer.Sparse Key := [(key1063, 4), (key1063, 4), (key1153, 4), (key1055, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1063, 4), (key1063, 4), (key1143, 4)]

def rawRow13899 : Integer.Sparse Key := [(key1063, 4), (key1153, 4), (key1063, 4), (key1063, -2), (key1055, -2), (key1143, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1063, 4), (key1143, 4), (key1063, 4)]

def rawRow13900 : Integer.Sparse Key := [(key1153, 4), (key1063, 4), (key1063, 4), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1153, -2), (key1153, -2), (key1074, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, 4), (key1063, 4), (key1063, 4)]

def rawRow13901 : Integer.Sparse Key := [(key1063, 4), (key1063, 4), (key1153, 4), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1055, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1143, -2), (key1063, 4), (key1063, 4), (key1143, 4)]

def rawRow13902 : Integer.Sparse Key := [(key1063, 4), (key1153, 4), (key1063, 4), (key1074, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1063, 4), (key1143, 4), (key1063, 4)]

def rawRow13903 : Integer.Sparse Key := [(key1153, 4), (key1063, 4), (key1063, 4), (key1153, -2), (key1153, -2), (key1074, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1143, 4), (key1063, 4), (key1063, 4)]

def rawRow13904 : Integer.Sparse Key := [(key1074, 4), (key1074, 4), (key1074, 4), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1055, 4), (key1055, 4), (key1055, 4)]

def rawRow13905 : Integer.Sparse Key := [(key2681, -1), (key2681, -1), (key2815, -1), (key2815, -1), (key2817, -1), (key2817, -1), (key2688, 2), (key2817, 2), (key2817, 2), (key2681, -1), (key2681, -1), (key2815, -1), (key2815, -1), (key2817, -1), (key2817, -1), (key2712, 2), (key2712, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, -1), (key2714, -1), (key2817, -1), (key2817, -1), (key2863, -1), (key2863, -1), (key2688, 2), (key2817, 2), (key2817, 2), (key2714, -1), (key2714, -1), (key2817, -1), (key2817, -1), (key2863, -1), (key2863, -1)]

def rawRow13906 : Integer.Sparse Key := [(key2815, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2817, 2), (key2688, 2), (key2817, 2), (key2815, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2815, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2817, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2714, -1), (key2817, -1), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2714, -1), (key2817, -1)]

def rawRow13907 : Integer.Sparse Key := [(key2817, -1), (key2815, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, -1), (key2815, -1), (key2817, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2863, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2712, 2), (key2863, -1), (key2817, -1), (key2863, -1), (key2714, -1), (key2817, -1), (key2714, -1), (key2817, 2), (key2817, 2), (key2688, 2), (key2863, -1), (key2817, -1), (key2863, -1), (key2714, -1), (key2817, -1), (key2714, -1)]

def rawRow13908 : Integer.Sparse Key := [(key2681, -1), (key2688, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2681, 2), (key2681, 2), (key2815, 2), (key2712, -1), (key2714, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, -1), (key2712, -1), (key2681, -1), (key2815, -1), (key2712, -1), (key2815, -1), (key2714, 2), (key2714, 2), (key2863, 2), (key2688, -1), (key2714, -1), (key2688, -1), (key2817, -1), (key2714, -1), (key2817, -1)]

def rawRow13909 : Integer.Sparse Key := [(key2688, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2681, 2), (key2815, 2), (key2681, 2), (key2714, -1), (key2712, -1), (key2863, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2712, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2815, -1), (key2712, -1), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, -1), (key2688, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2714, -1)]

def rawRow13910 : Integer.Sparse Key := [(key2817, -1), (key2817, -1), (key2688, -1), (key2688, -1), (key2681, -1), (key2681, -1), (key2815, 2), (key2681, 2), (key2681, 2), (key2863, -1), (key2863, -1), (key2714, -1), (key2714, -1), (key2712, -1), (key2712, -1), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, -1), (key2815, -1), (key2712, -1), (key2712, -1), (key2681, -1), (key2681, -1), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, -1), (key2817, -1), (key2714, -1), (key2714, -1), (key2688, -1), (key2688, -1)]

def rawRow13911 : Integer.Sparse Key := [(key2712, -1), (key2714, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2863, -1), (key2714, 2), (key2714, 2), (key2863, 2), (key2681, -1), (key2688, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2688, -1), (key2714, -1), (key2688, -1), (key2817, -1), (key2714, -1), (key2817, -1), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, -1), (key2712, -1), (key2681, -1), (key2815, -1), (key2712, -1), (key2815, -1)]

def rawRow13912 : Integer.Sparse Key := [(key2714, -1), (key2712, -1), (key2863, -1), (key2712, -1), (key2863, -1), (key2714, -1), (key2714, 2), (key2863, 2), (key2714, 2), (key2688, -1), (key2681, -1), (key2817, -1), (key2681, -1), (key2817, -1), (key2688, -1), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2714, -1), (key2688, -1), (key2817, -1), (key2688, -1), (key2817, -1), (key2714, -1), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, -1), (key2681, -1), (key2815, -1), (key2681, -1), (key2815, -1), (key2712, -1)]

def rawRow13913 : Integer.Sparse Key := [(key2863, -1), (key2863, -1), (key2714, -1), (key2714, -1), (key2712, -1), (key2712, -1), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, -1), (key2817, -1), (key2688, -1), (key2688, -1), (key2681, -1), (key2681, -1), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2817, -1), (key2817, -1), (key2714, -1), (key2714, -1), (key2688, -1), (key2688, -1), (key2815, 2), (key2681, 2), (key2681, 2), (key2815, -1), (key2815, -1), (key2712, -1), (key2712, -1), (key2681, -1), (key2681, -1)]

def rawRow13914 : Integer.Sparse Key := [(key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2712, 2), (key2712, 2), (key2712, 2), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2714, -1), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2712, 2), (key2712, 2), (key2712, 2), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1), (key2681, -1)]

def rawRow13915 : Integer.Sparse Key := [(key3079, 4), (key3084, 4), (key3084, 4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3099, 12)]

def rawRow13916 : Integer.Sparse Key := [(key3084, 4), (key3079, 4), (key3084, 4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, 12)]

def rawRow13917 : Integer.Sparse Key := [(key3084, 4), (key3084, 4), (key3079, 4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, 12)]

def rawRow13918 : Integer.Sparse Key := [(key3084, 4), (key3084, 4), (key3099, 4), (key3079, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3099, -4), (key3084, 12)]

def rawRow13919 : Integer.Sparse Key := [(key3084, 4), (key3099, 4), (key3084, 4), (key3084, -4), (key3079, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, 12)]

def rawRow13920 : Integer.Sparse Key := [(key3099, 4), (key3084, 4), (key3084, 4), (key3084, -4), (key3084, -4), (key3079, -4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, 12)]

def rawRow13921 : Integer.Sparse Key := [(key3084, 4), (key3084, 4), (key3099, 4), (key3084, -4), (key3099, -4), (key3099, -4), (key3079, -4), (key3084, -4), (key3084, -4), (key3084, 12)]

def rawRow13922 : Integer.Sparse Key := [(key3084, 4), (key3099, 4), (key3084, 4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3079, -4), (key3084, -4), (key3084, 12)]

def rawRow13923 : Integer.Sparse Key := [(key3099, 4), (key3084, 4), (key3084, 4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3079, -4), (key3084, 12)]

def rawRow13924 : Integer.Sparse Key := [(key3099, 4), (key3099, 4), (key3099, 4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3079, 12)]

def rawRow13925 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2531, 4), (key2456, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2531, -2), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2520, 4), (key2520, 4), (key2561, 4)]

def rawRow13926 : Integer.Sparse Key := [(key2456, 4), (key2531, 4), (key2456, 4), (key2459, -2), (key2456, -2), (key2531, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, 4), (key2561, 4), (key2520, 4)]

def rawRow13927 : Integer.Sparse Key := [(key2531, 4), (key2456, 4), (key2456, 4), (key2531, -2), (key2531, -2), (key2459, -2), (key2459, -2), (key2456, -2), (key2456, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2561, 4), (key2520, 4), (key2520, 4)]

def rawRow13928 : Integer.Sparse Key := [(key2459, 4), (key2459, 4), (key2459, 4), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow13929 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2531, 4), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2456, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2531, -2), (key2520, 4), (key2520, 4), (key2561, 4)]

def rawRow13930 : Integer.Sparse Key := [(key2456, 4), (key2531, 4), (key2456, 4), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2520, 4), (key2561, 4), (key2520, 4)]

def rawRow13931 : Integer.Sparse Key := [(key2531, 4), (key2456, 4), (key2456, 4), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2531, -2), (key2531, -2), (key2459, -2), (key2459, -2), (key2456, -2), (key2456, -2), (key2561, 4), (key2520, 4), (key2520, 4)]

def rawRow13932 : Integer.Sparse Key := [(key2361, 4), (key2517, 4), (key2561, 4), (key2361, -2), (key2364, -2), (key2456, -2), (key2531, -2), (key2520, -2), (key2561, -2), (key2361, -2), (key2364, -2), (key2456, -2), (key2531, -2), (key2520, -2), (key2561, -2), (key2364, 4), (key2459, 4), (key2531, 4)]

def rawRow13933 : Integer.Sparse Key := [(key2361, 4), (key2561, 4), (key2517, 4), (key2364, -2), (key2361, -2), (key2531, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2364, -2), (key2361, -2), (key2531, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2364, 4), (key2531, 4), (key2459, 4)]

def rawRow13934 : Integer.Sparse Key := [(key2517, 4), (key2361, 4), (key2561, 4), (key2456, -2), (key2520, -2), (key2361, -2), (key2561, -2), (key2364, -2), (key2531, -2), (key2456, -2), (key2520, -2), (key2361, -2), (key2561, -2), (key2364, -2), (key2531, -2), (key2459, 4), (key2364, 4), (key2531, 4)]

def rawRow13935 : Integer.Sparse Key := [(key2517, 4), (key2561, 4), (key2361, 4), (key2520, -2), (key2456, -2), (key2561, -2), (key2361, -2), (key2531, -2), (key2364, -2), (key2520, -2), (key2456, -2), (key2561, -2), (key2361, -2), (key2531, -2), (key2364, -2), (key2459, 4), (key2531, 4), (key2364, 4)]

def rawRow13936 : Integer.Sparse Key := [(key2561, 4), (key2361, 4), (key2517, 4), (key2531, -2), (key2561, -2), (key2364, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2531, -2), (key2561, -2), (key2364, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2531, 4), (key2364, 4), (key2459, 4)]

def rawRow13937 : Integer.Sparse Key := [(key2561, 4), (key2517, 4), (key2361, 4), (key2561, -2), (key2531, -2), (key2520, -2), (key2364, -2), (key2456, -2), (key2361, -2), (key2561, -2), (key2531, -2), (key2520, -2), (key2364, -2), (key2456, -2), (key2361, -2), (key2531, 4), (key2459, 4), (key2364, 4)]

def rawRow13938 : Integer.Sparse Key := [(key2364, 4), (key2520, 4), (key2520, 4), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2364, -2), (key2364, -2), (key2459, -2), (key2459, -2), (key2520, -2), (key2520, -2), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow13939 : Integer.Sparse Key := [(key2520, 4), (key2364, 4), (key2520, 4), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow13940 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2364, 4), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2520, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2364, -2), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow13941 : Integer.Sparse Key := [(key2459, 4), (key2459, 4), (key2459, 4), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow13942 : Integer.Sparse Key := [(key2364, 4), (key2520, 4), (key2520, 4), (key2364, -2), (key2364, -2), (key2459, -2), (key2459, -2), (key2520, -2), (key2520, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow13943 : Integer.Sparse Key := [(key2520, 4), (key2364, 4), (key2520, 4), (key2459, -2), (key2520, -2), (key2364, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow13944 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2364, 4), (key2520, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2364, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow13945 : Integer.Sparse Key := [(key972, -2), (key977, -2), (key977, -2), (key977, 6), (key1086, -2), (key1091, -2), (key1091, -2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1091, -2), (key1091, -2), (key1181, -2), (key1162, 6), (key1162, -2), (key1162, -2), (key1218, -2)]

def rawRow13946 : Integer.Sparse Key := [(key977, -2), (key972, -2), (key977, -2), (key977, 6), (key1091, -2), (key1086, -2), (key1091, -2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, -2), (key1181, -2), (key1091, -2), (key1162, 6), (key1162, -2), (key1218, -2), (key1162, -2)]

def rawRow13947 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key972, -2), (key977, 6), (key1091, -2), (key1091, -2), (key1086, -2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1181, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key1218, -2), (key1162, -2), (key1162, -2)]

def rawRow13948 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key977, -2), (key972, 6), (key1181, -2), (key1181, -2), (key1181, -2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1218, 6), (key1162, -2), (key1162, -2), (key1162, -2)]

def rawRow13949 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key972, -2), (key977, -2), (key977, -2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1162, -2), (key1162, -2), (key1218, -2), (key977, 6), (key1091, -2), (key1091, -2), (key1181, -2)]

def rawRow13950 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1091, -2), (key1162, 6), (key977, -2), (key972, -2), (key977, -2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1162, -2), (key1218, -2), (key1162, -2), (key977, 6), (key1091, -2), (key1181, -2), (key1091, -2)]

def rawRow13951 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1086, -2), (key1162, 6), (key977, -2), (key977, -2), (key972, -2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1218, -2), (key1162, -2), (key1162, -2), (key977, 6), (key1181, -2), (key1091, -2), (key1091, -2)]

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

def rawRow13952 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1162, -2), (key1091, 6), (key1086, -2), (key1091, -2), (key1162, -2), (key972, 2), (key977, 2), (key1086, 2), (key1181, 2), (key1162, 2), (key1218, 2), (key977, -2), (key1091, -2), (key1181, -2), (key1091, 6), (key977, -2), (key1091, -2), (key1181, -2)]

def rawRow13953 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1162, -2), (key1091, 6), (key1091, -2), (key1086, -2), (key1162, -2), (key977, 2), (key972, 2), (key1181, 2), (key1086, 2), (key1218, 2), (key1162, 2), (key977, -2), (key1181, -2), (key1091, -2), (key1091, 6), (key977, -2), (key1181, -2), (key1091, -2)]

def rawRow13954 : Integer.Sparse Key := [(key1086, -2), (key1162, -2), (key1091, -2), (key1091, 6), (key1086, -2), (key1162, -2), (key1091, -2), (key1086, 2), (key1162, 2), (key972, 2), (key1218, 2), (key977, 2), (key1181, 2), (key1091, -2), (key977, -2), (key1181, -2), (key1091, 6), (key1091, -2), (key977, -2), (key1181, -2)]

def rawRow13955 : Integer.Sparse Key := [(key1162, -2), (key1086, -2), (key1091, -2), (key1091, 6), (key1162, -2), (key1086, -2), (key1091, -2), (key1162, 2), (key1086, 2), (key1218, 2), (key972, 2), (key1181, 2), (key977, 2), (key1091, -2), (key1181, -2), (key977, -2), (key1091, 6), (key1091, -2), (key1181, -2), (key977, -2)]

def rawRow13956 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1086, -2), (key1091, 6), (key1091, -2), (key1162, -2), (key1086, -2), (key1181, 2), (key1218, 2), (key977, 2), (key1162, 2), (key972, 2), (key1086, 2), (key1181, -2), (key977, -2), (key1091, -2), (key1091, 6), (key1181, -2), (key977, -2), (key1091, -2)]

def rawRow13957 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1086, -2), (key1091, 6), (key1162, -2), (key1091, -2), (key1086, -2), (key1218, 2), (key1181, 2), (key1162, 2), (key977, 2), (key1086, 2), (key972, 2), (key1181, -2), (key1091, -2), (key977, -2), (key1091, 6), (key1181, -2), (key1091, -2), (key977, -2)]

def rawRow13958 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1162, -2), (key1086, 6), (key1181, -2), (key1181, -2), (key1218, -2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1181, 6), (key977, -2), (key1091, -2), (key1091, -2)]

def rawRow13959 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1091, -2), (key1086, 6), (key1181, -2), (key1218, -2), (key1181, -2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1181, 6), (key1091, -2), (key977, -2), (key1091, -2)]

def rawRow13960 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key1218, -2), (key1181, -2), (key1181, -2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1181, 6), (key1091, -2), (key1091, -2), (key977, -2)]

def rawRow13961 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1181, -2), (key1218, 6), (key977, -2), (key977, -2), (key977, -2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1162, -2), (key1162, -2), (key1162, -2), (key972, 6), (key1086, -2), (key1086, -2), (key1086, -2)]

def rawRow13962 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1218, -2), (key1181, 6), (key1091, -2), (key1091, -2), (key1162, -2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key977, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key972, -2), (key1086, -2), (key1086, -2)]

def rawRow13963 : Integer.Sparse Key := [(key1181, -2), (key1218, -2), (key1181, -2), (key1181, 6), (key1091, -2), (key1162, -2), (key1091, -2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, -2), (key977, -2), (key1091, -2), (key1086, 6), (key1086, -2), (key972, -2), (key1086, -2)]

def rawRow13964 : Integer.Sparse Key := [(key1218, -2), (key1181, -2), (key1181, -2), (key1181, 6), (key1162, -2), (key1091, -2), (key1091, -2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1091, -2), (key1091, -2), (key977, -2), (key1086, 6), (key1086, -2), (key1086, -2), (key972, -2)]

def rawRow13965 : Integer.Sparse Key := [(key2354, -2), (key2358, -2), (key2358, -2), (key2358, 6), (key2449, -2), (key2453, -2), (key2453, -2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2453, -2), (key2453, -2), (key2529, -2), (key2514, 6), (key2514, -2), (key2514, -2), (key2559, -2)]

def rawRow13966 : Integer.Sparse Key := [(key2358, -2), (key2354, -2), (key2358, -2), (key2358, 6), (key2453, -2), (key2449, -2), (key2453, -2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, -2), (key2529, -2), (key2453, -2), (key2514, 6), (key2514, -2), (key2559, -2), (key2514, -2)]

def rawRow13967 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2354, -2), (key2358, 6), (key2453, -2), (key2453, -2), (key2449, -2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2529, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2559, -2), (key2514, -2), (key2514, -2)]

def rawRow13968 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2358, -2), (key2354, 6), (key2529, -2), (key2529, -2), (key2529, -2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2449, -2), (key2449, -2), (key2449, -2), (key2559, 6), (key2514, -2), (key2514, -2), (key2514, -2)]

def rawRow13969 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2354, -2), (key2358, -2), (key2358, -2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2514, -2), (key2514, -2), (key2559, -2), (key2358, 6), (key2453, -2), (key2453, -2), (key2529, -2)]

def rawRow13970 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2453, -2), (key2514, 6), (key2358, -2), (key2354, -2), (key2358, -2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2514, -2), (key2559, -2), (key2514, -2), (key2358, 6), (key2453, -2), (key2529, -2), (key2453, -2)]

def rawRow13971 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2449, -2), (key2514, 6), (key2358, -2), (key2358, -2), (key2354, -2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2559, -2), (key2514, -2), (key2514, -2), (key2358, 6), (key2529, -2), (key2453, -2), (key2453, -2)]

def rawRow13972 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2514, -2), (key2453, 6), (key2449, -2), (key2453, -2), (key2514, -2), (key2354, 2), (key2358, 2), (key2449, 2), (key2529, 2), (key2514, 2), (key2559, 2), (key2358, -2), (key2453, -2), (key2529, -2), (key2453, 6), (key2358, -2), (key2453, -2), (key2529, -2)]

def rawRow13973 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2514, -2), (key2453, 6), (key2453, -2), (key2449, -2), (key2514, -2), (key2358, 2), (key2354, 2), (key2529, 2), (key2449, 2), (key2559, 2), (key2514, 2), (key2358, -2), (key2529, -2), (key2453, -2), (key2453, 6), (key2358, -2), (key2529, -2), (key2453, -2)]

def rawRow13974 : Integer.Sparse Key := [(key2449, -2), (key2514, -2), (key2453, -2), (key2453, 6), (key2449, -2), (key2514, -2), (key2453, -2), (key2449, 2), (key2514, 2), (key2354, 2), (key2559, 2), (key2358, 2), (key2529, 2), (key2453, -2), (key2358, -2), (key2529, -2), (key2453, 6), (key2453, -2), (key2358, -2), (key2529, -2)]

def rawRow13975 : Integer.Sparse Key := [(key2514, -2), (key2449, -2), (key2453, -2), (key2453, 6), (key2514, -2), (key2449, -2), (key2453, -2), (key2514, 2), (key2449, 2), (key2559, 2), (key2354, 2), (key2529, 2), (key2358, 2), (key2453, -2), (key2529, -2), (key2358, -2), (key2453, 6), (key2453, -2), (key2529, -2), (key2358, -2)]

def rawRow13976 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2449, -2), (key2453, 6), (key2453, -2), (key2514, -2), (key2449, -2), (key2529, 2), (key2559, 2), (key2358, 2), (key2514, 2), (key2354, 2), (key2449, 2), (key2529, -2), (key2358, -2), (key2453, -2), (key2453, 6), (key2529, -2), (key2358, -2), (key2453, -2)]

def rawRow13977 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2449, -2), (key2453, 6), (key2514, -2), (key2453, -2), (key2449, -2), (key2559, 2), (key2529, 2), (key2514, 2), (key2358, 2), (key2449, 2), (key2354, 2), (key2529, -2), (key2453, -2), (key2358, -2), (key2453, 6), (key2529, -2), (key2453, -2), (key2358, -2)]

def rawRow13978 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2514, -2), (key2449, 6), (key2529, -2), (key2529, -2), (key2559, -2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2354, -2), (key2449, -2), (key2449, -2), (key2529, 6), (key2358, -2), (key2453, -2), (key2453, -2)]

def rawRow13979 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2453, -2), (key2449, 6), (key2529, -2), (key2559, -2), (key2529, -2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2449, -2), (key2354, -2), (key2449, -2), (key2529, 6), (key2453, -2), (key2358, -2), (key2453, -2)]

def rawRow13980 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2559, -2), (key2529, -2), (key2529, -2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2449, -2), (key2449, -2), (key2354, -2), (key2529, 6), (key2453, -2), (key2453, -2), (key2358, -2)]

def rawRow13981 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2529, -2), (key2559, 6), (key2358, -2), (key2358, -2), (key2358, -2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2514, -2), (key2514, -2), (key2514, -2), (key2354, 6), (key2449, -2), (key2449, -2), (key2449, -2)]

def rawRow13982 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2559, -2), (key2529, 6), (key2453, -2), (key2453, -2), (key2514, -2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2358, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2354, -2), (key2449, -2), (key2449, -2)]

def rawRow13983 : Integer.Sparse Key := [(key2529, -2), (key2559, -2), (key2529, -2), (key2529, 6), (key2453, -2), (key2514, -2), (key2453, -2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, -2), (key2358, -2), (key2453, -2), (key2449, 6), (key2449, -2), (key2354, -2), (key2449, -2)]

def rawRow13984 : Integer.Sparse Key := [(key2559, -2), (key2529, -2), (key2529, -2), (key2529, 6), (key2514, -2), (key2453, -2), (key2453, -2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2453, -2), (key2453, -2), (key2358, -2), (key2449, 6), (key2449, -2), (key2449, -2), (key2354, -2)]

def rawRow13985 : Integer.Sparse Key := [(key2369, 6), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, 6), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, -2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

def rawRow13986 : Integer.Sparse Key := [(key2369, 6), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, 6), (key2397, -2), (key2431, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, -2), (key2463, -2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

def rawRow13987 : Integer.Sparse Key := [(key2369, 6), (key2384, -2), (key2369, -2), (key2369, -2), (key2397, 6), (key2431, -2), (key2397, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, -2), (key2463, -2), (key2463, -2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

def rawRow13988 : Integer.Sparse Key := [(key2384, 6), (key2369, -2), (key2369, -2), (key2369, -2), (key2431, 6), (key2397, -2), (key2397, -2), (key2397, -2), (key2497, -2), (key2497, -2), (key2497, -2), (key2474, -2), (key2474, -2), (key2474, -2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

def rawRow13989 : Integer.Sparse Key := [(key2397, 6), (key2463, -2), (key2463, -2), (key2474, -2), (key2369, 6), (key2463, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

def rawRow13990 : Integer.Sparse Key := [(key2397, 6), (key2463, -2), (key2474, -2), (key2463, -2), (key2369, 6), (key2463, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, -2), (key2431, -2), (key2397, -2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

def rawRow13991 : Integer.Sparse Key := [(key2397, 6), (key2474, -2), (key2463, -2), (key2463, -2), (key2369, 6), (key2497, -2), (key2463, -2), (key2463, -2), (key2384, -2), (key2369, -2), (key2369, -2), (key2431, -2), (key2397, -2), (key2397, -2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

def rawRow13992 : Integer.Sparse Key := [(key2463, 6), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, 6), (key2369, -2), (key2463, -2), (key2497, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2369, 2), (key2384, 2), (key2397, 2), (key2431, 2), (key2474, 2), (key2497, 2)]

def rawRow13993 : Integer.Sparse Key := [(key2463, 6), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, 6), (key2369, -2), (key2497, -2), (key2463, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2463, -2), (key2384, 2), (key2369, 2), (key2431, 2), (key2397, 2), (key2497, 2), (key2474, 2)]

def rawRow13994 : Integer.Sparse Key := [(key2463, 6), (key2463, -2), (key2397, -2), (key2474, -2), (key2463, 6), (key2463, -2), (key2369, -2), (key2497, -2), (key2463, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2397, 2), (key2474, 2), (key2369, 2), (key2497, 2), (key2384, 2), (key2431, 2)]

def rawRow13995 : Integer.Sparse Key := [(key2463, 6), (key2463, -2), (key2474, -2), (key2397, -2), (key2463, 6), (key2463, -2), (key2497, -2), (key2369, -2), (key2463, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2474, 2), (key2397, 2), (key2497, 2), (key2369, 2), (key2431, 2), (key2384, 2)]

def rawRow13996 : Integer.Sparse Key := [(key2463, 6), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, 6), (key2497, -2), (key2369, -2), (key2463, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2463, -2), (key2431, 2), (key2497, 2), (key2384, 2), (key2474, 2), (key2369, 2), (key2397, 2)]

def rawRow13997 : Integer.Sparse Key := [(key2463, 6), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, 6), (key2497, -2), (key2463, -2), (key2369, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2497, 2), (key2431, 2), (key2474, 2), (key2384, 2), (key2397, 2), (key2369, 2)]

def rawRow13998 : Integer.Sparse Key := [(key2474, 6), (key2397, -2), (key2463, -2), (key2463, -2), (key2497, 6), (key2369, -2), (key2463, -2), (key2463, -2), (key2431, -2), (key2497, -2), (key2497, -2), (key2384, -2), (key2474, -2), (key2474, -2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

def rawRow13999 : Integer.Sparse Key := [(key2474, 6), (key2463, -2), (key2397, -2), (key2463, -2), (key2497, 6), (key2463, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, -2), (key2384, -2), (key2474, -2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

def rawRow14000 : Integer.Sparse Key := [(key2474, 6), (key2463, -2), (key2463, -2), (key2397, -2), (key2497, 6), (key2463, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

def rawRow14001 : Integer.Sparse Key := [(key2431, 6), (key2497, -2), (key2497, -2), (key2497, -2), (key2384, 6), (key2474, -2), (key2474, -2), (key2474, -2), (key2369, -2), (key2369, -2), (key2369, -2), (key2397, -2), (key2397, -2), (key2397, -2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

def rawRow14002 : Integer.Sparse Key := [(key2497, 6), (key2431, -2), (key2497, -2), (key2497, -2), (key2474, 6), (key2384, -2), (key2474, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, -2), (key2463, -2), (key2463, -2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

def rawRow14003 : Integer.Sparse Key := [(key2497, 6), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, 6), (key2474, -2), (key2384, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, -2), (key2463, -2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

def rawRow14004 : Integer.Sparse Key := [(key2497, 6), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, 6), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, -2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

def rawRow14005 : Integer.Sparse Key := [(key971, -2), (key975, -2), (key975, -2), (key975, 6), (key1085, -2), (key1089, -2), (key1089, -2), (key1085, 2), (key1089, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1179, 2), (key1089, -2), (key1089, -2), (key1179, -2), (key1161, 6), (key1161, -2), (key1161, -2), (key1217, -2)]

def rawRow14006 : Integer.Sparse Key := [(key975, -2), (key971, -2), (key975, -2), (key975, 6), (key1089, -2), (key1085, -2), (key1089, -2), (key1089, 2), (key1085, 2), (key1179, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1089, -2), (key1179, -2), (key1089, -2), (key1161, 6), (key1161, -2), (key1217, -2), (key1161, -2)]

def rawRow14007 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key971, -2), (key975, 6), (key1089, -2), (key1089, -2), (key1085, -2), (key1179, 2), (key1179, 2), (key1089, 2), (key1089, 2), (key1085, 2), (key1085, 2), (key1179, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key1217, -2), (key1161, -2), (key1161, -2)]

def rawRow14008 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key975, -2), (key971, 6), (key1179, -2), (key1179, -2), (key1179, -2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1217, 6), (key1161, -2), (key1161, -2), (key1161, -2)]

def rawRow14009 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key971, -2), (key975, -2), (key975, -2), (key1085, 2), (key1089, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1179, 2), (key1161, -2), (key1161, -2), (key1217, -2), (key975, 6), (key1089, -2), (key1089, -2), (key1179, -2)]

def rawRow14010 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1089, -2), (key1161, 6), (key975, -2), (key971, -2), (key975, -2), (key1089, 2), (key1085, 2), (key1179, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1161, -2), (key1217, -2), (key1161, -2), (key975, 6), (key1089, -2), (key1179, -2), (key1089, -2)]

def rawRow14011 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1085, -2), (key1161, 6), (key975, -2), (key975, -2), (key971, -2), (key1179, 2), (key1179, 2), (key1089, 2), (key1089, 2), (key1085, 2), (key1085, 2), (key1217, -2), (key1161, -2), (key1161, -2), (key975, 6), (key1179, -2), (key1089, -2), (key1089, -2)]

def rawRow14012 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1161, -2), (key1089, 6), (key1085, -2), (key1089, -2), (key1161, -2), (key971, 2), (key975, 2), (key1085, 2), (key1179, 2), (key1161, 2), (key1217, 2), (key975, -2), (key1089, -2), (key1179, -2), (key1089, 6), (key975, -2), (key1089, -2), (key1179, -2)]

def rawRow14013 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1161, -2), (key1089, 6), (key1089, -2), (key1085, -2), (key1161, -2), (key975, 2), (key971, 2), (key1179, 2), (key1085, 2), (key1217, 2), (key1161, 2), (key975, -2), (key1179, -2), (key1089, -2), (key1089, 6), (key975, -2), (key1179, -2), (key1089, -2)]

def rawRow14014 : Integer.Sparse Key := [(key1085, -2), (key1161, -2), (key1089, -2), (key1089, 6), (key1085, -2), (key1161, -2), (key1089, -2), (key1085, 2), (key1161, 2), (key971, 2), (key1217, 2), (key975, 2), (key1179, 2), (key1089, -2), (key975, -2), (key1179, -2), (key1089, 6), (key1089, -2), (key975, -2), (key1179, -2)]

def rawRow14015 : Integer.Sparse Key := [(key1161, -2), (key1085, -2), (key1089, -2), (key1089, 6), (key1161, -2), (key1085, -2), (key1089, -2), (key1161, 2), (key1085, 2), (key1217, 2), (key971, 2), (key1179, 2), (key975, 2), (key1089, -2), (key1179, -2), (key975, -2), (key1089, 6), (key1089, -2), (key1179, -2), (key975, -2)]

def rawRow14016 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1085, -2), (key1089, 6), (key1089, -2), (key1161, -2), (key1085, -2), (key1179, 2), (key1217, 2), (key975, 2), (key1161, 2), (key971, 2), (key1085, 2), (key1179, -2), (key975, -2), (key1089, -2), (key1089, 6), (key1179, -2), (key975, -2), (key1089, -2)]

def rawRow14017 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1085, -2), (key1089, 6), (key1161, -2), (key1089, -2), (key1085, -2), (key1217, 2), (key1179, 2), (key1161, 2), (key975, 2), (key1085, 2), (key971, 2), (key1179, -2), (key1089, -2), (key975, -2), (key1089, 6), (key1179, -2), (key1089, -2), (key975, -2)]

def rawRow14018 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1161, -2), (key1085, 6), (key1179, -2), (key1179, -2), (key1217, -2), (key975, 2), (key975, 2), (key1089, 2), (key1089, 2), (key1161, 2), (key1161, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1179, 6), (key975, -2), (key1089, -2), (key1089, -2)]

def rawRow14019 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1089, -2), (key1085, 6), (key1179, -2), (key1217, -2), (key1179, -2), (key1089, 2), (key1161, 2), (key975, 2), (key1161, 2), (key975, 2), (key1089, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1179, 6), (key1089, -2), (key975, -2), (key1089, -2)]

def rawRow14020 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key1217, -2), (key1179, -2), (key1179, -2), (key1161, 2), (key1089, 2), (key1161, 2), (key975, 2), (key1089, 2), (key975, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1179, 6), (key1089, -2), (key1089, -2), (key975, -2)]

def rawRow14021 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1179, -2), (key1217, 6), (key975, -2), (key975, -2), (key975, -2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1161, -2), (key1161, -2), (key1161, -2), (key971, 6), (key1085, -2), (key1085, -2), (key1085, -2)]

def rawRow14022 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1217, -2), (key1179, 6), (key1089, -2), (key1089, -2), (key1161, -2), (key975, 2), (key975, 2), (key1089, 2), (key1089, 2), (key1161, 2), (key1161, 2), (key975, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key971, -2), (key1085, -2), (key1085, -2)]

def rawRow14023 : Integer.Sparse Key := [(key1179, -2), (key1217, -2), (key1179, -2), (key1179, 6), (key1089, -2), (key1161, -2), (key1089, -2), (key1089, 2), (key1161, 2), (key975, 2), (key1161, 2), (key975, 2), (key1089, 2), (key1089, -2), (key975, -2), (key1089, -2), (key1085, 6), (key1085, -2), (key971, -2), (key1085, -2)]

def rawRow14024 : Integer.Sparse Key := [(key1217, -2), (key1179, -2), (key1179, -2), (key1179, 6), (key1161, -2), (key1089, -2), (key1089, -2), (key1161, 2), (key1089, 2), (key1161, 2), (key975, 2), (key1089, 2), (key975, 2), (key1089, -2), (key1089, -2), (key975, -2), (key1085, 6), (key1085, -2), (key1085, -2), (key971, -2)]

def rawRow14025 : Integer.Sparse Key := [(key1095, 4), (key1095, 4), (key1184, 4), (key1095, -2), (key1099, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1184, -2), (key1166, -2), (key1170, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1221, -2), (key1170, 4), (key1170, 4), (key1221, 4)]

def rawRow14026 : Integer.Sparse Key := [(key1095, 4), (key1184, 4), (key1095, 4), (key1099, -2), (key1095, -2), (key1184, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1170, -2), (key1166, -2), (key1221, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1170, 4), (key1221, 4), (key1170, 4)]

def rawRow14027 : Integer.Sparse Key := [(key1184, 4), (key1095, 4), (key1095, 4), (key1184, -2), (key1184, -2), (key1099, -2), (key1099, -2), (key1095, -2), (key1095, -2), (key1221, -2), (key1221, -2), (key1170, -2), (key1170, -2), (key1166, -2), (key1166, -2), (key1221, 4), (key1170, 4), (key1170, 4)]

def rawRow14028 : Integer.Sparse Key := [(key1099, 4), (key1099, 4), (key1099, 4), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1166, 4), (key1166, 4), (key1166, 4)]

def rawRow14029 : Integer.Sparse Key := [(key1095, 4), (key1095, 4), (key1184, 4), (key1166, -2), (key1170, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1221, -2), (key1095, -2), (key1099, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1184, -2), (key1170, 4), (key1170, 4), (key1221, 4)]

def rawRow14030 : Integer.Sparse Key := [(key1095, 4), (key1184, 4), (key1095, 4), (key1170, -2), (key1166, -2), (key1221, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1099, -2), (key1095, -2), (key1184, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1170, 4), (key1221, 4), (key1170, 4)]

def rawRow14031 : Integer.Sparse Key := [(key1184, 4), (key1095, 4), (key1095, 4), (key1221, -2), (key1221, -2), (key1170, -2), (key1170, -2), (key1166, -2), (key1166, -2), (key1184, -2), (key1184, -2), (key1099, -2), (key1099, -2), (key1095, -2), (key1095, -2), (key1221, 4), (key1170, 4), (key1170, 4)]

def rawRow14032 : Integer.Sparse Key := [(key981, 4), (key1166, 4), (key1221, 4), (key981, -2), (key985, -2), (key1095, -2), (key1184, -2), (key1170, -2), (key1221, -2), (key981, -2), (key985, -2), (key1095, -2), (key1184, -2), (key1170, -2), (key1221, -2), (key985, 4), (key1099, 4), (key1184, 4)]

def rawRow14033 : Integer.Sparse Key := [(key981, 4), (key1221, 4), (key1166, 4), (key985, -2), (key981, -2), (key1184, -2), (key1095, -2), (key1221, -2), (key1170, -2), (key985, -2), (key981, -2), (key1184, -2), (key1095, -2), (key1221, -2), (key1170, -2), (key985, 4), (key1184, 4), (key1099, 4)]

def rawRow14034 : Integer.Sparse Key := [(key1166, 4), (key981, 4), (key1221, 4), (key1095, -2), (key1170, -2), (key981, -2), (key1221, -2), (key985, -2), (key1184, -2), (key1095, -2), (key1170, -2), (key981, -2), (key1221, -2), (key985, -2), (key1184, -2), (key1099, 4), (key985, 4), (key1184, 4)]

def rawRow14035 : Integer.Sparse Key := [(key1166, 4), (key1221, 4), (key981, 4), (key1170, -2), (key1095, -2), (key1221, -2), (key981, -2), (key1184, -2), (key985, -2), (key1170, -2), (key1095, -2), (key1221, -2), (key981, -2), (key1184, -2), (key985, -2), (key1099, 4), (key1184, 4), (key985, 4)]

def rawRow14036 : Integer.Sparse Key := [(key1221, 4), (key981, 4), (key1166, 4), (key1184, -2), (key1221, -2), (key985, -2), (key1170, -2), (key981, -2), (key1095, -2), (key1184, -2), (key1221, -2), (key985, -2), (key1170, -2), (key981, -2), (key1095, -2), (key1184, 4), (key985, 4), (key1099, 4)]

def rawRow14037 : Integer.Sparse Key := [(key1221, 4), (key1166, 4), (key981, 4), (key1221, -2), (key1184, -2), (key1170, -2), (key985, -2), (key1095, -2), (key981, -2), (key1221, -2), (key1184, -2), (key1170, -2), (key985, -2), (key1095, -2), (key981, -2), (key1184, 4), (key1099, 4), (key985, 4)]

def rawRow14038 : Integer.Sparse Key := [(key985, 4), (key1170, 4), (key1170, 4), (key981, -2), (key981, -2), (key1095, -2), (key1095, -2), (key1166, -2), (key1166, -2), (key985, -2), (key985, -2), (key1099, -2), (key1099, -2), (key1170, -2), (key1170, -2), (key981, 4), (key1095, 4), (key1095, 4)]

def rawRow14039 : Integer.Sparse Key := [(key1170, 4), (key985, 4), (key1170, 4), (key1095, -2), (key1166, -2), (key981, -2), (key1166, -2), (key981, -2), (key1095, -2), (key1099, -2), (key1170, -2), (key985, -2), (key1170, -2), (key985, -2), (key1099, -2), (key1095, 4), (key981, 4), (key1095, 4)]

def rawRow14040 : Integer.Sparse Key := [(key1170, 4), (key1170, 4), (key985, 4), (key1166, -2), (key1095, -2), (key1166, -2), (key981, -2), (key1095, -2), (key981, -2), (key1170, -2), (key1099, -2), (key1170, -2), (key985, -2), (key1099, -2), (key985, -2), (key1095, 4), (key1095, 4), (key981, 4)]

def rawRow14041 : Integer.Sparse Key := [(key1099, 4), (key1099, 4), (key1099, 4), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1166, 4), (key1166, 4), (key1166, 4)]

def rawRow14042 : Integer.Sparse Key := [(key985, 4), (key1170, 4), (key1170, 4), (key985, -2), (key985, -2), (key1099, -2), (key1099, -2), (key1170, -2), (key1170, -2), (key981, -2), (key981, -2), (key1095, -2), (key1095, -2), (key1166, -2), (key1166, -2), (key981, 4), (key1095, 4), (key1095, 4)]

def rawRow14043 : Integer.Sparse Key := [(key1170, 4), (key985, 4), (key1170, 4), (key1099, -2), (key1170, -2), (key985, -2), (key1170, -2), (key985, -2), (key1099, -2), (key1095, -2), (key1166, -2), (key981, -2), (key1166, -2), (key981, -2), (key1095, -2), (key1095, 4), (key981, 4), (key1095, 4)]

def rawRow14044 : Integer.Sparse Key := [(key1170, 4), (key1170, 4), (key985, 4), (key1170, -2), (key1099, -2), (key1170, -2), (key985, -2), (key1099, -2), (key985, -2), (key1166, -2), (key1095, -2), (key1166, -2), (key981, -2), (key1095, -2), (key981, -2), (key1095, 4), (key1095, 4), (key981, 4)]

def rawRow14045 : Integer.Sparse Key := [(key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2767, 2), (key2767, 2), (key2930, 2), (key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2844, -1), (key2888, -1), (key2844, -1), (key2967, -1), (key2888, -1), (key2967, -1), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, -1), (key2909, -1), (key2875, -1), (key2988, -1), (key2909, -1), (key2988, -1)]

def rawRow14046 : Integer.Sparse Key := [(key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2767, 2), (key2930, 2), (key2767, 2), (key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2888, -1), (key2844, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2888, -1), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, -1), (key2875, -1), (key2988, -1), (key2875, -1), (key2988, -1), (key2909, -1)]

def rawRow14047 : Integer.Sparse Key := [(key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2967, -1), (key2967, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1), (key2988, 2), (key2875, 2), (key2875, 2), (key2988, -1), (key2988, -1), (key2909, -1), (key2909, -1), (key2875, -1), (key2875, -1)]

def rawRow14048 : Integer.Sparse Key := [(key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2763, 2), (key2763, 2), (key2763, 2), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2909, 2), (key2909, 2), (key2909, 2), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1)]

def rawRow14049 : Integer.Sparse Key := [(key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2875, 2), (key2875, 2), (key2988, 2), (key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, -1), (key2909, -1), (key2875, -1), (key2988, -1), (key2909, -1), (key2988, -1), (key2767, 2), (key2767, 2), (key2930, 2), (key2844, -1), (key2888, -1), (key2844, -1), (key2967, -1), (key2888, -1), (key2967, -1)]

def rawRow14050 : Integer.Sparse Key := [(key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2875, 2), (key2988, 2), (key2875, 2), (key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2909, -1), (key2875, -1), (key2988, -1), (key2875, -1), (key2988, -1), (key2909, -1), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, -1), (key2844, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2888, -1)]

def rawRow14051 : Integer.Sparse Key := [(key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2988, 2), (key2875, 2), (key2875, 2), (key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2988, -1), (key2988, -1), (key2909, -1), (key2909, -1), (key2875, -1), (key2875, -1), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, -1), (key2967, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1)]

def rawRow14052 : Integer.Sparse Key := [(key2584, -1), (key2588, -1), (key2840, -1), (key2967, -1), (key2875, -1), (key2988, -1), (key2588, 2), (key2844, 2), (key2967, 2), (key2584, -1), (key2588, -1), (key2840, -1), (key2967, -1), (key2875, -1), (key2988, -1), (key2584, 2), (key2599, 2), (key2763, 2), (key2930, 2), (key2909, 2), (key2988, 2), (key2588, -1), (key2599, -1), (key2767, -1), (key2930, -1), (key2888, -1), (key2967, -1), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, -1), (key2599, -1), (key2767, -1), (key2930, -1), (key2888, -1), (key2967, -1)]

def rawRow14053 : Integer.Sparse Key := [(key2588, -1), (key2584, -1), (key2967, -1), (key2840, -1), (key2988, -1), (key2875, -1), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, -1), (key2584, -1), (key2967, -1), (key2840, -1), (key2988, -1), (key2875, -1), (key2599, 2), (key2584, 2), (key2930, 2), (key2763, 2), (key2988, 2), (key2909, 2), (key2599, -1), (key2588, -1), (key2930, -1), (key2767, -1), (key2967, -1), (key2888, -1), (key2588, 2), (key2967, 2), (key2844, 2), (key2599, -1), (key2588, -1), (key2930, -1), (key2767, -1), (key2967, -1), (key2888, -1)]

def rawRow14054 : Integer.Sparse Key := [(key2840, -1), (key2875, -1), (key2584, -1), (key2988, -1), (key2588, -1), (key2967, -1), (key2844, 2), (key2588, 2), (key2967, 2), (key2840, -1), (key2875, -1), (key2584, -1), (key2988, -1), (key2588, -1), (key2967, -1), (key2763, 2), (key2909, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2767, -1), (key2888, -1), (key2588, -1), (key2967, -1), (key2599, -1), (key2930, -1), (key2844, 2), (key2588, 2), (key2967, 2), (key2767, -1), (key2888, -1), (key2588, -1), (key2967, -1), (key2599, -1), (key2930, -1)]

def rawRow14055 : Integer.Sparse Key := [(key2875, -1), (key2840, -1), (key2988, -1), (key2584, -1), (key2967, -1), (key2588, -1), (key2844, 2), (key2967, 2), (key2588, 2), (key2875, -1), (key2840, -1), (key2988, -1), (key2584, -1), (key2967, -1), (key2588, -1), (key2909, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2930, 2), (key2599, 2), (key2888, -1), (key2767, -1), (key2967, -1), (key2588, -1), (key2930, -1), (key2599, -1), (key2844, 2), (key2967, 2), (key2588, 2), (key2888, -1), (key2767, -1), (key2967, -1), (key2588, -1), (key2930, -1), (key2599, -1)]

def rawRow14056 : Integer.Sparse Key := [(key2967, -1), (key2988, -1), (key2588, -1), (key2875, -1), (key2584, -1), (key2840, -1), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, -1), (key2988, -1), (key2588, -1), (key2875, -1), (key2584, -1), (key2840, -1), (key2930, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2584, 2), (key2763, 2), (key2930, -1), (key2967, -1), (key2599, -1), (key2888, -1), (key2588, -1), (key2767, -1), (key2967, 2), (key2588, 2), (key2844, 2), (key2930, -1), (key2967, -1), (key2599, -1), (key2888, -1), (key2588, -1), (key2767, -1)]

def rawRow14057 : Integer.Sparse Key := [(key2988, -1), (key2967, -1), (key2875, -1), (key2588, -1), (key2840, -1), (key2584, -1), (key2967, 2), (key2844, 2), (key2588, 2), (key2988, -1), (key2967, -1), (key2875, -1), (key2588, -1), (key2840, -1), (key2584, -1), (key2988, 2), (key2930, 2), (key2909, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2967, -1), (key2930, -1), (key2888, -1), (key2599, -1), (key2767, -1), (key2588, -1), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, -1), (key2930, -1), (key2888, -1), (key2599, -1), (key2767, -1), (key2588, -1)]

def rawRow14058 : Integer.Sparse Key := [(key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2584, 2), (key2840, 2), (key2840, 2), (key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2584, -1), (key2584, -1), (key2763, -1), (key2763, -1), (key2840, -1), (key2840, -1), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, -1), (key2588, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1)]

def rawRow14059 : Integer.Sparse Key := [(key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2840, 2), (key2584, 2), (key2840, 2), (key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2763, -1), (key2840, -1), (key2584, -1), (key2840, -1), (key2584, -1), (key2763, -1), (key2888, 2), (key2599, 2), (key2888, 2), (key2767, -1), (key2844, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2767, -1)]

def rawRow14060 : Integer.Sparse Key := [(key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2840, 2), (key2840, 2), (key2584, 2), (key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, -1), (key2763, -1), (key2840, -1), (key2584, -1), (key2763, -1), (key2584, -1), (key2888, 2), (key2888, 2), (key2599, 2), (key2844, -1), (key2767, -1), (key2844, -1), (key2588, -1), (key2767, -1), (key2588, -1)]

def rawRow14061 : Integer.Sparse Key := [(key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2909, 2), (key2909, 2), (key2909, 2), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2763, 2), (key2763, 2), (key2763, 2), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1)]

def rawRow14062 : Integer.Sparse Key := [(key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2588, -1), (key2588, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1), (key2584, 2), (key2840, 2), (key2840, 2), (key2584, -1), (key2584, -1), (key2763, -1), (key2763, -1), (key2840, -1), (key2840, -1)]

def rawRow14063 : Integer.Sparse Key := [(key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2888, 2), (key2599, 2), (key2888, 2), (key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2767, -1), (key2844, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2767, -1), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, -1), (key2840, -1), (key2584, -1), (key2840, -1), (key2584, -1), (key2763, -1)]

def rawRow14064 : Integer.Sparse Key := [(key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2888, 2), (key2888, 2), (key2599, 2), (key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2844, -1), (key2767, -1), (key2844, -1), (key2588, -1), (key2767, -1), (key2588, -1), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, -1), (key2763, -1), (key2840, -1), (key2584, -1), (key2763, -1), (key2584, -1)]

def rawRow14065 : Integer.Sparse Key := [(key2413, 4), (key2413, 4), (key2422, 4), (key2413, -4), (key2422, -4), (key2422, -4), (key2486, -4), (key2490, -4), (key2490, -4), (key2490, 12)]

def rawRow14066 : Integer.Sparse Key := [(key2413, 4), (key2422, 4), (key2413, 4), (key2422, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2486, -4), (key2490, -4), (key2490, 12)]

def rawRow14067 : Integer.Sparse Key := [(key2422, 4), (key2413, 4), (key2413, 4), (key2422, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2490, -4), (key2486, -4), (key2490, 12)]

def rawRow14068 : Integer.Sparse Key := [(key2422, 4), (key2422, 4), (key2422, 4), (key2413, -4), (key2413, -4), (key2413, -4), (key2490, -4), (key2490, -4), (key2490, -4), (key2486, 12)]

def rawRow14069 : Integer.Sparse Key := [(key2413, 4), (key2413, 4), (key2422, 4), (key2486, -4), (key2490, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2422, -4), (key2490, 12)]

def rawRow14070 : Integer.Sparse Key := [(key2413, 4), (key2422, 4), (key2413, 4), (key2490, -4), (key2486, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2422, -4), (key2490, 12)]

def rawRow14071 : Integer.Sparse Key := [(key2422, 4), (key2413, 4), (key2413, 4), (key2490, -4), (key2490, -4), (key2486, -4), (key2422, -4), (key2422, -4), (key2413, -4), (key2490, 12)]

def rawRow14072 : Integer.Sparse Key := [(key2413, 4), (key2486, 4), (key2490, 4), (key2413, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2422, 12)]

def rawRow14073 : Integer.Sparse Key := [(key2413, 4), (key2490, 4), (key2486, 4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, 12)]

def rawRow14074 : Integer.Sparse Key := [(key2486, 4), (key2413, 4), (key2490, 4), (key2413, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2422, 12)]

def rawRow14075 : Integer.Sparse Key := [(key2486, 4), (key2490, 4), (key2413, 4), (key2490, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2422, 12)]

def rawRow14076 : Integer.Sparse Key := [(key2490, 4), (key2413, 4), (key2486, 4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, 12)]

def rawRow14077 : Integer.Sparse Key := [(key2490, 4), (key2486, 4), (key2413, 4), (key2490, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2422, 12)]

def rawRow14078 : Integer.Sparse Key := [(key2422, 4), (key2490, 4), (key2490, 4), (key2413, -4), (key2413, -4), (key2486, -4), (key2422, -4), (key2422, -4), (key2490, -4), (key2413, 12)]

def rawRow14079 : Integer.Sparse Key := [(key2490, 4), (key2422, 4), (key2490, 4), (key2413, -4), (key2486, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2422, -4), (key2413, 12)]

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

def rawRow14080 : Integer.Sparse Key := [(key2490, 4), (key2490, 4), (key2422, 4), (key2486, -4), (key2413, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2422, -4), (key2413, 12)]

def rawRow14081 : Integer.Sparse Key := [(key2422, 4), (key2422, 4), (key2422, 4), (key2490, -4), (key2490, -4), (key2490, -4), (key2413, -4), (key2413, -4), (key2413, -4), (key2486, 12)]

def rawRow14082 : Integer.Sparse Key := [(key2422, 4), (key2490, 4), (key2490, 4), (key2422, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2413, -4), (key2486, -4), (key2413, 12)]

def rawRow14083 : Integer.Sparse Key := [(key2490, 4), (key2422, 4), (key2490, 4), (key2422, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2486, -4), (key2413, -4), (key2413, 12)]

def rawRow14084 : Integer.Sparse Key := [(key2490, 4), (key2490, 4), (key2422, 4), (key2490, -4), (key2422, -4), (key2422, -4), (key2486, -4), (key2413, -4), (key2413, -4), (key2413, 12)]

def rawRow14085 : Integer.Sparse Key := [(key2353, -2), (key2356, -2), (key2356, -2), (key2356, 6), (key2448, -2), (key2451, -2), (key2451, -2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2451, -2), (key2451, -2), (key2513, -2), (key2527, 6), (key2527, -2), (key2527, -2), (key2558, -2)]

def rawRow14086 : Integer.Sparse Key := [(key2356, -2), (key2353, -2), (key2356, -2), (key2356, 6), (key2451, -2), (key2448, -2), (key2451, -2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2451, -2), (key2513, -2), (key2451, -2), (key2527, 6), (key2527, -2), (key2558, -2), (key2527, -2)]

def rawRow14087 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2353, -2), (key2356, 6), (key2451, -2), (key2451, -2), (key2448, -2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2513, -2), (key2451, -2), (key2451, -2), (key2527, 6), (key2558, -2), (key2527, -2), (key2527, -2)]

def rawRow14088 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2356, -2), (key2353, 6), (key2513, -2), (key2513, -2), (key2513, -2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2558, 6), (key2527, -2), (key2527, -2), (key2527, -2)]

def rawRow14089 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2451, -2), (key2513, 6), (key2353, -2), (key2356, -2), (key2356, -2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, 6), (key2451, -2), (key2451, -2), (key2513, -2)]

def rawRow14090 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2451, -2), (key2513, 6), (key2356, -2), (key2353, -2), (key2356, -2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2527, -2), (key2558, -2), (key2527, -2), (key2356, 6), (key2451, -2), (key2513, -2), (key2451, -2)]

def rawRow14091 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2448, -2), (key2513, 6), (key2356, -2), (key2356, -2), (key2353, -2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2558, -2), (key2527, -2), (key2527, -2), (key2356, 6), (key2513, -2), (key2451, -2), (key2451, -2)]

def rawRow14092 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2513, -2), (key2451, 6), (key2448, -2), (key2451, -2), (key2513, -2), (key2353, 2), (key2356, 2), (key2448, 2), (key2513, 2), (key2527, 2), (key2558, 2), (key2356, -2), (key2451, -2), (key2513, -2), (key2451, 6), (key2356, -2), (key2451, -2), (key2513, -2)]

def rawRow14093 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2513, -2), (key2451, 6), (key2451, -2), (key2448, -2), (key2513, -2), (key2356, 2), (key2353, 2), (key2513, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2356, -2), (key2513, -2), (key2451, -2), (key2451, 6), (key2356, -2), (key2513, -2), (key2451, -2)]

def rawRow14094 : Integer.Sparse Key := [(key2448, -2), (key2513, -2), (key2451, -2), (key2451, 6), (key2448, -2), (key2513, -2), (key2451, -2), (key2448, 2), (key2513, 2), (key2353, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2451, -2), (key2356, -2), (key2513, -2), (key2451, 6), (key2451, -2), (key2356, -2), (key2513, -2)]

def rawRow14095 : Integer.Sparse Key := [(key2513, -2), (key2448, -2), (key2451, -2), (key2451, 6), (key2513, -2), (key2448, -2), (key2451, -2), (key2513, 2), (key2448, 2), (key2558, 2), (key2353, 2), (key2513, 2), (key2356, 2), (key2451, -2), (key2513, -2), (key2356, -2), (key2451, 6), (key2451, -2), (key2513, -2), (key2356, -2)]

def rawRow14096 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2448, -2), (key2451, 6), (key2451, -2), (key2513, -2), (key2448, -2), (key2527, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2353, 2), (key2448, 2), (key2513, -2), (key2356, -2), (key2451, -2), (key2451, 6), (key2513, -2), (key2356, -2), (key2451, -2)]

def rawRow14097 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2448, -2), (key2451, 6), (key2513, -2), (key2451, -2), (key2448, -2), (key2558, 2), (key2527, 2), (key2513, 2), (key2356, 2), (key2448, 2), (key2353, 2), (key2513, -2), (key2451, -2), (key2356, -2), (key2451, 6), (key2513, -2), (key2451, -2), (key2356, -2)]

def rawRow14098 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2513, -2), (key2448, 6), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, 2), (key2356, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2513, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2513, 6), (key2356, -2), (key2451, -2), (key2451, -2)]

def rawRow14099 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2451, -2), (key2448, 6), (key2527, -2), (key2558, -2), (key2527, -2), (key2451, 2), (key2513, 2), (key2356, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2513, 6), (key2451, -2), (key2356, -2), (key2451, -2)]

def rawRow14100 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2558, -2), (key2527, -2), (key2527, -2), (key2513, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2356, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2513, 6), (key2451, -2), (key2451, -2), (key2356, -2)]

def rawRow14101 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2527, -2), (key2558, 6), (key2356, -2), (key2356, -2), (key2356, -2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2513, -2), (key2513, -2), (key2513, -2), (key2353, 6), (key2448, -2), (key2448, -2), (key2448, -2)]

def rawRow14102 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2558, -2), (key2527, 6), (key2451, -2), (key2451, -2), (key2513, -2), (key2356, 2), (key2356, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2513, 2), (key2356, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2353, -2), (key2448, -2), (key2448, -2)]

def rawRow14103 : Integer.Sparse Key := [(key2527, -2), (key2558, -2), (key2527, -2), (key2527, 6), (key2451, -2), (key2513, -2), (key2451, -2), (key2451, 2), (key2513, 2), (key2356, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2451, -2), (key2356, -2), (key2451, -2), (key2448, 6), (key2448, -2), (key2353, -2), (key2448, -2)]

def rawRow14104 : Integer.Sparse Key := [(key2558, -2), (key2527, -2), (key2527, -2), (key2527, 6), (key2513, -2), (key2451, -2), (key2451, -2), (key2513, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2356, 2), (key2451, -2), (key2451, -2), (key2356, -2), (key2448, 6), (key2448, -2), (key2448, -2), (key2353, -2)]

def rawRow14105 : Integer.Sparse Key := [(key1975, 4), (key2217, 4), (key2217, 4), (key1980, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key2261, -2), (key2261, -2), (key1980, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key2261, -2), (key2261, -2), (key1996, 4), (key2261, 4), (key2261, 4)]

def rawRow14106 : Integer.Sparse Key := [(key2217, 4), (key1975, 4), (key2217, 4), (key2217, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key2261, 4), (key1996, 4), (key2261, 4)]

def rawRow14107 : Integer.Sparse Key := [(key2217, 4), (key2217, 4), (key1975, 4), (key2261, -2), (key2217, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key1980, -2), (key2261, -2), (key2217, -2), (key2261, -2), (key1980, -2), (key2217, -2), (key1980, -2), (key2261, 4), (key2261, 4), (key1996, 4)]

def rawRow14108 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key2261, 4), (key1975, -2), (key1980, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key2217, -2), (key1980, -2), (key1996, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key2261, -2), (key1980, 4), (key1980, 4), (key2217, 4)]

def rawRow14109 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key1980, 4), (key1980, -2), (key1975, -2), (key2217, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key1996, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key1980, 4), (key2217, 4), (key1980, 4)]

def rawRow14110 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key1980, 4), (key2217, -2), (key2217, -2), (key1980, -2), (key1980, -2), (key1975, -2), (key1975, -2), (key2261, -2), (key2261, -2), (key1996, -2), (key1996, -2), (key1980, -2), (key1980, -2), (key2217, 4), (key1980, 4), (key1980, 4)]

def rawRow14111 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key2261, 4), (key1980, -2), (key1996, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key2261, -2), (key1975, -2), (key1980, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key2217, -2), (key1980, 4), (key1980, 4), (key2217, 4)]

def rawRow14112 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key1980, 4), (key1996, -2), (key1980, -2), (key2261, -2), (key1980, -2), (key2261, -2), (key1996, -2), (key1980, -2), (key1975, -2), (key2217, -2), (key1975, -2), (key2217, -2), (key1980, -2), (key1980, 4), (key2217, 4), (key1980, 4)]

def rawRow14113 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key1980, 4), (key2261, -2), (key2261, -2), (key1996, -2), (key1996, -2), (key1980, -2), (key1980, -2), (key2217, -2), (key2217, -2), (key1980, -2), (key1980, -2), (key1975, -2), (key1975, -2), (key2217, 4), (key1980, 4), (key1980, 4)]

def rawRow14114 : Integer.Sparse Key := [(key1996, 4), (key1996, 4), (key1996, 4), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1980, -2), (key1975, 4), (key1975, 4), (key1975, 4)]

def rawRow14115 : Integer.Sparse Key := [(key55, -2), (key55, -2), (key61, -2), (key61, 6), (key55, -2), (key55, -2), (key61, -2), (key55, 2), (key55, 2), (key123, 2), (key123, 2), (key126, 2), (key126, 2), (key61, -2), (key126, -2), (key126, -2), (key61, 6), (key61, -2), (key126, -2), (key126, -2)]

def rawRow14116 : Integer.Sparse Key := [(key55, -2), (key61, -2), (key55, -2), (key61, 6), (key55, -2), (key61, -2), (key55, -2), (key123, 2), (key126, 2), (key55, 2), (key126, 2), (key55, 2), (key123, 2), (key126, -2), (key61, -2), (key126, -2), (key61, 6), (key126, -2), (key61, -2), (key126, -2)]

def rawRow14117 : Integer.Sparse Key := [(key61, -2), (key55, -2), (key55, -2), (key61, 6), (key61, -2), (key55, -2), (key55, -2), (key126, 2), (key123, 2), (key126, 2), (key55, 2), (key123, 2), (key55, 2), (key126, -2), (key126, -2), (key61, -2), (key61, 6), (key126, -2), (key126, -2), (key61, -2)]

def rawRow14118 : Integer.Sparse Key := [(key55, -2), (key61, -2), (key61, -2), (key55, 6), (key123, -2), (key126, -2), (key126, -2), (key55, 2), (key61, 2), (key55, 2), (key126, 2), (key61, 2), (key126, 2), (key55, -2), (key55, -2), (key123, -2), (key126, 6), (key61, -2), (key61, -2), (key126, -2)]

def rawRow14119 : Integer.Sparse Key := [(key61, -2), (key55, -2), (key61, -2), (key55, 6), (key126, -2), (key123, -2), (key126, -2), (key61, 2), (key55, 2), (key126, 2), (key55, 2), (key126, 2), (key61, 2), (key55, -2), (key123, -2), (key55, -2), (key126, 6), (key61, -2), (key126, -2), (key61, -2)]

def rawRow14120 : Integer.Sparse Key := [(key61, -2), (key61, -2), (key55, -2), (key55, 6), (key126, -2), (key126, -2), (key123, -2), (key126, 2), (key126, 2), (key61, 2), (key61, 2), (key55, 2), (key55, 2), (key123, -2), (key55, -2), (key55, -2), (key126, 6), (key126, -2), (key61, -2), (key61, -2)]

def rawRow14121 : Integer.Sparse Key := [(key123, -2), (key126, -2), (key126, -2), (key126, 6), (key55, -2), (key61, -2), (key61, -2), (key55, 2), (key61, 2), (key55, 2), (key126, 2), (key61, 2), (key126, 2), (key61, -2), (key61, -2), (key126, -2), (key55, 6), (key55, -2), (key55, -2), (key123, -2)]

def rawRow14122 : Integer.Sparse Key := [(key126, -2), (key123, -2), (key126, -2), (key126, 6), (key61, -2), (key55, -2), (key61, -2), (key61, 2), (key55, 2), (key126, 2), (key55, 2), (key126, 2), (key61, 2), (key61, -2), (key126, -2), (key61, -2), (key55, 6), (key55, -2), (key123, -2), (key55, -2)]

def rawRow14123 : Integer.Sparse Key := [(key126, -2), (key126, -2), (key123, -2), (key126, 6), (key61, -2), (key61, -2), (key55, -2), (key126, 2), (key126, 2), (key61, 2), (key61, 2), (key55, 2), (key55, 2), (key126, -2), (key61, -2), (key61, -2), (key55, 6), (key123, -2), (key55, -2), (key55, -2)]

def rawRow14124 : Integer.Sparse Key := [(key126, -2), (key126, -2), (key126, -2), (key123, 6), (key126, -2), (key126, -2), (key126, -2), (key61, 2), (key61, 2), (key61, 2), (key61, 2), (key61, 2), (key61, 2), (key55, -2), (key55, -2), (key55, -2), (key123, 6), (key55, -2), (key55, -2), (key55, -2)]

def rawRow14125 : Integer.Sparse Key := [(key1972, -2), (key1972, -2), (key1984, -2), (key1984, 6), (key1972, -2), (key1972, -2), (key1984, -2), (key1972, 2), (key1972, 2), (key2208, 2), (key2208, 2), (key2225, 2), (key2225, 2), (key1984, -2), (key2225, -2), (key2225, -2), (key1984, 6), (key1984, -2), (key2225, -2), (key2225, -2)]

def rawRow14126 : Integer.Sparse Key := [(key1972, -2), (key1984, -2), (key1972, -2), (key1984, 6), (key1972, -2), (key1984, -2), (key1972, -2), (key2208, 2), (key2225, 2), (key1972, 2), (key2225, 2), (key1972, 2), (key2208, 2), (key2225, -2), (key1984, -2), (key2225, -2), (key1984, 6), (key2225, -2), (key1984, -2), (key2225, -2)]

def rawRow14127 : Integer.Sparse Key := [(key1984, -2), (key1972, -2), (key1972, -2), (key1984, 6), (key1984, -2), (key1972, -2), (key1972, -2), (key2225, 2), (key2208, 2), (key2225, 2), (key1972, 2), (key2208, 2), (key1972, 2), (key2225, -2), (key2225, -2), (key1984, -2), (key1984, 6), (key2225, -2), (key2225, -2), (key1984, -2)]

def rawRow14128 : Integer.Sparse Key := [(key1972, -2), (key1984, -2), (key1984, -2), (key1972, 6), (key2208, -2), (key2225, -2), (key2225, -2), (key1972, 2), (key1984, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key2225, 2), (key1972, -2), (key1972, -2), (key2208, -2), (key2225, 6), (key1984, -2), (key1984, -2), (key2225, -2)]

def rawRow14129 : Integer.Sparse Key := [(key1984, -2), (key1972, -2), (key1984, -2), (key1972, 6), (key2225, -2), (key2208, -2), (key2225, -2), (key1984, 2), (key1972, 2), (key2225, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key1972, -2), (key2208, -2), (key1972, -2), (key2225, 6), (key1984, -2), (key2225, -2), (key1984, -2)]

def rawRow14130 : Integer.Sparse Key := [(key1984, -2), (key1984, -2), (key1972, -2), (key1972, 6), (key2225, -2), (key2225, -2), (key2208, -2), (key2225, 2), (key2225, 2), (key1984, 2), (key1984, 2), (key1972, 2), (key1972, 2), (key2208, -2), (key1972, -2), (key1972, -2), (key2225, 6), (key2225, -2), (key1984, -2), (key1984, -2)]

def rawRow14131 : Integer.Sparse Key := [(key2208, -2), (key2225, -2), (key2225, -2), (key2225, 6), (key1972, -2), (key1984, -2), (key1984, -2), (key1972, 2), (key1984, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key2225, 2), (key1984, -2), (key1984, -2), (key2225, -2), (key1972, 6), (key1972, -2), (key1972, -2), (key2208, -2)]

def rawRow14132 : Integer.Sparse Key := [(key2225, -2), (key2208, -2), (key2225, -2), (key2225, 6), (key1984, -2), (key1972, -2), (key1984, -2), (key1984, 2), (key1972, 2), (key2225, 2), (key1972, 2), (key2225, 2), (key1984, 2), (key1984, -2), (key2225, -2), (key1984, -2), (key1972, 6), (key1972, -2), (key2208, -2), (key1972, -2)]

def rawRow14133 : Integer.Sparse Key := [(key2225, -2), (key2225, -2), (key2208, -2), (key2225, 6), (key1984, -2), (key1984, -2), (key1972, -2), (key2225, 2), (key2225, 2), (key1984, 2), (key1984, 2), (key1972, 2), (key1972, 2), (key2225, -2), (key1984, -2), (key1984, -2), (key1972, 6), (key2208, -2), (key1972, -2), (key1972, -2)]

def rawRow14134 : Integer.Sparse Key := [(key2225, -2), (key2225, -2), (key2225, -2), (key2208, 6), (key2225, -2), (key2225, -2), (key2225, -2), (key1984, 2), (key1984, 2), (key1984, 2), (key1984, 2), (key1984, 2), (key1984, 2), (key1972, -2), (key1972, -2), (key1972, -2), (key2208, 6), (key1972, -2), (key1972, -2), (key1972, -2)]

def rawRow14135 : Integer.Sparse Key := [(key2010, 6), (key2010, -2), (key2039, -2), (key2039, -2), (key2010, 6), (key2010, -2), (key2124, -2), (key2124, -2), (key2010, -2), (key2039, -2), (key2039, -2), (key2010, -2), (key2124, -2), (key2124, -2), (key2039, 2), (key2039, 2), (key2124, 2), (key2124, 2), (key2211, 2), (key2211, 2)]

def rawRow14136 : Integer.Sparse Key := [(key2010, 6), (key2039, -2), (key2010, -2), (key2039, -2), (key2010, 6), (key2124, -2), (key2010, -2), (key2124, -2), (key2039, -2), (key2010, -2), (key2039, -2), (key2124, -2), (key2010, -2), (key2124, -2), (key2124, 2), (key2211, 2), (key2039, 2), (key2211, 2), (key2039, 2), (key2124, 2)]

def rawRow14137 : Integer.Sparse Key := [(key2010, 6), (key2039, -2), (key2039, -2), (key2010, -2), (key2010, 6), (key2124, -2), (key2124, -2), (key2010, -2), (key2039, -2), (key2039, -2), (key2010, -2), (key2124, -2), (key2124, -2), (key2010, -2), (key2211, 2), (key2124, 2), (key2211, 2), (key2039, 2), (key2124, 2), (key2039, 2)]

def rawRow14138 : Integer.Sparse Key := [(key2039, 6), (key2010, -2), (key2010, -2), (key2039, -2), (key2124, 6), (key2010, -2), (key2010, -2), (key2124, -2), (key2124, -2), (key2124, -2), (key2211, -2), (key2039, -2), (key2039, -2), (key2211, -2), (key2010, 2), (key2039, 2), (key2010, 2), (key2124, 2), (key2039, 2), (key2124, 2)]

def rawRow14139 : Integer.Sparse Key := [(key2039, 6), (key2010, -2), (key2039, -2), (key2010, -2), (key2124, 6), (key2010, -2), (key2124, -2), (key2010, -2), (key2124, -2), (key2211, -2), (key2124, -2), (key2039, -2), (key2211, -2), (key2039, -2), (key2039, 2), (key2010, 2), (key2124, 2), (key2010, 2), (key2124, 2), (key2039, 2)]

def rawRow14140 : Integer.Sparse Key := [(key2039, 6), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, 6), (key2124, -2), (key2010, -2), (key2010, -2), (key2211, -2), (key2124, -2), (key2124, -2), (key2211, -2), (key2039, -2), (key2039, -2), (key2124, 2), (key2124, 2), (key2039, 2), (key2039, 2), (key2010, 2), (key2010, 2)]

def rawRow14141 : Integer.Sparse Key := [(key2124, 6), (key2124, -2), (key2124, -2), (key2211, -2), (key2039, 6), (key2039, -2), (key2039, -2), (key2211, -2), (key2010, -2), (key2010, -2), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, -2), (key2010, 2), (key2039, 2), (key2010, 2), (key2124, 2), (key2039, 2), (key2124, 2)]

def rawRow14142 : Integer.Sparse Key := [(key2124, 6), (key2124, -2), (key2211, -2), (key2124, -2), (key2039, 6), (key2039, -2), (key2211, -2), (key2039, -2), (key2010, -2), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, -2), (key2010, -2), (key2039, 2), (key2010, 2), (key2124, 2), (key2010, 2), (key2124, 2), (key2039, 2)]

def rawRow14143 : Integer.Sparse Key := [(key2124, 6), (key2211, -2), (key2124, -2), (key2124, -2), (key2039, 6), (key2211, -2), (key2039, -2), (key2039, -2), (key2039, -2), (key2010, -2), (key2010, -2), (key2124, -2), (key2010, -2), (key2010, -2), (key2124, 2), (key2124, 2), (key2039, 2), (key2039, 2), (key2010, 2), (key2010, 2)]

def rawRow14144 : Integer.Sparse Key := [(key2211, 6), (key2124, -2), (key2124, -2), (key2124, -2), (key2211, 6), (key2039, -2), (key2039, -2), (key2039, -2), (key2124, -2), (key2124, -2), (key2124, -2), (key2039, -2), (key2039, -2), (key2039, -2), (key2010, 2), (key2010, 2), (key2010, 2), (key2010, 2), (key2010, 2), (key2010, 2)]

def rawRow14145 : Integer.Sparse Key := [(key53, -2), (key53, -2), (key59, -2), (key59, 6), (key53, -2), (key53, -2), (key59, -2), (key53, 2), (key53, 2), (key121, 2), (key121, 2), (key124, 2), (key124, 2), (key59, -2), (key124, -2), (key124, -2), (key59, 6), (key59, -2), (key124, -2), (key124, -2)]

def rawRow14146 : Integer.Sparse Key := [(key53, -2), (key59, -2), (key53, -2), (key59, 6), (key53, -2), (key59, -2), (key53, -2), (key121, 2), (key124, 2), (key53, 2), (key124, 2), (key53, 2), (key121, 2), (key124, -2), (key59, -2), (key124, -2), (key59, 6), (key124, -2), (key59, -2), (key124, -2)]

def rawRow14147 : Integer.Sparse Key := [(key59, -2), (key53, -2), (key53, -2), (key59, 6), (key59, -2), (key53, -2), (key53, -2), (key124, 2), (key121, 2), (key124, 2), (key53, 2), (key121, 2), (key53, 2), (key124, -2), (key124, -2), (key59, -2), (key59, 6), (key124, -2), (key124, -2), (key59, -2)]

def rawRow14148 : Integer.Sparse Key := [(key53, -2), (key59, -2), (key59, -2), (key53, 6), (key121, -2), (key124, -2), (key124, -2), (key53, 2), (key59, 2), (key53, 2), (key124, 2), (key59, 2), (key124, 2), (key53, -2), (key53, -2), (key121, -2), (key124, 6), (key59, -2), (key59, -2), (key124, -2)]

def rawRow14149 : Integer.Sparse Key := [(key59, -2), (key53, -2), (key59, -2), (key53, 6), (key124, -2), (key121, -2), (key124, -2), (key59, 2), (key53, 2), (key124, 2), (key53, 2), (key124, 2), (key59, 2), (key53, -2), (key121, -2), (key53, -2), (key124, 6), (key59, -2), (key124, -2), (key59, -2)]

def rawRow14150 : Integer.Sparse Key := [(key59, -2), (key59, -2), (key53, -2), (key53, 6), (key124, -2), (key124, -2), (key121, -2), (key124, 2), (key124, 2), (key59, 2), (key59, 2), (key53, 2), (key53, 2), (key121, -2), (key53, -2), (key53, -2), (key124, 6), (key124, -2), (key59, -2), (key59, -2)]

def rawRow14151 : Integer.Sparse Key := [(key121, -2), (key124, -2), (key124, -2), (key124, 6), (key53, -2), (key59, -2), (key59, -2), (key53, 2), (key59, 2), (key53, 2), (key124, 2), (key59, 2), (key124, 2), (key59, -2), (key59, -2), (key124, -2), (key53, 6), (key53, -2), (key53, -2), (key121, -2)]

def rawRow14152 : Integer.Sparse Key := [(key124, -2), (key121, -2), (key124, -2), (key124, 6), (key59, -2), (key53, -2), (key59, -2), (key59, 2), (key53, 2), (key124, 2), (key53, 2), (key124, 2), (key59, 2), (key59, -2), (key124, -2), (key59, -2), (key53, 6), (key53, -2), (key121, -2), (key53, -2)]

def rawRow14153 : Integer.Sparse Key := [(key124, -2), (key124, -2), (key121, -2), (key124, 6), (key59, -2), (key59, -2), (key53, -2), (key124, 2), (key124, 2), (key59, 2), (key59, 2), (key53, 2), (key53, 2), (key124, -2), (key59, -2), (key59, -2), (key53, 6), (key121, -2), (key53, -2), (key53, -2)]

def rawRow14154 : Integer.Sparse Key := [(key124, -2), (key124, -2), (key124, -2), (key121, 6), (key124, -2), (key124, -2), (key124, -2), (key59, 2), (key59, 2), (key59, 2), (key59, 2), (key59, 2), (key59, 2), (key53, -2), (key53, -2), (key53, -2), (key121, 6), (key53, -2), (key53, -2), (key53, -2)]

def rawRow14155 : Integer.Sparse Key := [(key57, 4), (key129, 4), (key129, 4), (key64, -2), (key64, -2), (key129, -2), (key129, -2), (key140, -2), (key140, -2), (key64, -2), (key64, -2), (key129, -2), (key129, -2), (key140, -2), (key140, -2), (key77, 4), (key140, 4), (key140, 4)]

def rawRow14156 : Integer.Sparse Key := [(key129, 4), (key57, 4), (key129, 4), (key129, -2), (key140, -2), (key64, -2), (key140, -2), (key64, -2), (key129, -2), (key129, -2), (key140, -2), (key64, -2), (key140, -2), (key64, -2), (key129, -2), (key140, 4), (key77, 4), (key140, 4)]

def rawRow14157 : Integer.Sparse Key := [(key129, 4), (key129, 4), (key57, 4), (key140, -2), (key129, -2), (key140, -2), (key64, -2), (key129, -2), (key64, -2), (key140, -2), (key129, -2), (key140, -2), (key64, -2), (key129, -2), (key64, -2), (key140, 4), (key140, 4), (key77, 4)]

def rawRow14158 : Integer.Sparse Key := [(key64, 4), (key64, 4), (key140, 4), (key57, -2), (key64, -2), (key57, -2), (key129, -2), (key64, -2), (key129, -2), (key64, -2), (key77, -2), (key64, -2), (key140, -2), (key77, -2), (key140, -2), (key64, 4), (key64, 4), (key129, 4)]

def rawRow14159 : Integer.Sparse Key := [(key64, 4), (key140, 4), (key64, 4), (key64, -2), (key57, -2), (key129, -2), (key57, -2), (key129, -2), (key64, -2), (key77, -2), (key64, -2), (key140, -2), (key64, -2), (key140, -2), (key77, -2), (key64, 4), (key129, 4), (key64, 4)]

def rawRow14160 : Integer.Sparse Key := [(key140, 4), (key64, 4), (key64, 4), (key129, -2), (key129, -2), (key64, -2), (key64, -2), (key57, -2), (key57, -2), (key140, -2), (key140, -2), (key77, -2), (key77, -2), (key64, -2), (key64, -2), (key129, 4), (key64, 4), (key64, 4)]

def rawRow14161 : Integer.Sparse Key := [(key64, 4), (key64, 4), (key140, 4), (key64, -2), (key77, -2), (key64, -2), (key140, -2), (key77, -2), (key140, -2), (key57, -2), (key64, -2), (key57, -2), (key129, -2), (key64, -2), (key129, -2), (key64, 4), (key64, 4), (key129, 4)]

def rawRow14162 : Integer.Sparse Key := [(key64, 4), (key140, 4), (key64, 4), (key77, -2), (key64, -2), (key140, -2), (key64, -2), (key140, -2), (key77, -2), (key64, -2), (key57, -2), (key129, -2), (key57, -2), (key129, -2), (key64, -2), (key64, 4), (key129, 4), (key64, 4)]

def rawRow14163 : Integer.Sparse Key := [(key140, 4), (key64, 4), (key64, 4), (key140, -2), (key140, -2), (key77, -2), (key77, -2), (key64, -2), (key64, -2), (key129, -2), (key129, -2), (key64, -2), (key64, -2), (key57, -2), (key57, -2), (key129, 4), (key64, 4), (key64, 4)]

def rawRow14164 : Integer.Sparse Key := [(key77, 4), (key77, 4), (key77, 4), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key64, -2), (key57, 4), (key57, 4), (key57, 4)]

def rawRow14165 : Integer.Sparse Key := [(key2012, -1), (key2012, -1), (key2126, -1), (key2126, -1), (key2143, -1), (key2143, -1), (key2025, 2), (key2143, 2), (key2143, 2), (key2012, -1), (key2012, -1), (key2126, -1), (key2126, -1), (key2143, -1), (key2143, -1), (key2041, 2), (key2041, 2), (key2126, 2), (key2126, 2), (key2227, 2), (key2227, 2), (key2054, -1), (key2054, -1), (key2143, -1), (key2143, -1), (key2227, -1), (key2227, -1), (key2025, 2), (key2143, 2), (key2143, 2), (key2054, -1), (key2054, -1), (key2143, -1), (key2143, -1), (key2227, -1), (key2227, -1)]

def rawRow14166 : Integer.Sparse Key := [(key2126, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2143, 2), (key2025, 2), (key2143, 2), (key2126, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2126, 2), (key2227, 2), (key2041, 2), (key2227, 2), (key2041, 2), (key2126, 2), (key2143, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2054, -1), (key2143, -1), (key2143, 2), (key2025, 2), (key2143, 2), (key2143, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2054, -1), (key2143, -1)]

def rawRow14167 : Integer.Sparse Key := [(key2143, -1), (key2126, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2143, 2), (key2143, 2), (key2025, 2), (key2143, -1), (key2126, -1), (key2143, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2227, 2), (key2126, 2), (key2227, 2), (key2041, 2), (key2126, 2), (key2041, 2), (key2227, -1), (key2143, -1), (key2227, -1), (key2054, -1), (key2143, -1), (key2054, -1), (key2143, 2), (key2143, 2), (key2025, 2), (key2227, -1), (key2143, -1), (key2227, -1), (key2054, -1), (key2143, -1), (key2054, -1)]

def rawRow14168 : Integer.Sparse Key := [(key2012, -1), (key2025, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2012, 2), (key2012, 2), (key2126, 2), (key2041, -1), (key2054, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2012, 2), (key2054, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2143, 2), (key2012, -1), (key2041, -1), (key2012, -1), (key2126, -1), (key2041, -1), (key2126, -1), (key2054, 2), (key2054, 2), (key2227, 2), (key2025, -1), (key2054, -1), (key2025, -1), (key2143, -1), (key2054, -1), (key2143, -1)]

def rawRow14169 : Integer.Sparse Key := [(key2025, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2012, 2), (key2126, 2), (key2012, 2), (key2054, -1), (key2041, -1), (key2227, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2054, 2), (key2012, 2), (key2143, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2041, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2126, -1), (key2041, -1), (key2054, 2), (key2227, 2), (key2054, 2), (key2054, -1), (key2025, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2054, -1)]

def rawRow14170 : Integer.Sparse Key := [(key2143, -1), (key2143, -1), (key2025, -1), (key2025, -1), (key2012, -1), (key2012, -1), (key2126, 2), (key2012, 2), (key2012, 2), (key2227, -1), (key2227, -1), (key2054, -1), (key2054, -1), (key2041, -1), (key2041, -1), (key2143, 2), (key2143, 2), (key2054, 2), (key2054, 2), (key2012, 2), (key2012, 2), (key2126, -1), (key2126, -1), (key2041, -1), (key2041, -1), (key2012, -1), (key2012, -1), (key2227, 2), (key2054, 2), (key2054, 2), (key2143, -1), (key2143, -1), (key2054, -1), (key2054, -1), (key2025, -1), (key2025, -1)]

def rawRow14171 : Integer.Sparse Key := [(key2041, -1), (key2054, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2227, -1), (key2054, 2), (key2054, 2), (key2227, 2), (key2012, -1), (key2025, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2012, 2), (key2054, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2143, 2), (key2025, -1), (key2054, -1), (key2025, -1), (key2143, -1), (key2054, -1), (key2143, -1), (key2012, 2), (key2012, 2), (key2126, 2), (key2012, -1), (key2041, -1), (key2012, -1), (key2126, -1), (key2041, -1), (key2126, -1)]

def rawRow14172 : Integer.Sparse Key := [(key2054, -1), (key2041, -1), (key2227, -1), (key2041, -1), (key2227, -1), (key2054, -1), (key2054, 2), (key2227, 2), (key2054, 2), (key2025, -1), (key2012, -1), (key2143, -1), (key2012, -1), (key2143, -1), (key2025, -1), (key2054, 2), (key2012, 2), (key2143, 2), (key2012, 2), (key2143, 2), (key2054, 2), (key2054, -1), (key2025, -1), (key2143, -1), (key2025, -1), (key2143, -1), (key2054, -1), (key2012, 2), (key2126, 2), (key2012, 2), (key2041, -1), (key2012, -1), (key2126, -1), (key2012, -1), (key2126, -1), (key2041, -1)]

def rawRow14173 : Integer.Sparse Key := [(key2227, -1), (key2227, -1), (key2054, -1), (key2054, -1), (key2041, -1), (key2041, -1), (key2227, 2), (key2054, 2), (key2054, 2), (key2143, -1), (key2143, -1), (key2025, -1), (key2025, -1), (key2012, -1), (key2012, -1), (key2143, 2), (key2143, 2), (key2054, 2), (key2054, 2), (key2012, 2), (key2012, 2), (key2143, -1), (key2143, -1), (key2054, -1), (key2054, -1), (key2025, -1), (key2025, -1), (key2126, 2), (key2012, 2), (key2012, 2), (key2126, -1), (key2126, -1), (key2041, -1), (key2041, -1), (key2012, -1), (key2012, -1)]

def rawRow14174 : Integer.Sparse Key := [(key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2041, 2), (key2041, 2), (key2041, 2), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2054, -1), (key2025, 2), (key2025, 2), (key2025, 2), (key2025, 2), (key2025, 2), (key2025, 2), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2041, 2), (key2041, 2), (key2041, 2), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1), (key2012, -1)]

def rawRow14175 : Integer.Sparse Key := [(key2100, 4), (key2105, 4), (key2105, 4), (key2105, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2130, 12)]

def rawRow14176 : Integer.Sparse Key := [(key2105, 4), (key2100, 4), (key2105, 4), (key2105, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2130, 12)]

def rawRow14177 : Integer.Sparse Key := [(key2105, 4), (key2105, 4), (key2100, 4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2130, 12)]

def rawRow14178 : Integer.Sparse Key := [(key2105, 4), (key2105, 4), (key2130, 4), (key2100, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2130, -4), (key2130, -4), (key2105, 12)]

def rawRow14179 : Integer.Sparse Key := [(key2105, 4), (key2130, 4), (key2105, 4), (key2105, -4), (key2100, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2130, -4), (key2105, 12)]

def rawRow14180 : Integer.Sparse Key := [(key2130, 4), (key2105, 4), (key2105, 4), (key2105, -4), (key2105, -4), (key2100, -4), (key2130, -4), (key2130, -4), (key2105, -4), (key2105, 12)]

def rawRow14181 : Integer.Sparse Key := [(key2105, 4), (key2105, 4), (key2130, 4), (key2105, -4), (key2130, -4), (key2130, -4), (key2100, -4), (key2105, -4), (key2105, -4), (key2105, 12)]

def rawRow14182 : Integer.Sparse Key := [(key2105, 4), (key2130, 4), (key2105, 4), (key2130, -4), (key2105, -4), (key2130, -4), (key2105, -4), (key2100, -4), (key2105, -4), (key2105, 12)]

def rawRow14183 : Integer.Sparse Key := [(key2130, 4), (key2105, 4), (key2105, 4), (key2130, -4), (key2130, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2100, -4), (key2105, 12)]

def rawRow14184 : Integer.Sparse Key := [(key2130, 4), (key2130, 4), (key2130, 4), (key2105, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2105, -4), (key2100, 12)]

def rawRow14185 : Integer.Sparse Key := [(key1971, -2), (key1971, -2), (key1979, -2), (key1979, 6), (key1971, -2), (key1971, -2), (key1979, -2), (key1971, 2), (key1971, 2), (key2207, 2), (key2207, 2), (key2216, 2), (key2216, 2), (key1979, -2), (key2216, -2), (key2216, -2), (key1979, 6), (key1979, -2), (key2216, -2), (key2216, -2)]

def rawRow14186 : Integer.Sparse Key := [(key1971, -2), (key1979, -2), (key1971, -2), (key1979, 6), (key1971, -2), (key1979, -2), (key1971, -2), (key2207, 2), (key2216, 2), (key1971, 2), (key2216, 2), (key1971, 2), (key2207, 2), (key2216, -2), (key1979, -2), (key2216, -2), (key1979, 6), (key2216, -2), (key1979, -2), (key2216, -2)]

def rawRow14187 : Integer.Sparse Key := [(key1979, -2), (key1971, -2), (key1971, -2), (key1979, 6), (key1979, -2), (key1971, -2), (key1971, -2), (key2216, 2), (key2207, 2), (key2216, 2), (key1971, 2), (key2207, 2), (key1971, 2), (key2216, -2), (key2216, -2), (key1979, -2), (key1979, 6), (key2216, -2), (key2216, -2), (key1979, -2)]

def rawRow14188 : Integer.Sparse Key := [(key1971, -2), (key1979, -2), (key1979, -2), (key1971, 6), (key2207, -2), (key2216, -2), (key2216, -2), (key1971, 2), (key1979, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key2216, 2), (key1971, -2), (key1971, -2), (key2207, -2), (key2216, 6), (key1979, -2), (key1979, -2), (key2216, -2)]

def rawRow14189 : Integer.Sparse Key := [(key1979, -2), (key1971, -2), (key1979, -2), (key1971, 6), (key2216, -2), (key2207, -2), (key2216, -2), (key1979, 2), (key1971, 2), (key2216, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key1971, -2), (key2207, -2), (key1971, -2), (key2216, 6), (key1979, -2), (key2216, -2), (key1979, -2)]

def rawRow14190 : Integer.Sparse Key := [(key1979, -2), (key1979, -2), (key1971, -2), (key1971, 6), (key2216, -2), (key2216, -2), (key2207, -2), (key2216, 2), (key2216, 2), (key1979, 2), (key1979, 2), (key1971, 2), (key1971, 2), (key2207, -2), (key1971, -2), (key1971, -2), (key2216, 6), (key2216, -2), (key1979, -2), (key1979, -2)]

def rawRow14191 : Integer.Sparse Key := [(key2207, -2), (key2216, -2), (key2216, -2), (key2216, 6), (key1971, -2), (key1979, -2), (key1979, -2), (key1971, 2), (key1979, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key2216, 2), (key1979, -2), (key1979, -2), (key2216, -2), (key1971, 6), (key1971, -2), (key1971, -2), (key2207, -2)]

def rawRow14192 : Integer.Sparse Key := [(key2216, -2), (key2207, -2), (key2216, -2), (key2216, 6), (key1979, -2), (key1971, -2), (key1979, -2), (key1979, 2), (key1971, 2), (key2216, 2), (key1971, 2), (key2216, 2), (key1979, 2), (key1979, -2), (key2216, -2), (key1979, -2), (key1971, 6), (key1971, -2), (key2207, -2), (key1971, -2)]

def rawRow14193 : Integer.Sparse Key := [(key2216, -2), (key2216, -2), (key2207, -2), (key2216, 6), (key1979, -2), (key1979, -2), (key1971, -2), (key2216, 2), (key2216, 2), (key1979, 2), (key1979, 2), (key1971, 2), (key1971, 2), (key2216, -2), (key1979, -2), (key1979, -2), (key1971, 6), (key2207, -2), (key1971, -2), (key1971, -2)]

def rawRow14194 : Integer.Sparse Key := [(key2216, -2), (key2216, -2), (key2216, -2), (key2207, 6), (key2216, -2), (key2216, -2), (key2216, -2), (key1979, 2), (key1979, 2), (key1979, 2), (key1979, 2), (key1979, 2), (key1979, 2), (key1971, -2), (key1971, -2), (key1971, -2), (key2207, 6), (key1971, -2), (key1971, -2), (key1971, -2)]

def rawRow14195 : Integer.Sparse Key := [(key756, 4), (key760, 4), (key760, 4), (key760, -4), (key760, -4), (key787, -4), (key760, -4), (key760, -4), (key787, -4), (key787, 12)]

def rawRow14196 : Integer.Sparse Key := [(key760, 4), (key756, 4), (key760, 4), (key760, -4), (key787, -4), (key760, -4), (key760, -4), (key787, -4), (key760, -4), (key787, 12)]

def rawRow14197 : Integer.Sparse Key := [(key760, 4), (key760, 4), (key756, 4), (key787, -4), (key760, -4), (key760, -4), (key787, -4), (key760, -4), (key760, -4), (key787, 12)]

def rawRow14198 : Integer.Sparse Key := [(key760, 4), (key760, 4), (key787, 4), (key756, -4), (key760, -4), (key760, -4), (key760, -4), (key787, -4), (key787, -4), (key760, 12)]

def rawRow14199 : Integer.Sparse Key := [(key760, 4), (key787, 4), (key760, 4), (key760, -4), (key756, -4), (key760, -4), (key787, -4), (key760, -4), (key787, -4), (key760, 12)]

def rawRow14200 : Integer.Sparse Key := [(key787, 4), (key760, 4), (key760, 4), (key760, -4), (key760, -4), (key756, -4), (key787, -4), (key787, -4), (key760, -4), (key760, 12)]

def rawRow14201 : Integer.Sparse Key := [(key760, 4), (key760, 4), (key787, 4), (key760, -4), (key787, -4), (key787, -4), (key756, -4), (key760, -4), (key760, -4), (key760, 12)]

def rawRow14202 : Integer.Sparse Key := [(key760, 4), (key787, 4), (key760, 4), (key787, -4), (key760, -4), (key787, -4), (key760, -4), (key756, -4), (key760, -4), (key760, 12)]

def rawRow14203 : Integer.Sparse Key := [(key787, 4), (key760, 4), (key760, 4), (key787, -4), (key787, -4), (key760, -4), (key760, -4), (key760, -4), (key756, -4), (key760, 12)]

def rawRow14204 : Integer.Sparse Key := [(key787, 4), (key787, 4), (key787, 4), (key760, -4), (key760, -4), (key760, -4), (key760, -4), (key760, -4), (key760, -4), (key756, 12)]

def rawRow14205 : Integer.Sparse Key := [(key2378, 4), (key2503, 4), (key2554, 4), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow14206 : Integer.Sparse Key := [(key2378, 4), (key2554, 4), (key2503, 4), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow14207 : Integer.Sparse Key := [(key2503, 4), (key2378, 4), (key2554, 4), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2482, 4), (key2392, 4), (key2543, 4)]

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

def rawRow14208 : Integer.Sparse Key := [(key2503, 4), (key2554, 4), (key2378, 4), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow14209 : Integer.Sparse Key := [(key2554, 4), (key2378, 4), (key2503, 4), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow14210 : Integer.Sparse Key := [(key2554, 4), (key2503, 4), (key2378, 4), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow14211 : Integer.Sparse Key := [(key2381, 4), (key2506, 4), (key2506, 4), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow14212 : Integer.Sparse Key := [(key2506, 4), (key2381, 4), (key2506, 4), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow14213 : Integer.Sparse Key := [(key2506, 4), (key2506, 4), (key2381, 4), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow14214 : Integer.Sparse Key := [(key2378, 4), (key2503, 4), (key2554, 4), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow14215 : Integer.Sparse Key := [(key2378, 4), (key2554, 4), (key2503, 4), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow14216 : Integer.Sparse Key := [(key2503, 4), (key2378, 4), (key2554, 4), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2482, 4), (key2392, 4), (key2543, 4)]

def rawRow14217 : Integer.Sparse Key := [(key2503, 4), (key2554, 4), (key2378, 4), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow14218 : Integer.Sparse Key := [(key2554, 4), (key2378, 4), (key2503, 4), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow14219 : Integer.Sparse Key := [(key2554, 4), (key2503, 4), (key2378, 4), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow14220 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2563, 4), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2381, 4), (key2409, 4), (key2538, 4)]

def rawRow14221 : Integer.Sparse Key := [(key2390, 4), (key2563, 4), (key2437, 4), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2381, 4), (key2538, 4), (key2409, 4)]

def rawRow14222 : Integer.Sparse Key := [(key2437, 4), (key2390, 4), (key2563, 4), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2409, 4), (key2381, 4), (key2538, 4)]

def rawRow14223 : Integer.Sparse Key := [(key2437, 4), (key2563, 4), (key2390, 4), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2409, 4), (key2538, 4), (key2381, 4)]

def rawRow14224 : Integer.Sparse Key := [(key2563, 4), (key2390, 4), (key2437, 4), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2538, 4), (key2381, 4), (key2409, 4)]

def rawRow14225 : Integer.Sparse Key := [(key2563, 4), (key2437, 4), (key2390, 4), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2538, 4), (key2409, 4), (key2381, 4)]

def rawRow14226 : Integer.Sparse Key := [(key2392, 4), (key2440, 4), (key2522, 4), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

def rawRow14227 : Integer.Sparse Key := [(key2392, 4), (key2522, 4), (key2440, 4), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

def rawRow14228 : Integer.Sparse Key := [(key2440, 4), (key2392, 4), (key2522, 4), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

def rawRow14229 : Integer.Sparse Key := [(key2440, 4), (key2522, 4), (key2392, 4), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

def rawRow14230 : Integer.Sparse Key := [(key2522, 4), (key2392, 4), (key2440, 4), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

def rawRow14231 : Integer.Sparse Key := [(key2522, 4), (key2440, 4), (key2392, 4), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

def rawRow14232 : Integer.Sparse Key := [(key2381, 4), (key2506, 4), (key2506, 4), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow14233 : Integer.Sparse Key := [(key2506, 4), (key2381, 4), (key2506, 4), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow14234 : Integer.Sparse Key := [(key2506, 4), (key2506, 4), (key2381, 4), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow14235 : Integer.Sparse Key := [(key2392, 4), (key2440, 4), (key2522, 4), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

def rawRow14236 : Integer.Sparse Key := [(key2392, 4), (key2522, 4), (key2440, 4), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

def rawRow14237 : Integer.Sparse Key := [(key2440, 4), (key2392, 4), (key2522, 4), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

def rawRow14238 : Integer.Sparse Key := [(key2440, 4), (key2522, 4), (key2392, 4), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

def rawRow14239 : Integer.Sparse Key := [(key2522, 4), (key2392, 4), (key2440, 4), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

def rawRow14240 : Integer.Sparse Key := [(key2522, 4), (key2440, 4), (key2392, 4), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

def rawRow14241 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1069, -2), (key1034, 6), (key1107, -2), (key1112, -2), (key1148, -2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key999, -2), (key1112, -2), (key1191, -2), (key1121, 6), (key1013, -2), (key1121, -2), (key1197, -2)]

def rawRow14242 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1069, -2), (key1034, 6), (key1112, -2), (key1107, -2), (key1148, -2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key999, -2), (key1191, -2), (key1112, -2), (key1121, 6), (key1013, -2), (key1197, -2), (key1121, -2)]

def rawRow14243 : Integer.Sparse Key := [(key1029, -2), (key1069, -2), (key1034, -2), (key1034, 6), (key1107, -2), (key1148, -2), (key1112, -2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1112, -2), (key999, -2), (key1191, -2), (key1121, 6), (key1121, -2), (key1013, -2), (key1197, -2)]

def rawRow14244 : Integer.Sparse Key := [(key1069, -2), (key1029, -2), (key1034, -2), (key1034, 6), (key1148, -2), (key1107, -2), (key1112, -2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1112, -2), (key1191, -2), (key999, -2), (key1121, 6), (key1121, -2), (key1197, -2), (key1013, -2)]

def rawRow14245 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1029, -2), (key1034, 6), (key1112, -2), (key1148, -2), (key1107, -2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1191, -2), (key999, -2), (key1112, -2), (key1121, 6), (key1197, -2), (key1013, -2), (key1121, -2)]

def rawRow14246 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1029, -2), (key1034, 6), (key1148, -2), (key1112, -2), (key1107, -2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1191, -2), (key1112, -2), (key999, -2), (key1121, 6), (key1197, -2), (key1121, -2), (key1013, -2)]

def rawRow14247 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1069, -2), (key1029, 6), (key1191, -2), (key1191, -2), (key1210, -2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1197, 6), (key1013, -2), (key1121, -2), (key1121, -2)]

def rawRow14248 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1034, -2), (key1029, 6), (key1191, -2), (key1210, -2), (key1191, -2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1197, 6), (key1121, -2), (key1013, -2), (key1121, -2)]

def rawRow14249 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1034, -2), (key1029, 6), (key1210, -2), (key1191, -2), (key1191, -2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1197, 6), (key1121, -2), (key1121, -2), (key1013, -2)]

def rawRow14250 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1148, -2), (key1121, 6), (key1029, -2), (key1034, -2), (key1069, -2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key1013, -2), (key1121, -2), (key1197, -2), (key1034, 6), (key999, -2), (key1112, -2), (key1191, -2)]

def rawRow14251 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1148, -2), (key1121, 6), (key1034, -2), (key1029, -2), (key1069, -2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1013, -2), (key1197, -2), (key1121, -2), (key1034, 6), (key999, -2), (key1191, -2), (key1112, -2)]

def rawRow14252 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1112, -2), (key1121, 6), (key1029, -2), (key1069, -2), (key1034, -2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1121, -2), (key1013, -2), (key1197, -2), (key1034, 6), (key1112, -2), (key999, -2), (key1191, -2)]

def rawRow14253 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1112, -2), (key1121, 6), (key1069, -2), (key1029, -2), (key1034, -2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1121, -2), (key1197, -2), (key1013, -2), (key1034, 6), (key1112, -2), (key1191, -2), (key999, -2)]

def rawRow14254 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1107, -2), (key1121, 6), (key1034, -2), (key1069, -2), (key1029, -2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1197, -2), (key1013, -2), (key1121, -2), (key1034, 6), (key1191, -2), (key999, -2), (key1112, -2)]

def rawRow14255 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1107, -2), (key1121, 6), (key1069, -2), (key1034, -2), (key1029, -2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1197, -2), (key1121, -2), (key1013, -2), (key1034, 6), (key1191, -2), (key1112, -2), (key999, -2)]

def rawRow14256 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1148, -2), (key1112, 6), (key1107, -2), (key1121, -2), (key1148, -2), (key994, 2), (key1013, 2), (key1029, 2), (key1197, 2), (key1069, 2), (key1210, 2), (key999, -2), (key1034, -2), (key1191, -2), (key1112, 6), (key999, -2), (key1034, -2), (key1191, -2)]

def rawRow14257 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1148, -2), (key1112, 6), (key1121, -2), (key1107, -2), (key1148, -2), (key1013, 2), (key994, 2), (key1197, 2), (key1029, 2), (key1210, 2), (key1069, 2), (key999, -2), (key1191, -2), (key1034, -2), (key1112, 6), (key999, -2), (key1191, -2), (key1034, -2)]

def rawRow14258 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1121, -2), (key1112, 6), (key1107, -2), (key1148, -2), (key1121, -2), (key1029, 2), (key1069, 2), (key994, 2), (key1210, 2), (key1013, 2), (key1197, 2), (key1034, -2), (key999, -2), (key1191, -2), (key1112, 6), (key1034, -2), (key999, -2), (key1191, -2)]

def rawRow14259 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1121, -2), (key1112, 6), (key1148, -2), (key1107, -2), (key1121, -2), (key1069, 2), (key1029, 2), (key1210, 2), (key994, 2), (key1197, 2), (key1013, 2), (key1034, -2), (key1191, -2), (key999, -2), (key1112, 6), (key1034, -2), (key1191, -2), (key999, -2)]

def rawRow14260 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1107, -2), (key1112, 6), (key1121, -2), (key1148, -2), (key1107, -2), (key1197, 2), (key1210, 2), (key1013, 2), (key1069, 2), (key994, 2), (key1029, 2), (key1191, -2), (key999, -2), (key1034, -2), (key1112, 6), (key1191, -2), (key999, -2), (key1034, -2)]

def rawRow14261 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1107, -2), (key1112, 6), (key1148, -2), (key1121, -2), (key1107, -2), (key1210, 2), (key1197, 2), (key1069, 2), (key1013, 2), (key1029, 2), (key994, 2), (key1191, -2), (key1034, -2), (key999, -2), (key1112, 6), (key1191, -2), (key1034, -2), (key999, -2)]

def rawRow14262 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1148, -2), (key1107, 6), (key1191, -2), (key1197, -2), (key1210, -2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1191, 6), (key999, -2), (key1034, -2), (key1112, -2)]

def rawRow14263 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1148, -2), (key1107, 6), (key1197, -2), (key1191, -2), (key1210, -2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1191, 6), (key999, -2), (key1112, -2), (key1034, -2)]

def rawRow14264 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1121, -2), (key1107, 6), (key1191, -2), (key1210, -2), (key1197, -2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1191, 6), (key1034, -2), (key999, -2), (key1112, -2)]

def rawRow14265 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1121, -2), (key1107, 6), (key1210, -2), (key1191, -2), (key1197, -2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1191, 6), (key1034, -2), (key1112, -2), (key999, -2)]

def rawRow14266 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1112, -2), (key1107, 6), (key1197, -2), (key1210, -2), (key1191, -2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1191, 6), (key1112, -2), (key999, -2), (key1034, -2)]

def rawRow14267 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1112, -2), (key1107, 6), (key1210, -2), (key1197, -2), (key1191, -2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1191, 6), (key1112, -2), (key1034, -2), (key999, -2)]

def rawRow14268 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1210, -2), (key1197, 6), (key1034, -2), (key1034, -2), (key1069, -2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key1013, -2), (key1121, -2), (key1121, -2), (key1029, 6), (key994, -2), (key1107, -2), (key1107, -2)]

def rawRow14269 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1191, -2), (key1197, 6), (key1034, -2), (key1069, -2), (key1034, -2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1121, -2), (key1013, -2), (key1121, -2), (key1029, 6), (key1107, -2), (key994, -2), (key1107, -2)]

def rawRow14270 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1191, -2), (key1197, 6), (key1069, -2), (key1034, -2), (key1034, -2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1121, -2), (key1121, -2), (key1013, -2), (key1029, 6), (key1107, -2), (key1107, -2), (key994, -2)]

def rawRow14271 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1210, -2), (key1191, 6), (key1112, -2), (key1121, -2), (key1148, -2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key999, -2), (key1034, -2), (key1112, -2), (key1107, 6), (key994, -2), (key1029, -2), (key1107, -2)]

def rawRow14272 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1210, -2), (key1191, 6), (key1121, -2), (key1112, -2), (key1148, -2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key999, -2), (key1112, -2), (key1034, -2), (key1107, 6), (key994, -2), (key1107, -2), (key1029, -2)]

def rawRow14273 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1197, -2), (key1191, 6), (key1112, -2), (key1148, -2), (key1121, -2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1034, -2), (key999, -2), (key1112, -2), (key1107, 6), (key1029, -2), (key994, -2), (key1107, -2)]

def rawRow14274 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1197, -2), (key1191, 6), (key1148, -2), (key1112, -2), (key1121, -2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1034, -2), (key1112, -2), (key999, -2), (key1107, 6), (key1029, -2), (key1107, -2), (key994, -2)]

def rawRow14275 : Integer.Sparse Key := [(key1197, -2), (key1210, -2), (key1191, -2), (key1191, 6), (key1121, -2), (key1148, -2), (key1112, -2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1112, -2), (key999, -2), (key1034, -2), (key1107, 6), (key1107, -2), (key994, -2), (key1029, -2)]

def rawRow14276 : Integer.Sparse Key := [(key1210, -2), (key1197, -2), (key1191, -2), (key1191, 6), (key1148, -2), (key1121, -2), (key1112, -2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1112, -2), (key1034, -2), (key999, -2), (key1107, 6), (key1107, -2), (key1029, -2), (key994, -2)]

def rawRow14277 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2434, -2), (key2403, 6), (key2465, -2), (key2469, -2), (key2500, -2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2375, -2), (key2469, -2), (key2536, -2), (key2477, 6), (key2387, -2), (key2477, -2), (key2541, -2)]

def rawRow14278 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2434, -2), (key2403, 6), (key2469, -2), (key2465, -2), (key2500, -2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2375, -2), (key2536, -2), (key2469, -2), (key2477, 6), (key2387, -2), (key2541, -2), (key2477, -2)]

def rawRow14279 : Integer.Sparse Key := [(key2399, -2), (key2434, -2), (key2403, -2), (key2403, 6), (key2465, -2), (key2500, -2), (key2469, -2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2469, -2), (key2375, -2), (key2536, -2), (key2477, 6), (key2477, -2), (key2387, -2), (key2541, -2)]

def rawRow14280 : Integer.Sparse Key := [(key2434, -2), (key2399, -2), (key2403, -2), (key2403, 6), (key2500, -2), (key2465, -2), (key2469, -2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2469, -2), (key2536, -2), (key2375, -2), (key2477, 6), (key2477, -2), (key2541, -2), (key2387, -2)]

def rawRow14281 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2399, -2), (key2403, 6), (key2469, -2), (key2500, -2), (key2465, -2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2536, -2), (key2375, -2), (key2469, -2), (key2477, 6), (key2541, -2), (key2387, -2), (key2477, -2)]

def rawRow14282 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2399, -2), (key2403, 6), (key2500, -2), (key2469, -2), (key2465, -2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2536, -2), (key2469, -2), (key2375, -2), (key2477, 6), (key2541, -2), (key2477, -2), (key2387, -2)]

def rawRow14283 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2434, -2), (key2399, 6), (key2536, -2), (key2536, -2), (key2552, -2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2371, -2), (key2465, -2), (key2465, -2), (key2541, 6), (key2387, -2), (key2477, -2), (key2477, -2)]

def rawRow14284 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2403, -2), (key2399, 6), (key2536, -2), (key2552, -2), (key2536, -2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2465, -2), (key2371, -2), (key2465, -2), (key2541, 6), (key2477, -2), (key2387, -2), (key2477, -2)]

def rawRow14285 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2403, -2), (key2399, 6), (key2552, -2), (key2536, -2), (key2536, -2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2465, -2), (key2465, -2), (key2371, -2), (key2541, 6), (key2477, -2), (key2477, -2), (key2387, -2)]

def rawRow14286 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2500, -2), (key2477, 6), (key2399, -2), (key2403, -2), (key2434, -2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2387, -2), (key2477, -2), (key2541, -2), (key2403, 6), (key2375, -2), (key2469, -2), (key2536, -2)]

def rawRow14287 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2500, -2), (key2477, 6), (key2403, -2), (key2399, -2), (key2434, -2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2387, -2), (key2541, -2), (key2477, -2), (key2403, 6), (key2375, -2), (key2536, -2), (key2469, -2)]

def rawRow14288 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2469, -2), (key2477, 6), (key2399, -2), (key2434, -2), (key2403, -2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2477, -2), (key2387, -2), (key2541, -2), (key2403, 6), (key2469, -2), (key2375, -2), (key2536, -2)]

def rawRow14289 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2469, -2), (key2477, 6), (key2434, -2), (key2399, -2), (key2403, -2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2477, -2), (key2541, -2), (key2387, -2), (key2403, 6), (key2469, -2), (key2536, -2), (key2375, -2)]

def rawRow14290 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2465, -2), (key2477, 6), (key2403, -2), (key2434, -2), (key2399, -2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2541, -2), (key2387, -2), (key2477, -2), (key2403, 6), (key2536, -2), (key2375, -2), (key2469, -2)]

def rawRow14291 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2465, -2), (key2477, 6), (key2434, -2), (key2403, -2), (key2399, -2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2541, -2), (key2477, -2), (key2387, -2), (key2403, 6), (key2536, -2), (key2469, -2), (key2375, -2)]

def rawRow14292 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2500, -2), (key2469, 6), (key2465, -2), (key2477, -2), (key2500, -2), (key2371, 2), (key2387, 2), (key2399, 2), (key2541, 2), (key2434, 2), (key2552, 2), (key2375, -2), (key2403, -2), (key2536, -2), (key2469, 6), (key2375, -2), (key2403, -2), (key2536, -2)]

def rawRow14293 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2500, -2), (key2469, 6), (key2477, -2), (key2465, -2), (key2500, -2), (key2387, 2), (key2371, 2), (key2541, 2), (key2399, 2), (key2552, 2), (key2434, 2), (key2375, -2), (key2536, -2), (key2403, -2), (key2469, 6), (key2375, -2), (key2536, -2), (key2403, -2)]

def rawRow14294 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2477, -2), (key2469, 6), (key2465, -2), (key2500, -2), (key2477, -2), (key2399, 2), (key2434, 2), (key2371, 2), (key2552, 2), (key2387, 2), (key2541, 2), (key2403, -2), (key2375, -2), (key2536, -2), (key2469, 6), (key2403, -2), (key2375, -2), (key2536, -2)]

def rawRow14295 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2477, -2), (key2469, 6), (key2500, -2), (key2465, -2), (key2477, -2), (key2434, 2), (key2399, 2), (key2552, 2), (key2371, 2), (key2541, 2), (key2387, 2), (key2403, -2), (key2536, -2), (key2375, -2), (key2469, 6), (key2403, -2), (key2536, -2), (key2375, -2)]

def rawRow14296 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2465, -2), (key2469, 6), (key2477, -2), (key2500, -2), (key2465, -2), (key2541, 2), (key2552, 2), (key2387, 2), (key2434, 2), (key2371, 2), (key2399, 2), (key2536, -2), (key2375, -2), (key2403, -2), (key2469, 6), (key2536, -2), (key2375, -2), (key2403, -2)]

def rawRow14297 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2465, -2), (key2469, 6), (key2500, -2), (key2477, -2), (key2465, -2), (key2552, 2), (key2541, 2), (key2434, 2), (key2387, 2), (key2399, 2), (key2371, 2), (key2536, -2), (key2403, -2), (key2375, -2), (key2469, 6), (key2536, -2), (key2403, -2), (key2375, -2)]

def rawRow14298 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2500, -2), (key2465, 6), (key2536, -2), (key2541, -2), (key2552, -2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2371, -2), (key2399, -2), (key2465, -2), (key2536, 6), (key2375, -2), (key2403, -2), (key2469, -2)]

def rawRow14299 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2500, -2), (key2465, 6), (key2541, -2), (key2536, -2), (key2552, -2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2371, -2), (key2465, -2), (key2399, -2), (key2536, 6), (key2375, -2), (key2469, -2), (key2403, -2)]

def rawRow14300 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2477, -2), (key2465, 6), (key2536, -2), (key2552, -2), (key2541, -2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2399, -2), (key2371, -2), (key2465, -2), (key2536, 6), (key2403, -2), (key2375, -2), (key2469, -2)]

def rawRow14301 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2477, -2), (key2465, 6), (key2552, -2), (key2536, -2), (key2541, -2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2399, -2), (key2465, -2), (key2371, -2), (key2536, 6), (key2403, -2), (key2469, -2), (key2375, -2)]

def rawRow14302 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2469, -2), (key2465, 6), (key2541, -2), (key2552, -2), (key2536, -2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2465, -2), (key2371, -2), (key2399, -2), (key2536, 6), (key2469, -2), (key2375, -2), (key2403, -2)]

def rawRow14303 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2469, -2), (key2465, 6), (key2552, -2), (key2541, -2), (key2536, -2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2465, -2), (key2399, -2), (key2371, -2), (key2536, 6), (key2469, -2), (key2403, -2), (key2375, -2)]

def rawRow14304 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2552, -2), (key2541, 6), (key2403, -2), (key2403, -2), (key2434, -2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2387, -2), (key2477, -2), (key2477, -2), (key2399, 6), (key2371, -2), (key2465, -2), (key2465, -2)]

def rawRow14305 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2536, -2), (key2541, 6), (key2403, -2), (key2434, -2), (key2403, -2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2477, -2), (key2387, -2), (key2477, -2), (key2399, 6), (key2465, -2), (key2371, -2), (key2465, -2)]

def rawRow14306 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2536, -2), (key2541, 6), (key2434, -2), (key2403, -2), (key2403, -2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2477, -2), (key2477, -2), (key2387, -2), (key2399, 6), (key2465, -2), (key2465, -2), (key2371, -2)]

def rawRow14307 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2552, -2), (key2536, 6), (key2469, -2), (key2477, -2), (key2500, -2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2375, -2), (key2403, -2), (key2469, -2), (key2465, 6), (key2371, -2), (key2399, -2), (key2465, -2)]

def rawRow14308 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2552, -2), (key2536, 6), (key2477, -2), (key2469, -2), (key2500, -2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2375, -2), (key2469, -2), (key2403, -2), (key2465, 6), (key2371, -2), (key2465, -2), (key2399, -2)]

def rawRow14309 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2541, -2), (key2536, 6), (key2469, -2), (key2500, -2), (key2477, -2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2403, -2), (key2375, -2), (key2469, -2), (key2465, 6), (key2399, -2), (key2371, -2), (key2465, -2)]

def rawRow14310 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2541, -2), (key2536, 6), (key2500, -2), (key2469, -2), (key2477, -2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2403, -2), (key2469, -2), (key2375, -2), (key2465, 6), (key2399, -2), (key2465, -2), (key2371, -2)]

def rawRow14311 : Integer.Sparse Key := [(key2541, -2), (key2552, -2), (key2536, -2), (key2536, 6), (key2477, -2), (key2500, -2), (key2469, -2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2469, -2), (key2375, -2), (key2403, -2), (key2465, 6), (key2465, -2), (key2371, -2), (key2399, -2)]

def rawRow14312 : Integer.Sparse Key := [(key2552, -2), (key2541, -2), (key2536, -2), (key2536, 6), (key2500, -2), (key2477, -2), (key2469, -2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2469, -2), (key2403, -2), (key2375, -2), (key2465, 6), (key2465, -2), (key2399, -2), (key2371, -2)]

def rawRow14313 : Integer.Sparse Key := [(key2777, 6), (key2662, -2), (key2777, -2), (key2788, -2), (key2800, 6), (key2607, -2), (key2800, -2), (key2823, -2), (key2697, -2), (key2850, -2), (key2854, -2), (key2623, -2), (key2850, -2), (key2864, -2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

def rawRow14314 : Integer.Sparse Key := [(key2777, 6), (key2662, -2), (key2788, -2), (key2777, -2), (key2800, 6), (key2607, -2), (key2823, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, -2), (key2864, -2), (key2850, -2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

def rawRow14315 : Integer.Sparse Key := [(key2777, 6), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, 6), (key2800, -2), (key2607, -2), (key2823, -2), (key2850, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, -2), (key2864, -2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

def rawRow14316 : Integer.Sparse Key := [(key2777, 6), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, 6), (key2800, -2), (key2823, -2), (key2607, -2), (key2850, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, -2), (key2623, -2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

def rawRow14317 : Integer.Sparse Key := [(key2777, 6), (key2788, -2), (key2662, -2), (key2777, -2), (key2800, 6), (key2823, -2), (key2607, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, -2), (key2623, -2), (key2850, -2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

def rawRow14318 : Integer.Sparse Key := [(key2777, 6), (key2788, -2), (key2777, -2), (key2662, -2), (key2800, 6), (key2823, -2), (key2800, -2), (key2607, -2), (key2854, -2), (key2850, -2), (key2697, -2), (key2864, -2), (key2850, -2), (key2623, -2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

def rawRow14319 : Integer.Sparse Key := [(key2788, 6), (key2662, -2), (key2777, -2), (key2777, -2), (key2823, 6), (key2607, -2), (key2800, -2), (key2800, -2), (key2720, -2), (key2864, -2), (key2864, -2), (key2634, -2), (key2854, -2), (key2854, -2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

def rawRow14320 : Integer.Sparse Key := [(key2788, 6), (key2777, -2), (key2662, -2), (key2777, -2), (key2823, 6), (key2800, -2), (key2607, -2), (key2800, -2), (key2864, -2), (key2720, -2), (key2864, -2), (key2854, -2), (key2634, -2), (key2854, -2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

def rawRow14321 : Integer.Sparse Key := [(key2788, 6), (key2777, -2), (key2777, -2), (key2662, -2), (key2823, 6), (key2800, -2), (key2800, -2), (key2607, -2), (key2864, -2), (key2864, -2), (key2720, -2), (key2854, -2), (key2854, -2), (key2634, -2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

def rawRow14322 : Integer.Sparse Key := [(key2800, 6), (key2697, -2), (key2850, -2), (key2854, -2), (key2777, 6), (key2623, -2), (key2850, -2), (key2864, -2), (key2662, -2), (key2777, -2), (key2788, -2), (key2607, -2), (key2800, -2), (key2823, -2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

def rawRow14323 : Integer.Sparse Key := [(key2800, 6), (key2697, -2), (key2854, -2), (key2850, -2), (key2777, 6), (key2623, -2), (key2864, -2), (key2850, -2), (key2662, -2), (key2788, -2), (key2777, -2), (key2607, -2), (key2823, -2), (key2800, -2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

def rawRow14324 : Integer.Sparse Key := [(key2800, 6), (key2850, -2), (key2697, -2), (key2854, -2), (key2777, 6), (key2850, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, -2), (key2607, -2), (key2823, -2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

def rawRow14325 : Integer.Sparse Key := [(key2800, 6), (key2850, -2), (key2854, -2), (key2697, -2), (key2777, 6), (key2850, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, -2), (key2823, -2), (key2607, -2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

def rawRow14326 : Integer.Sparse Key := [(key2800, 6), (key2854, -2), (key2697, -2), (key2850, -2), (key2777, 6), (key2864, -2), (key2623, -2), (key2850, -2), (key2788, -2), (key2662, -2), (key2777, -2), (key2823, -2), (key2607, -2), (key2800, -2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

def rawRow14327 : Integer.Sparse Key := [(key2800, 6), (key2854, -2), (key2850, -2), (key2697, -2), (key2777, 6), (key2864, -2), (key2850, -2), (key2623, -2), (key2788, -2), (key2777, -2), (key2662, -2), (key2823, -2), (key2800, -2), (key2607, -2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

def rawRow14328 : Integer.Sparse Key := [(key2850, 6), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, 6), (key2623, -2), (key2777, -2), (key2864, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2607, 2), (key2634, 2), (key2662, 2), (key2720, 2), (key2788, 2), (key2823, 2)]

def rawRow14329 : Integer.Sparse Key := [(key2850, 6), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, 6), (key2623, -2), (key2864, -2), (key2777, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2634, 2), (key2607, 2), (key2720, 2), (key2662, 2), (key2823, 2), (key2788, 2)]

def rawRow14330 : Integer.Sparse Key := [(key2850, 6), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, 6), (key2777, -2), (key2623, -2), (key2864, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2662, 2), (key2788, 2), (key2607, 2), (key2823, 2), (key2634, 2), (key2720, 2)]

def rawRow14331 : Integer.Sparse Key := [(key2850, 6), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, 6), (key2777, -2), (key2864, -2), (key2623, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2788, 2), (key2662, 2), (key2823, 2), (key2607, 2), (key2720, 2), (key2634, 2)]

def rawRow14332 : Integer.Sparse Key := [(key2850, 6), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, 6), (key2864, -2), (key2623, -2), (key2777, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2720, 2), (key2823, 2), (key2634, 2), (key2788, 2), (key2607, 2), (key2662, 2)]

def rawRow14333 : Integer.Sparse Key := [(key2850, 6), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, 6), (key2864, -2), (key2777, -2), (key2623, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2823, 2), (key2720, 2), (key2788, 2), (key2634, 2), (key2662, 2), (key2607, 2)]

def rawRow14334 : Integer.Sparse Key := [(key2854, 6), (key2697, -2), (key2800, -2), (key2850, -2), (key2864, 6), (key2623, -2), (key2777, -2), (key2850, -2), (key2720, -2), (key2823, -2), (key2864, -2), (key2634, -2), (key2788, -2), (key2854, -2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

def rawRow14335 : Integer.Sparse Key := [(key2854, 6), (key2697, -2), (key2850, -2), (key2800, -2), (key2864, 6), (key2623, -2), (key2850, -2), (key2777, -2), (key2720, -2), (key2864, -2), (key2823, -2), (key2634, -2), (key2854, -2), (key2788, -2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

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

def rawRow14336 : Integer.Sparse Key := [(key2854, 6), (key2800, -2), (key2697, -2), (key2850, -2), (key2864, 6), (key2777, -2), (key2623, -2), (key2850, -2), (key2823, -2), (key2720, -2), (key2864, -2), (key2788, -2), (key2634, -2), (key2854, -2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

def rawRow14337 : Integer.Sparse Key := [(key2854, 6), (key2800, -2), (key2850, -2), (key2697, -2), (key2864, 6), (key2777, -2), (key2850, -2), (key2623, -2), (key2823, -2), (key2864, -2), (key2720, -2), (key2788, -2), (key2854, -2), (key2634, -2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

def rawRow14338 : Integer.Sparse Key := [(key2854, 6), (key2850, -2), (key2697, -2), (key2800, -2), (key2864, 6), (key2850, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, -2), (key2634, -2), (key2788, -2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

def rawRow14339 : Integer.Sparse Key := [(key2854, 6), (key2850, -2), (key2800, -2), (key2697, -2), (key2864, 6), (key2850, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, -2), (key2788, -2), (key2634, -2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

def rawRow14340 : Integer.Sparse Key := [(key2823, 6), (key2720, -2), (key2864, -2), (key2864, -2), (key2788, 6), (key2634, -2), (key2854, -2), (key2854, -2), (key2662, -2), (key2777, -2), (key2777, -2), (key2607, -2), (key2800, -2), (key2800, -2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

def rawRow14341 : Integer.Sparse Key := [(key2823, 6), (key2864, -2), (key2720, -2), (key2864, -2), (key2788, 6), (key2854, -2), (key2634, -2), (key2854, -2), (key2777, -2), (key2662, -2), (key2777, -2), (key2800, -2), (key2607, -2), (key2800, -2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

def rawRow14342 : Integer.Sparse Key := [(key2823, 6), (key2864, -2), (key2864, -2), (key2720, -2), (key2788, 6), (key2854, -2), (key2854, -2), (key2634, -2), (key2777, -2), (key2777, -2), (key2662, -2), (key2800, -2), (key2800, -2), (key2607, -2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

def rawRow14343 : Integer.Sparse Key := [(key2864, 6), (key2720, -2), (key2823, -2), (key2864, -2), (key2854, 6), (key2634, -2), (key2788, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, -2), (key2777, -2), (key2850, -2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

def rawRow14344 : Integer.Sparse Key := [(key2864, 6), (key2720, -2), (key2864, -2), (key2823, -2), (key2854, 6), (key2634, -2), (key2854, -2), (key2788, -2), (key2697, -2), (key2850, -2), (key2800, -2), (key2623, -2), (key2850, -2), (key2777, -2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

def rawRow14345 : Integer.Sparse Key := [(key2864, 6), (key2823, -2), (key2720, -2), (key2864, -2), (key2854, 6), (key2788, -2), (key2634, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, -2), (key2623, -2), (key2850, -2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

def rawRow14346 : Integer.Sparse Key := [(key2864, 6), (key2823, -2), (key2864, -2), (key2720, -2), (key2854, 6), (key2788, -2), (key2854, -2), (key2634, -2), (key2800, -2), (key2850, -2), (key2697, -2), (key2777, -2), (key2850, -2), (key2623, -2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

def rawRow14347 : Integer.Sparse Key := [(key2864, 6), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, 6), (key2854, -2), (key2634, -2), (key2788, -2), (key2850, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, -2), (key2777, -2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

def rawRow14348 : Integer.Sparse Key := [(key2864, 6), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, 6), (key2854, -2), (key2788, -2), (key2634, -2), (key2850, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, -2), (key2623, -2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

def rawRow14349 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1068, -2), (key1032, 6), (key1106, -2), (key1110, -2), (key1147, -2), (key993, 2), (key997, 2), (key1106, 2), (key1189, 2), (key1147, 2), (key1209, 2), (key997, -2), (key1110, -2), (key1189, -2), (key1120, 6), (key1012, -2), (key1120, -2), (key1196, -2)]

def rawRow14350 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1068, -2), (key1032, 6), (key1110, -2), (key1106, -2), (key1147, -2), (key997, 2), (key993, 2), (key1189, 2), (key1106, 2), (key1209, 2), (key1147, 2), (key997, -2), (key1189, -2), (key1110, -2), (key1120, 6), (key1012, -2), (key1196, -2), (key1120, -2)]

def rawRow14351 : Integer.Sparse Key := [(key1028, -2), (key1068, -2), (key1032, -2), (key1032, 6), (key1106, -2), (key1147, -2), (key1110, -2), (key1106, 2), (key1147, 2), (key993, 2), (key1209, 2), (key997, 2), (key1189, 2), (key1110, -2), (key997, -2), (key1189, -2), (key1120, 6), (key1120, -2), (key1012, -2), (key1196, -2)]

def rawRow14352 : Integer.Sparse Key := [(key1068, -2), (key1028, -2), (key1032, -2), (key1032, 6), (key1147, -2), (key1106, -2), (key1110, -2), (key1147, 2), (key1106, 2), (key1209, 2), (key993, 2), (key1189, 2), (key997, 2), (key1110, -2), (key1189, -2), (key997, -2), (key1120, 6), (key1120, -2), (key1196, -2), (key1012, -2)]

def rawRow14353 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1028, -2), (key1032, 6), (key1110, -2), (key1147, -2), (key1106, -2), (key1189, 2), (key1209, 2), (key997, 2), (key1147, 2), (key993, 2), (key1106, 2), (key1189, -2), (key997, -2), (key1110, -2), (key1120, 6), (key1196, -2), (key1012, -2), (key1120, -2)]

def rawRow14354 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1028, -2), (key1032, 6), (key1147, -2), (key1110, -2), (key1106, -2), (key1209, 2), (key1189, 2), (key1147, 2), (key997, 2), (key1106, 2), (key993, 2), (key1189, -2), (key1110, -2), (key997, -2), (key1120, 6), (key1196, -2), (key1120, -2), (key1012, -2)]

def rawRow14355 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1068, -2), (key1028, 6), (key1189, -2), (key1189, -2), (key1209, -2), (key997, 2), (key997, 2), (key1110, 2), (key1110, 2), (key1147, 2), (key1147, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1196, 6), (key1012, -2), (key1120, -2), (key1120, -2)]

def rawRow14356 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1032, -2), (key1028, 6), (key1189, -2), (key1209, -2), (key1189, -2), (key1110, 2), (key1147, 2), (key997, 2), (key1147, 2), (key997, 2), (key1110, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1196, 6), (key1120, -2), (key1012, -2), (key1120, -2)]

def rawRow14357 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1032, -2), (key1028, 6), (key1209, -2), (key1189, -2), (key1189, -2), (key1147, 2), (key1110, 2), (key1147, 2), (key997, 2), (key1110, 2), (key997, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1196, 6), (key1120, -2), (key1120, -2), (key1012, -2)]

def rawRow14358 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1147, -2), (key1120, 6), (key1028, -2), (key1032, -2), (key1068, -2), (key993, 2), (key997, 2), (key1106, 2), (key1189, 2), (key1147, 2), (key1209, 2), (key1012, -2), (key1120, -2), (key1196, -2), (key1032, 6), (key997, -2), (key1110, -2), (key1189, -2)]

def rawRow14359 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1147, -2), (key1120, 6), (key1032, -2), (key1028, -2), (key1068, -2), (key997, 2), (key993, 2), (key1189, 2), (key1106, 2), (key1209, 2), (key1147, 2), (key1012, -2), (key1196, -2), (key1120, -2), (key1032, 6), (key997, -2), (key1189, -2), (key1110, -2)]

def rawRow14360 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1110, -2), (key1120, 6), (key1028, -2), (key1068, -2), (key1032, -2), (key1106, 2), (key1147, 2), (key993, 2), (key1209, 2), (key997, 2), (key1189, 2), (key1120, -2), (key1012, -2), (key1196, -2), (key1032, 6), (key1110, -2), (key997, -2), (key1189, -2)]

def rawRow14361 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1110, -2), (key1120, 6), (key1068, -2), (key1028, -2), (key1032, -2), (key1147, 2), (key1106, 2), (key1209, 2), (key993, 2), (key1189, 2), (key997, 2), (key1120, -2), (key1196, -2), (key1012, -2), (key1032, 6), (key1110, -2), (key1189, -2), (key997, -2)]

def rawRow14362 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1106, -2), (key1120, 6), (key1032, -2), (key1068, -2), (key1028, -2), (key1189, 2), (key1209, 2), (key997, 2), (key1147, 2), (key993, 2), (key1106, 2), (key1196, -2), (key1012, -2), (key1120, -2), (key1032, 6), (key1189, -2), (key997, -2), (key1110, -2)]

def rawRow14363 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1106, -2), (key1120, 6), (key1068, -2), (key1032, -2), (key1028, -2), (key1209, 2), (key1189, 2), (key1147, 2), (key997, 2), (key1106, 2), (key993, 2), (key1196, -2), (key1120, -2), (key1012, -2), (key1032, 6), (key1189, -2), (key1110, -2), (key997, -2)]

def rawRow14364 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1147, -2), (key1110, 6), (key1106, -2), (key1120, -2), (key1147, -2), (key993, 2), (key1012, 2), (key1028, 2), (key1196, 2), (key1068, 2), (key1209, 2), (key997, -2), (key1032, -2), (key1189, -2), (key1110, 6), (key997, -2), (key1032, -2), (key1189, -2)]

def rawRow14365 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1147, -2), (key1110, 6), (key1120, -2), (key1106, -2), (key1147, -2), (key1012, 2), (key993, 2), (key1196, 2), (key1028, 2), (key1209, 2), (key1068, 2), (key997, -2), (key1189, -2), (key1032, -2), (key1110, 6), (key997, -2), (key1189, -2), (key1032, -2)]

def rawRow14366 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1120, -2), (key1110, 6), (key1106, -2), (key1147, -2), (key1120, -2), (key1028, 2), (key1068, 2), (key993, 2), (key1209, 2), (key1012, 2), (key1196, 2), (key1032, -2), (key997, -2), (key1189, -2), (key1110, 6), (key1032, -2), (key997, -2), (key1189, -2)]

def rawRow14367 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1120, -2), (key1110, 6), (key1147, -2), (key1106, -2), (key1120, -2), (key1068, 2), (key1028, 2), (key1209, 2), (key993, 2), (key1196, 2), (key1012, 2), (key1032, -2), (key1189, -2), (key997, -2), (key1110, 6), (key1032, -2), (key1189, -2), (key997, -2)]

def rawRow14368 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1106, -2), (key1110, 6), (key1120, -2), (key1147, -2), (key1106, -2), (key1196, 2), (key1209, 2), (key1012, 2), (key1068, 2), (key993, 2), (key1028, 2), (key1189, -2), (key997, -2), (key1032, -2), (key1110, 6), (key1189, -2), (key997, -2), (key1032, -2)]

def rawRow14369 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1106, -2), (key1110, 6), (key1147, -2), (key1120, -2), (key1106, -2), (key1209, 2), (key1196, 2), (key1068, 2), (key1012, 2), (key1028, 2), (key993, 2), (key1189, -2), (key1032, -2), (key997, -2), (key1110, 6), (key1189, -2), (key1032, -2), (key997, -2)]

def rawRow14370 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1147, -2), (key1106, 6), (key1189, -2), (key1196, -2), (key1209, -2), (key997, 2), (key1012, 2), (key1032, 2), (key1120, 2), (key1068, 2), (key1147, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1189, 6), (key997, -2), (key1032, -2), (key1110, -2)]

def rawRow14371 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1147, -2), (key1106, 6), (key1196, -2), (key1189, -2), (key1209, -2), (key1012, 2), (key997, 2), (key1120, 2), (key1032, 2), (key1147, 2), (key1068, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1189, 6), (key997, -2), (key1110, -2), (key1032, -2)]

def rawRow14372 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1120, -2), (key1106, 6), (key1189, -2), (key1209, -2), (key1196, -2), (key1032, 2), (key1068, 2), (key997, 2), (key1147, 2), (key1012, 2), (key1120, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1189, 6), (key1032, -2), (key997, -2), (key1110, -2)]

def rawRow14373 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1120, -2), (key1106, 6), (key1209, -2), (key1189, -2), (key1196, -2), (key1068, 2), (key1032, 2), (key1147, 2), (key997, 2), (key1120, 2), (key1012, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1189, 6), (key1032, -2), (key1110, -2), (key997, -2)]

def rawRow14374 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1110, -2), (key1106, 6), (key1196, -2), (key1209, -2), (key1189, -2), (key1120, 2), (key1147, 2), (key1012, 2), (key1068, 2), (key997, 2), (key1032, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1189, 6), (key1110, -2), (key997, -2), (key1032, -2)]

def rawRow14375 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1110, -2), (key1106, 6), (key1209, -2), (key1196, -2), (key1189, -2), (key1147, 2), (key1120, 2), (key1068, 2), (key1012, 2), (key1032, 2), (key997, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1189, 6), (key1110, -2), (key1032, -2), (key997, -2)]

def rawRow14376 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1209, -2), (key1196, 6), (key1032, -2), (key1032, -2), (key1068, -2), (key997, 2), (key997, 2), (key1110, 2), (key1110, 2), (key1147, 2), (key1147, 2), (key1012, -2), (key1120, -2), (key1120, -2), (key1028, 6), (key993, -2), (key1106, -2), (key1106, -2)]

def rawRow14377 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1189, -2), (key1196, 6), (key1032, -2), (key1068, -2), (key1032, -2), (key1110, 2), (key1147, 2), (key997, 2), (key1147, 2), (key997, 2), (key1110, 2), (key1120, -2), (key1012, -2), (key1120, -2), (key1028, 6), (key1106, -2), (key993, -2), (key1106, -2)]

def rawRow14378 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1189, -2), (key1196, 6), (key1068, -2), (key1032, -2), (key1032, -2), (key1147, 2), (key1110, 2), (key1147, 2), (key997, 2), (key1110, 2), (key997, 2), (key1120, -2), (key1120, -2), (key1012, -2), (key1028, 6), (key1106, -2), (key1106, -2), (key993, -2)]

def rawRow14379 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1209, -2), (key1189, 6), (key1110, -2), (key1120, -2), (key1147, -2), (key997, 2), (key1012, 2), (key1032, 2), (key1120, 2), (key1068, 2), (key1147, 2), (key997, -2), (key1032, -2), (key1110, -2), (key1106, 6), (key993, -2), (key1028, -2), (key1106, -2)]

def rawRow14380 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1209, -2), (key1189, 6), (key1120, -2), (key1110, -2), (key1147, -2), (key1012, 2), (key997, 2), (key1120, 2), (key1032, 2), (key1147, 2), (key1068, 2), (key997, -2), (key1110, -2), (key1032, -2), (key1106, 6), (key993, -2), (key1106, -2), (key1028, -2)]

def rawRow14381 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1196, -2), (key1189, 6), (key1110, -2), (key1147, -2), (key1120, -2), (key1032, 2), (key1068, 2), (key997, 2), (key1147, 2), (key1012, 2), (key1120, 2), (key1032, -2), (key997, -2), (key1110, -2), (key1106, 6), (key1028, -2), (key993, -2), (key1106, -2)]

def rawRow14382 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1196, -2), (key1189, 6), (key1147, -2), (key1110, -2), (key1120, -2), (key1068, 2), (key1032, 2), (key1147, 2), (key997, 2), (key1120, 2), (key1012, 2), (key1032, -2), (key1110, -2), (key997, -2), (key1106, 6), (key1028, -2), (key1106, -2), (key993, -2)]

def rawRow14383 : Integer.Sparse Key := [(key1196, -2), (key1209, -2), (key1189, -2), (key1189, 6), (key1120, -2), (key1147, -2), (key1110, -2), (key1120, 2), (key1147, 2), (key1012, 2), (key1068, 2), (key997, 2), (key1032, 2), (key1110, -2), (key997, -2), (key1032, -2), (key1106, 6), (key1106, -2), (key993, -2), (key1028, -2)]

def rawRow14384 : Integer.Sparse Key := [(key1209, -2), (key1196, -2), (key1189, -2), (key1189, 6), (key1147, -2), (key1120, -2), (key1110, -2), (key1147, 2), (key1120, 2), (key1068, 2), (key1012, 2), (key1032, 2), (key997, 2), (key1110, -2), (key1032, -2), (key997, -2), (key1106, 6), (key1106, -2), (key1028, -2), (key993, -2)]

def rawRow14385 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1213, 4), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1020, 4), (key1128, 4), (key1200, 4)]

def rawRow14386 : Integer.Sparse Key := [(key1003, 4), (key1213, 4), (key1152, 4), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1020, 4), (key1200, 4), (key1128, 4)]

def rawRow14387 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1213, 4), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1128, 4), (key1020, 4), (key1200, 4)]

def rawRow14388 : Integer.Sparse Key := [(key1152, 4), (key1213, 4), (key1003, 4), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1128, 4), (key1200, 4), (key1020, 4)]

def rawRow14389 : Integer.Sparse Key := [(key1213, 4), (key1003, 4), (key1152, 4), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1200, 4), (key1020, 4), (key1128, 4)]

def rawRow14390 : Integer.Sparse Key := [(key1213, 4), (key1152, 4), (key1003, 4), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1200, 4), (key1128, 4), (key1020, 4)]

def rawRow14391 : Integer.Sparse Key := [(key1007, 4), (key1156, 4), (key1156, 4), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

def rawRow14392 : Integer.Sparse Key := [(key1156, 4), (key1007, 4), (key1156, 4), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

def rawRow14393 : Integer.Sparse Key := [(key1156, 4), (key1156, 4), (key1007, 4), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

def rawRow14394 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1213, 4), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1020, 4), (key1128, 4), (key1200, 4)]

def rawRow14395 : Integer.Sparse Key := [(key1003, 4), (key1213, 4), (key1152, 4), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, 4), (key1200, 4), (key1128, 4)]

def rawRow14396 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1213, 4), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1128, 4), (key1020, 4), (key1200, 4)]

def rawRow14397 : Integer.Sparse Key := [(key1152, 4), (key1213, 4), (key1003, 4), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1128, 4), (key1200, 4), (key1020, 4)]

def rawRow14398 : Integer.Sparse Key := [(key1213, 4), (key1003, 4), (key1152, 4), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, 4), (key1020, 4), (key1128, 4)]

def rawRow14399 : Integer.Sparse Key := [(key1213, 4), (key1152, 4), (key1003, 4), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1200, 4), (key1128, 4), (key1020, 4)]

def rawRow14400 : Integer.Sparse Key := [(key1017, 4), (key1073, 4), (key1223, 4), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1007, 4), (key1042, 4), (key1194, 4)]

def rawRow14401 : Integer.Sparse Key := [(key1017, 4), (key1223, 4), (key1073, 4), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1007, 4), (key1194, 4), (key1042, 4)]

def rawRow14402 : Integer.Sparse Key := [(key1073, 4), (key1017, 4), (key1223, 4), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1042, 4), (key1007, 4), (key1194, 4)]

def rawRow14403 : Integer.Sparse Key := [(key1073, 4), (key1223, 4), (key1017, 4), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1042, 4), (key1194, 4), (key1007, 4)]

def rawRow14404 : Integer.Sparse Key := [(key1223, 4), (key1017, 4), (key1073, 4), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1194, 4), (key1007, 4), (key1042, 4)]

def rawRow14405 : Integer.Sparse Key := [(key1223, 4), (key1073, 4), (key1017, 4), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1194, 4), (key1042, 4), (key1007, 4)]

def rawRow14406 : Integer.Sparse Key := [(key1020, 4), (key1077, 4), (key1172, 4), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

def rawRow14407 : Integer.Sparse Key := [(key1020, 4), (key1172, 4), (key1077, 4), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

def rawRow14408 : Integer.Sparse Key := [(key1077, 4), (key1020, 4), (key1172, 4), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

def rawRow14409 : Integer.Sparse Key := [(key1077, 4), (key1172, 4), (key1020, 4), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

def rawRow14410 : Integer.Sparse Key := [(key1172, 4), (key1020, 4), (key1077, 4), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

def rawRow14411 : Integer.Sparse Key := [(key1172, 4), (key1077, 4), (key1020, 4), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

def rawRow14412 : Integer.Sparse Key := [(key1007, 4), (key1156, 4), (key1156, 4), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

def rawRow14413 : Integer.Sparse Key := [(key1156, 4), (key1007, 4), (key1156, 4), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

def rawRow14414 : Integer.Sparse Key := [(key1156, 4), (key1156, 4), (key1007, 4), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

def rawRow14415 : Integer.Sparse Key := [(key1020, 4), (key1077, 4), (key1172, 4), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

def rawRow14416 : Integer.Sparse Key := [(key1020, 4), (key1172, 4), (key1077, 4), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

def rawRow14417 : Integer.Sparse Key := [(key1077, 4), (key1020, 4), (key1172, 4), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

def rawRow14418 : Integer.Sparse Key := [(key1077, 4), (key1172, 4), (key1020, 4), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

def rawRow14419 : Integer.Sparse Key := [(key1172, 4), (key1020, 4), (key1077, 4), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

def rawRow14420 : Integer.Sparse Key := [(key1172, 4), (key1077, 4), (key1020, 4), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

def rawRow14421 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1)]

def rawRow14422 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1)]

def rawRow14423 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1)]

def rawRow14424 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1)]

def rawRow14425 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1)]

def rawRow14426 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1)]

def rawRow14427 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1)]

def rawRow14428 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1)]

def rawRow14429 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1)]

def rawRow14430 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1)]

def rawRow14431 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1)]

def rawRow14432 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1)]

def rawRow14433 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1)]

def rawRow14434 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1)]

def rawRow14435 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1)]

def rawRow14436 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2699, -1), (key2975, -1), (key2723, -1), (key2982, -1), (key2629, 2), (key2703, 2), (key2973, 2), (key2625, -1), (key2637, -1), (key2699, -1), (key2975, -1), (key2723, -1), (key2982, -1), (key2609, 2), (key2652, 2), (key2664, 2), (key2942, 2), (key2746, 2), (key2959, 2), (key2613, -1), (key2647, -1), (key2668, -1), (key2937, -1), (key2736, -1), (key2949, -1), (key2629, 2), (key2703, 2), (key2973, 2), (key2613, -1), (key2647, -1), (key2668, -1), (key2937, -1), (key2736, -1), (key2949, -1)]

def rawRow14437 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2975, -1), (key2699, -1), (key2982, -1), (key2723, -1), (key2629, 2), (key2973, 2), (key2703, 2), (key2637, -1), (key2625, -1), (key2975, -1), (key2699, -1), (key2982, -1), (key2723, -1), (key2652, 2), (key2609, 2), (key2942, 2), (key2664, 2), (key2959, 2), (key2746, 2), (key2647, -1), (key2613, -1), (key2937, -1), (key2668, -1), (key2949, -1), (key2736, -1), (key2629, 2), (key2973, 2), (key2703, 2), (key2647, -1), (key2613, -1), (key2937, -1), (key2668, -1), (key2949, -1), (key2736, -1)]

def rawRow14438 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2625, -1), (key2982, -1), (key2637, -1), (key2975, -1), (key2703, 2), (key2629, 2), (key2973, 2), (key2699, -1), (key2723, -1), (key2625, -1), (key2982, -1), (key2637, -1), (key2975, -1), (key2664, 2), (key2746, 2), (key2609, 2), (key2959, 2), (key2652, 2), (key2942, 2), (key2668, -1), (key2736, -1), (key2613, -1), (key2949, -1), (key2647, -1), (key2937, -1), (key2703, 2), (key2629, 2), (key2973, 2), (key2668, -1), (key2736, -1), (key2613, -1), (key2949, -1), (key2647, -1), (key2937, -1)]

def rawRow14439 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2982, -1), (key2625, -1), (key2975, -1), (key2637, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2723, -1), (key2699, -1), (key2982, -1), (key2625, -1), (key2975, -1), (key2637, -1), (key2746, 2), (key2664, 2), (key2959, 2), (key2609, 2), (key2942, 2), (key2652, 2), (key2736, -1), (key2668, -1), (key2949, -1), (key2613, -1), (key2937, -1), (key2647, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2736, -1), (key2668, -1), (key2949, -1), (key2613, -1), (key2937, -1), (key2647, -1)]

def rawRow14440 : Integer.Sparse Key := [(key2975, -1), (key2982, -1), (key2637, -1), (key2723, -1), (key2625, -1), (key2699, -1), (key2973, 2), (key2629, 2), (key2703, 2), (key2975, -1), (key2982, -1), (key2637, -1), (key2723, -1), (key2625, -1), (key2699, -1), (key2942, 2), (key2959, 2), (key2652, 2), (key2746, 2), (key2609, 2), (key2664, 2), (key2937, -1), (key2949, -1), (key2647, -1), (key2736, -1), (key2613, -1), (key2668, -1), (key2973, 2), (key2629, 2), (key2703, 2), (key2937, -1), (key2949, -1), (key2647, -1), (key2736, -1), (key2613, -1), (key2668, -1)]

def rawRow14441 : Integer.Sparse Key := [(key2982, -1), (key2975, -1), (key2723, -1), (key2637, -1), (key2699, -1), (key2625, -1), (key2973, 2), (key2703, 2), (key2629, 2), (key2982, -1), (key2975, -1), (key2723, -1), (key2637, -1), (key2699, -1), (key2625, -1), (key2959, 2), (key2942, 2), (key2746, 2), (key2652, 2), (key2664, 2), (key2609, 2), (key2949, -1), (key2937, -1), (key2736, -1), (key2647, -1), (key2668, -1), (key2613, -1), (key2973, 2), (key2703, 2), (key2629, 2), (key2949, -1), (key2937, -1), (key2736, -1), (key2647, -1), (key2668, -1), (key2613, -1)]

def rawRow14442 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2613, 2), (key2637, 2), (key2668, 2), (key2791, 2), (key2723, 2), (key2826, 2), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1)]

def rawRow14443 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2637, 2), (key2613, 2), (key2791, 2), (key2668, 2), (key2826, 2), (key2723, 2), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1)]

def rawRow14444 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2668, 2), (key2723, 2), (key2613, 2), (key2826, 2), (key2637, 2), (key2791, 2), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1)]

def rawRow14445 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2723, 2), (key2668, 2), (key2826, 2), (key2613, 2), (key2791, 2), (key2637, 2), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1)]

def rawRow14446 : Integer.Sparse Key := [(key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2791, 2), (key2826, 2), (key2637, 2), (key2723, 2), (key2613, 2), (key2668, 2), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1)]

def rawRow14447 : Integer.Sparse Key := [(key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2826, 2), (key2791, 2), (key2723, 2), (key2637, 2), (key2668, 2), (key2613, 2), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1)]

def rawRow14448 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1)]

def rawRow14449 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1)]

def rawRow14450 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1)]

def rawRow14451 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2613, 2), (key2637, 2), (key2668, 2), (key2791, 2), (key2723, 2), (key2826, 2), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1)]

def rawRow14452 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2637, 2), (key2613, 2), (key2791, 2), (key2668, 2), (key2826, 2), (key2723, 2), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1)]

def rawRow14453 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2668, 2), (key2723, 2), (key2613, 2), (key2826, 2), (key2637, 2), (key2791, 2), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1)]

def rawRow14454 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2723, 2), (key2668, 2), (key2826, 2), (key2613, 2), (key2791, 2), (key2637, 2), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1)]

def rawRow14455 : Integer.Sparse Key := [(key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2791, 2), (key2826, 2), (key2637, 2), (key2723, 2), (key2613, 2), (key2668, 2), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1)]

def rawRow14456 : Integer.Sparse Key := [(key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2826, 2), (key2791, 2), (key2723, 2), (key2637, 2), (key2668, 2), (key2613, 2), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1)]

def rawRow14457 : Integer.Sparse Key := [(key2678, 4), (key2812, 4), (key2816, 4), (key2678, -4), (key2687, -4), (key2816, -4), (key2709, -4), (key2713, -4), (key2862, -4), (key2713, 12)]

def rawRow14458 : Integer.Sparse Key := [(key2678, 4), (key2816, 4), (key2812, 4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2709, -4), (key2862, -4), (key2713, 12)]

def rawRow14459 : Integer.Sparse Key := [(key2812, 4), (key2678, 4), (key2816, 4), (key2678, -4), (key2816, -4), (key2687, -4), (key2709, -4), (key2862, -4), (key2713, -4), (key2713, 12)]

def rawRow14460 : Integer.Sparse Key := [(key2812, 4), (key2816, 4), (key2678, 4), (key2816, -4), (key2678, -4), (key2687, -4), (key2862, -4), (key2709, -4), (key2713, -4), (key2713, 12)]

def rawRow14461 : Integer.Sparse Key := [(key2816, 4), (key2678, 4), (key2812, 4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2862, -4), (key2709, -4), (key2713, 12)]

def rawRow14462 : Integer.Sparse Key := [(key2816, 4), (key2812, 4), (key2678, 4), (key2816, -4), (key2687, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2709, -4), (key2713, 12)]

def rawRow14463 : Integer.Sparse Key := [(key2687, 4), (key2816, 4), (key2816, 4), (key2678, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2713, -4), (key2862, -4), (key2709, 12)]

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

def rawRow14464 : Integer.Sparse Key := [(key2816, 4), (key2687, 4), (key2816, 4), (key2678, -4), (key2812, -4), (key2678, -4), (key2713, -4), (key2862, -4), (key2713, -4), (key2709, 12)]

def rawRow14465 : Integer.Sparse Key := [(key2816, 4), (key2816, 4), (key2687, 4), (key2812, -4), (key2678, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2713, -4), (key2709, 12)]

def rawRow14466 : Integer.Sparse Key := [(key2678, 4), (key2812, 4), (key2816, 4), (key2709, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2687, -4), (key2816, -4), (key2713, 12)]

def rawRow14467 : Integer.Sparse Key := [(key2678, 4), (key2816, 4), (key2812, 4), (key2713, -4), (key2709, -4), (key2862, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, 12)]

def rawRow14468 : Integer.Sparse Key := [(key2812, 4), (key2678, 4), (key2816, 4), (key2709, -4), (key2862, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2713, 12)]

def rawRow14469 : Integer.Sparse Key := [(key2812, 4), (key2816, 4), (key2678, 4), (key2862, -4), (key2709, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2713, 12)]

def rawRow14470 : Integer.Sparse Key := [(key2816, 4), (key2678, 4), (key2812, 4), (key2713, -4), (key2862, -4), (key2709, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, 12)]

def rawRow14471 : Integer.Sparse Key := [(key2816, 4), (key2812, 4), (key2678, 4), (key2862, -4), (key2713, -4), (key2709, -4), (key2816, -4), (key2687, -4), (key2678, -4), (key2713, 12)]

def rawRow14472 : Integer.Sparse Key := [(key2709, 4), (key2812, 4), (key2862, 4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2687, 12)]

def rawRow14473 : Integer.Sparse Key := [(key2709, 4), (key2862, 4), (key2812, 4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2687, 12)]

def rawRow14474 : Integer.Sparse Key := [(key2812, 4), (key2709, 4), (key2862, 4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2687, 12)]

def rawRow14475 : Integer.Sparse Key := [(key2812, 4), (key2862, 4), (key2709, 4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2687, 12)]

def rawRow14476 : Integer.Sparse Key := [(key2862, 4), (key2709, 4), (key2812, 4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2687, 12)]

def rawRow14477 : Integer.Sparse Key := [(key2862, 4), (key2812, 4), (key2709, 4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2687, 12)]

def rawRow14478 : Integer.Sparse Key := [(key2713, 4), (key2816, 4), (key2862, 4), (key2678, -4), (key2709, -4), (key2812, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, 12)]

def rawRow14479 : Integer.Sparse Key := [(key2713, 4), (key2862, 4), (key2816, 4), (key2709, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2687, -4), (key2816, -4), (key2678, 12)]

def rawRow14480 : Integer.Sparse Key := [(key2816, 4), (key2713, 4), (key2862, 4), (key2678, -4), (key2812, -4), (key2709, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, 12)]

def rawRow14481 : Integer.Sparse Key := [(key2816, 4), (key2862, 4), (key2713, 4), (key2812, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2687, -4), (key2713, -4), (key2678, 12)]

def rawRow14482 : Integer.Sparse Key := [(key2862, 4), (key2713, 4), (key2816, 4), (key2709, -4), (key2812, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2678, 12)]

def rawRow14483 : Integer.Sparse Key := [(key2862, 4), (key2816, 4), (key2713, 4), (key2812, -4), (key2709, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2678, 12)]

def rawRow14484 : Integer.Sparse Key := [(key2687, 4), (key2816, 4), (key2816, 4), (key2713, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2678, -4), (key2812, -4), (key2709, 12)]

def rawRow14485 : Integer.Sparse Key := [(key2816, 4), (key2687, 4), (key2816, 4), (key2713, -4), (key2862, -4), (key2713, -4), (key2678, -4), (key2812, -4), (key2678, -4), (key2709, 12)]

def rawRow14486 : Integer.Sparse Key := [(key2816, 4), (key2816, 4), (key2687, 4), (key2862, -4), (key2713, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2678, -4), (key2709, 12)]

def rawRow14487 : Integer.Sparse Key := [(key2713, 4), (key2816, 4), (key2862, 4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2709, -4), (key2812, -4), (key2678, 12)]

def rawRow14488 : Integer.Sparse Key := [(key2713, 4), (key2862, 4), (key2816, 4), (key2713, -4), (key2687, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2812, -4), (key2678, 12)]

def rawRow14489 : Integer.Sparse Key := [(key2816, 4), (key2713, 4), (key2862, 4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2812, -4), (key2709, -4), (key2678, 12)]

def rawRow14490 : Integer.Sparse Key := [(key2816, 4), (key2862, 4), (key2713, 4), (key2816, -4), (key2687, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2709, -4), (key2678, 12)]

def rawRow14491 : Integer.Sparse Key := [(key2862, 4), (key2713, 4), (key2816, 4), (key2713, -4), (key2816, -4), (key2687, -4), (key2709, -4), (key2812, -4), (key2678, -4), (key2678, 12)]

def rawRow14492 : Integer.Sparse Key := [(key2862, 4), (key2816, 4), (key2713, 4), (key2816, -4), (key2713, -4), (key2687, -4), (key2812, -4), (key2709, -4), (key2678, -4), (key2678, 12)]

def rawRow14493 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2401, 6), (key2839, -2), (key2842, -2), (key2965, -2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2586, -2), (key2842, -2), (key2874, -2), (key2886, 6), (key2597, -2), (key2886, -2), (key2908, -2)]

def rawRow14494 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2433, -2), (key2401, 6), (key2842, -2), (key2839, -2), (key2965, -2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2586, -2), (key2874, -2), (key2842, -2), (key2886, 6), (key2597, -2), (key2908, -2), (key2886, -2)]

def rawRow14495 : Integer.Sparse Key := [(key2398, -2), (key2433, -2), (key2401, -2), (key2401, 6), (key2839, -2), (key2965, -2), (key2842, -2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2842, -2), (key2586, -2), (key2874, -2), (key2886, 6), (key2886, -2), (key2597, -2), (key2908, -2)]

def rawRow14496 : Integer.Sparse Key := [(key2433, -2), (key2398, -2), (key2401, -2), (key2401, 6), (key2965, -2), (key2839, -2), (key2842, -2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2842, -2), (key2874, -2), (key2586, -2), (key2886, 6), (key2886, -2), (key2908, -2), (key2597, -2)]

def rawRow14497 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2398, -2), (key2401, 6), (key2842, -2), (key2965, -2), (key2839, -2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2874, -2), (key2586, -2), (key2842, -2), (key2886, 6), (key2908, -2), (key2597, -2), (key2886, -2)]

def rawRow14498 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2398, -2), (key2401, 6), (key2965, -2), (key2842, -2), (key2839, -2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2874, -2), (key2842, -2), (key2586, -2), (key2886, 6), (key2908, -2), (key2886, -2), (key2597, -2)]

def rawRow14499 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2433, -2), (key2398, 6), (key2874, -2), (key2874, -2), (key2987, -2), (key2586, 2), (key2586, 2), (key2842, 2), (key2842, 2), (key2965, 2), (key2965, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2908, 6), (key2597, -2), (key2886, -2), (key2886, -2)]

def rawRow14500 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2401, -2), (key2398, 6), (key2874, -2), (key2987, -2), (key2874, -2), (key2842, 2), (key2965, 2), (key2586, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2908, 6), (key2886, -2), (key2597, -2), (key2886, -2)]

def rawRow14501 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2401, -2), (key2398, 6), (key2987, -2), (key2874, -2), (key2874, -2), (key2965, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2586, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2908, 6), (key2886, -2), (key2886, -2), (key2597, -2)]

def rawRow14502 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2499, -2), (key2476, 6), (key2398, -2), (key2401, -2), (key2433, -2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2597, -2), (key2886, -2), (key2908, -2), (key2765, 6), (key2586, -2), (key2842, -2), (key2874, -2)]

def rawRow14503 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2499, -2), (key2476, 6), (key2401, -2), (key2398, -2), (key2433, -2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2597, -2), (key2908, -2), (key2886, -2), (key2765, 6), (key2586, -2), (key2874, -2), (key2842, -2)]

def rawRow14504 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2467, -2), (key2476, 6), (key2398, -2), (key2433, -2), (key2401, -2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2886, -2), (key2597, -2), (key2908, -2), (key2765, 6), (key2842, -2), (key2586, -2), (key2874, -2)]

def rawRow14505 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2433, -2), (key2398, -2), (key2401, -2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2886, -2), (key2908, -2), (key2597, -2), (key2765, 6), (key2842, -2), (key2874, -2), (key2586, -2)]

def rawRow14506 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2464, -2), (key2476, 6), (key2401, -2), (key2433, -2), (key2398, -2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2908, -2), (key2597, -2), (key2886, -2), (key2765, 6), (key2874, -2), (key2586, -2), (key2842, -2)]

def rawRow14507 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2464, -2), (key2476, 6), (key2433, -2), (key2401, -2), (key2398, -2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2908, -2), (key2886, -2), (key2597, -2), (key2765, 6), (key2874, -2), (key2842, -2), (key2586, -2)]

def rawRow14508 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2499, -2), (key2467, 6), (key2464, -2), (key2476, -2), (key2499, -2), (key2370, 2), (key2386, 2), (key2762, 2), (key2908, 2), (key2928, 2), (key2987, 2), (key2586, -2), (key2765, -2), (key2874, -2), (key2842, 6), (key2586, -2), (key2765, -2), (key2874, -2)]

def rawRow14509 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2499, -2), (key2467, 6), (key2476, -2), (key2464, -2), (key2499, -2), (key2386, 2), (key2370, 2), (key2908, 2), (key2762, 2), (key2987, 2), (key2928, 2), (key2586, -2), (key2874, -2), (key2765, -2), (key2842, 6), (key2586, -2), (key2874, -2), (key2765, -2)]

def rawRow14510 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2476, -2), (key2467, 6), (key2464, -2), (key2499, -2), (key2476, -2), (key2398, 2), (key2433, 2), (key2583, 2), (key2987, 2), (key2597, 2), (key2908, 2), (key2765, -2), (key2586, -2), (key2874, -2), (key2842, 6), (key2765, -2), (key2586, -2), (key2874, -2)]

def rawRow14511 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2476, -2), (key2467, 6), (key2499, -2), (key2464, -2), (key2476, -2), (key2433, 2), (key2398, 2), (key2987, 2), (key2583, 2), (key2908, 2), (key2597, 2), (key2765, -2), (key2874, -2), (key2586, -2), (key2842, 6), (key2765, -2), (key2874, -2), (key2586, -2)]

def rawRow14512 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2464, -2), (key2467, 6), (key2476, -2), (key2499, -2), (key2464, -2), (key2540, 2), (key2551, 2), (key2386, 2), (key2433, 2), (key2370, 2), (key2762, 2), (key2874, -2), (key2586, -2), (key2765, -2), (key2842, 6), (key2874, -2), (key2586, -2), (key2765, -2)]

def rawRow14513 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2464, -2), (key2467, 6), (key2499, -2), (key2476, -2), (key2464, -2), (key2551, 2), (key2540, 2), (key2433, 2), (key2386, 2), (key2398, 2), (key2583, 2), (key2874, -2), (key2765, -2), (key2586, -2), (key2842, 6), (key2874, -2), (key2765, -2), (key2586, -2)]

def rawRow14514 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2499, -2), (key2464, 6), (key2534, -2), (key2540, -2), (key2551, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2874, 6), (key2586, -2), (key2765, -2), (key2842, -2)]

def rawRow14515 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2499, -2), (key2464, 6), (key2540, -2), (key2534, -2), (key2551, -2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2874, 6), (key2586, -2), (key2842, -2), (key2765, -2)]

def rawRow14516 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2476, -2), (key2464, 6), (key2534, -2), (key2551, -2), (key2540, -2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2874, 6), (key2765, -2), (key2586, -2), (key2842, -2)]

def rawRow14517 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2476, -2), (key2464, 6), (key2551, -2), (key2534, -2), (key2540, -2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2874, 6), (key2765, -2), (key2842, -2), (key2586, -2)]

def rawRow14518 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2467, -2), (key2464, 6), (key2540, -2), (key2551, -2), (key2534, -2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2874, 6), (key2842, -2), (key2586, -2), (key2765, -2)]

def rawRow14519 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2467, -2), (key2464, 6), (key2551, -2), (key2540, -2), (key2534, -2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2874, 6), (key2842, -2), (key2765, -2), (key2586, -2)]

def rawRow14520 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2551, -2), (key2540, 6), (key2401, -2), (key2401, -2), (key2433, -2), (key2373, 2), (key2373, 2), (key2467, 2), (key2467, 2), (key2499, 2), (key2499, 2), (key2386, -2), (key2476, -2), (key2476, -2), (key2398, 6), (key2583, -2), (key2839, -2), (key2839, -2)]

def rawRow14521 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2534, -2), (key2540, 6), (key2401, -2), (key2433, -2), (key2401, -2), (key2467, 2), (key2499, 2), (key2373, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2476, -2), (key2386, -2), (key2476, -2), (key2398, 6), (key2839, -2), (key2583, -2), (key2839, -2)]

def rawRow14522 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2534, -2), (key2540, 6), (key2433, -2), (key2401, -2), (key2401, -2), (key2499, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2373, 2), (key2476, -2), (key2476, -2), (key2386, -2), (key2398, 6), (key2839, -2), (key2839, -2), (key2583, -2)]

def rawRow14523 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2551, -2), (key2534, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2373, -2), (key2401, -2), (key2467, -2), (key2464, 6), (key2370, -2), (key2762, -2), (key2839, -2)]

def rawRow14524 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2551, -2), (key2534, 6), (key2476, -2), (key2467, -2), (key2499, -2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2373, -2), (key2467, -2), (key2401, -2), (key2464, 6), (key2370, -2), (key2839, -2), (key2762, -2)]

def rawRow14525 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2540, -2), (key2534, 6), (key2467, -2), (key2499, -2), (key2476, -2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2401, -2), (key2373, -2), (key2467, -2), (key2464, 6), (key2398, -2), (key2583, -2), (key2839, -2)]

def rawRow14526 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2540, -2), (key2534, 6), (key2499, -2), (key2467, -2), (key2476, -2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2401, -2), (key2467, -2), (key2373, -2), (key2464, 6), (key2398, -2), (key2839, -2), (key2583, -2)]

def rawRow14527 : Integer.Sparse Key := [(key2540, -2), (key2551, -2), (key2534, -2), (key2534, 6), (key2476, -2), (key2499, -2), (key2467, -2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2467, -2), (key2373, -2), (key2401, -2), (key2464, 6), (key2464, -2), (key2370, -2), (key2762, -2)]

def rawRow14528 : Integer.Sparse Key := [(key2551, -2), (key2540, -2), (key2534, -2), (key2534, 6), (key2499, -2), (key2476, -2), (key2467, -2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2467, -2), (key2401, -2), (key2373, -2), (key2464, 6), (key2464, -2), (key2398, -2), (key2583, -2)]

def rawRow14529 : Integer.Sparse Key := [(key2011, 4), (key2125, 4), (key2135, 4), (key2011, -4), (key2020, -4), (key2135, -4), (key2040, -4), (key2048, -4), (key2220, -4), (key2048, 12)]

def rawRow14530 : Integer.Sparse Key := [(key2011, 4), (key2135, 4), (key2125, 4), (key2020, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2040, -4), (key2220, -4), (key2048, 12)]

def rawRow14531 : Integer.Sparse Key := [(key2125, 4), (key2011, 4), (key2135, 4), (key2011, -4), (key2135, -4), (key2020, -4), (key2040, -4), (key2220, -4), (key2048, -4), (key2048, 12)]

def rawRow14532 : Integer.Sparse Key := [(key2125, 4), (key2135, 4), (key2011, 4), (key2135, -4), (key2011, -4), (key2020, -4), (key2220, -4), (key2040, -4), (key2048, -4), (key2048, 12)]

def rawRow14533 : Integer.Sparse Key := [(key2135, 4), (key2011, 4), (key2125, 4), (key2020, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2220, -4), (key2040, -4), (key2048, 12)]

def rawRow14534 : Integer.Sparse Key := [(key2135, 4), (key2125, 4), (key2011, 4), (key2135, -4), (key2020, -4), (key2011, -4), (key2220, -4), (key2048, -4), (key2040, -4), (key2048, 12)]

def rawRow14535 : Integer.Sparse Key := [(key2020, 4), (key2135, 4), (key2135, 4), (key2011, -4), (key2011, -4), (key2125, -4), (key2048, -4), (key2048, -4), (key2220, -4), (key2040, 12)]

def rawRow14536 : Integer.Sparse Key := [(key2135, 4), (key2020, 4), (key2135, 4), (key2011, -4), (key2125, -4), (key2011, -4), (key2048, -4), (key2220, -4), (key2048, -4), (key2040, 12)]

def rawRow14537 : Integer.Sparse Key := [(key2135, 4), (key2135, 4), (key2020, 4), (key2125, -4), (key2011, -4), (key2011, -4), (key2220, -4), (key2048, -4), (key2048, -4), (key2040, 12)]

def rawRow14538 : Integer.Sparse Key := [(key2011, 4), (key2125, 4), (key2135, 4), (key2040, -4), (key2048, -4), (key2220, -4), (key2011, -4), (key2020, -4), (key2135, -4), (key2048, 12)]

def rawRow14539 : Integer.Sparse Key := [(key2011, 4), (key2135, 4), (key2125, 4), (key2048, -4), (key2040, -4), (key2220, -4), (key2020, -4), (key2011, -4), (key2135, -4), (key2048, 12)]

def rawRow14540 : Integer.Sparse Key := [(key2125, 4), (key2011, 4), (key2135, 4), (key2040, -4), (key2220, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2020, -4), (key2048, 12)]

def rawRow14541 : Integer.Sparse Key := [(key2125, 4), (key2135, 4), (key2011, 4), (key2220, -4), (key2040, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2020, -4), (key2048, 12)]

def rawRow14542 : Integer.Sparse Key := [(key2135, 4), (key2011, 4), (key2125, 4), (key2048, -4), (key2220, -4), (key2040, -4), (key2020, -4), (key2135, -4), (key2011, -4), (key2048, 12)]

def rawRow14543 : Integer.Sparse Key := [(key2135, 4), (key2125, 4), (key2011, 4), (key2220, -4), (key2048, -4), (key2040, -4), (key2135, -4), (key2020, -4), (key2011, -4), (key2048, 12)]

def rawRow14544 : Integer.Sparse Key := [(key2040, 4), (key2125, 4), (key2220, 4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2020, 12)]

def rawRow14545 : Integer.Sparse Key := [(key2040, 4), (key2220, 4), (key2125, 4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2020, 12)]

def rawRow14546 : Integer.Sparse Key := [(key2125, 4), (key2040, 4), (key2220, 4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2020, 12)]

def rawRow14547 : Integer.Sparse Key := [(key2125, 4), (key2220, 4), (key2040, 4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2020, 12)]

def rawRow14548 : Integer.Sparse Key := [(key2220, 4), (key2040, 4), (key2125, 4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2020, 12)]

def rawRow14549 : Integer.Sparse Key := [(key2220, 4), (key2125, 4), (key2040, 4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2020, 12)]

def rawRow14550 : Integer.Sparse Key := [(key2048, 4), (key2135, 4), (key2220, 4), (key2011, -4), (key2040, -4), (key2125, -4), (key2020, -4), (key2048, -4), (key2135, -4), (key2011, 12)]

def rawRow14551 : Integer.Sparse Key := [(key2048, 4), (key2220, 4), (key2135, 4), (key2040, -4), (key2011, -4), (key2125, -4), (key2048, -4), (key2020, -4), (key2135, -4), (key2011, 12)]

def rawRow14552 : Integer.Sparse Key := [(key2135, 4), (key2048, 4), (key2220, 4), (key2011, -4), (key2125, -4), (key2040, -4), (key2020, -4), (key2135, -4), (key2048, -4), (key2011, 12)]

def rawRow14553 : Integer.Sparse Key := [(key2135, 4), (key2220, 4), (key2048, 4), (key2125, -4), (key2011, -4), (key2040, -4), (key2135, -4), (key2020, -4), (key2048, -4), (key2011, 12)]

def rawRow14554 : Integer.Sparse Key := [(key2220, 4), (key2048, 4), (key2135, 4), (key2040, -4), (key2125, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2020, -4), (key2011, 12)]

def rawRow14555 : Integer.Sparse Key := [(key2220, 4), (key2135, 4), (key2048, 4), (key2125, -4), (key2040, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2020, -4), (key2011, 12)]

def rawRow14556 : Integer.Sparse Key := [(key2020, 4), (key2135, 4), (key2135, 4), (key2048, -4), (key2048, -4), (key2220, -4), (key2011, -4), (key2011, -4), (key2125, -4), (key2040, 12)]

def rawRow14557 : Integer.Sparse Key := [(key2135, 4), (key2020, 4), (key2135, 4), (key2048, -4), (key2220, -4), (key2048, -4), (key2011, -4), (key2125, -4), (key2011, -4), (key2040, 12)]

def rawRow14558 : Integer.Sparse Key := [(key2135, 4), (key2135, 4), (key2020, 4), (key2220, -4), (key2048, -4), (key2048, -4), (key2125, -4), (key2011, -4), (key2011, -4), (key2040, 12)]

def rawRow14559 : Integer.Sparse Key := [(key2048, 4), (key2135, 4), (key2220, 4), (key2020, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2040, -4), (key2125, -4), (key2011, 12)]

def rawRow14560 : Integer.Sparse Key := [(key2048, 4), (key2220, 4), (key2135, 4), (key2048, -4), (key2020, -4), (key2135, -4), (key2040, -4), (key2011, -4), (key2125, -4), (key2011, 12)]

def rawRow14561 : Integer.Sparse Key := [(key2135, 4), (key2048, 4), (key2220, 4), (key2020, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2125, -4), (key2040, -4), (key2011, 12)]

def rawRow14562 : Integer.Sparse Key := [(key2135, 4), (key2220, 4), (key2048, 4), (key2135, -4), (key2020, -4), (key2048, -4), (key2125, -4), (key2011, -4), (key2040, -4), (key2011, 12)]

def rawRow14563 : Integer.Sparse Key := [(key2220, 4), (key2048, 4), (key2135, 4), (key2048, -4), (key2135, -4), (key2020, -4), (key2040, -4), (key2125, -4), (key2011, -4), (key2011, 12)]

def rawRow14564 : Integer.Sparse Key := [(key2220, 4), (key2135, 4), (key2048, 4), (key2135, -4), (key2048, -4), (key2020, -4), (key2125, -4), (key2040, -4), (key2011, -4), (key2011, 12)]

def rawRow14565 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2624, -1), (key2627, -1), (key2851, -1), (key2866, -1), (key2971, -1), (key2981, -1), (key2624, 2), (key2636, 2), (key2698, 2), (key2722, 2), (key2974, 2), (key2981, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1), (key2645, 2), (key2892, 2), (key2902, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1)]

def rawRow14566 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2627, -1), (key2624, -1), (key2866, -1), (key2851, -1), (key2981, -1), (key2971, -1), (key2636, 2), (key2624, 2), (key2722, 2), (key2698, 2), (key2981, 2), (key2974, 2), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1), (key2645, 2), (key2902, 2), (key2892, 2), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1)]

def rawRow14567 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2851, -1), (key2971, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2698, 2), (key2974, 2), (key2624, 2), (key2981, 2), (key2636, 2), (key2722, 2), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2892, 2), (key2645, 2), (key2902, 2), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1)]

def rawRow14568 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2971, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2866, -1), (key2627, -1), (key2974, 2), (key2698, 2), (key2981, 2), (key2624, 2), (key2722, 2), (key2636, 2), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1), (key2892, 2), (key2902, 2), (key2645, 2), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1)]

def rawRow14569 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2866, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2624, -1), (key2851, -1), (key2722, 2), (key2981, 2), (key2636, 2), (key2974, 2), (key2624, 2), (key2698, 2), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1), (key2902, 2), (key2645, 2), (key2892, 2), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1)]

def rawRow14570 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2981, -1), (key2866, -1), (key2971, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2981, 2), (key2722, 2), (key2974, 2), (key2636, 2), (key2698, 2), (key2624, 2), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2902, 2), (key2892, 2), (key2645, 2), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1)]

def rawRow14571 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2636, -1), (key2636, -1), (key2856, -1), (key2856, -1), (key2974, -1), (key2974, -1), (key2627, 2), (key2627, 2), (key2701, 2), (key2701, 2), (key2971, 2), (key2971, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2645, -1), (key2645, -1), (key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1)]

def rawRow14572 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2856, -1), (key2974, -1), (key2636, -1), (key2974, -1), (key2636, -1), (key2856, -1), (key2701, 2), (key2971, 2), (key2627, 2), (key2971, 2), (key2627, 2), (key2701, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2734, -1), (key2892, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2734, -1)]

def rawRow14573 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2974, -1), (key2856, -1), (key2974, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2971, 2), (key2701, 2), (key2971, 2), (key2627, 2), (key2701, 2), (key2627, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2892, -1), (key2734, -1), (key2892, -1), (key2645, -1), (key2734, -1), (key2645, -1)]

def rawRow14574 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2636, 2), (key2856, 2), (key2974, 2), (key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2624, 2), (key2636, 2), (key2698, 2), (key2722, 2), (key2974, 2), (key2981, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1)]

def rawRow14575 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2636, 2), (key2974, 2), (key2856, 2), (key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2636, 2), (key2624, 2), (key2722, 2), (key2698, 2), (key2981, 2), (key2974, 2), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1)]

def rawRow14576 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2856, 2), (key2636, 2), (key2974, 2), (key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2698, 2), (key2974, 2), (key2624, 2), (key2981, 2), (key2636, 2), (key2722, 2), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1)]

def rawRow14577 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2856, 2), (key2974, 2), (key2636, 2), (key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2974, 2), (key2698, 2), (key2981, 2), (key2624, 2), (key2722, 2), (key2636, 2), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1)]

def rawRow14578 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2974, 2), (key2636, 2), (key2856, 2), (key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2722, 2), (key2981, 2), (key2636, 2), (key2974, 2), (key2624, 2), (key2698, 2), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1)]

def rawRow14579 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2974, 2), (key2856, 2), (key2636, 2), (key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2981, 2), (key2722, 2), (key2974, 2), (key2636, 2), (key2698, 2), (key2624, 2), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1)]

def rawRow14580 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2698, -1), (key2974, -1), (key2722, -1), (key2981, -1), (key2627, 2), (key2701, 2), (key2971, 2), (key2624, -1), (key2636, -1), (key2698, -1), (key2974, -1), (key2722, -1), (key2981, -1), (key2608, 2), (key2651, 2), (key2663, 2), (key2745, 2), (key2941, 2), (key2958, 2), (key2611, -1), (key2636, -1), (key2666, -1), (key2722, -1), (key2790, -1), (key2825, -1), (key2627, 2), (key2781, 2), (key2866, 2), (key2611, -1), (key2636, -1), (key2666, -1), (key2722, -1), (key2790, -1), (key2825, -1)]

def rawRow14581 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2974, -1), (key2698, -1), (key2981, -1), (key2722, -1), (key2627, 2), (key2971, 2), (key2701, 2), (key2636, -1), (key2624, -1), (key2974, -1), (key2698, -1), (key2981, -1), (key2722, -1), (key2651, 2), (key2608, 2), (key2745, 2), (key2663, 2), (key2958, 2), (key2941, 2), (key2636, -1), (key2611, -1), (key2722, -1), (key2666, -1), (key2825, -1), (key2790, -1), (key2627, 2), (key2866, 2), (key2781, 2), (key2636, -1), (key2611, -1), (key2722, -1), (key2666, -1), (key2825, -1), (key2790, -1)]

def rawRow14582 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2624, -1), (key2981, -1), (key2636, -1), (key2974, -1), (key2701, 2), (key2627, 2), (key2971, 2), (key2698, -1), (key2722, -1), (key2624, -1), (key2981, -1), (key2636, -1), (key2974, -1), (key2663, 2), (key2745, 2), (key2608, 2), (key2958, 2), (key2651, 2), (key2745, 2), (key2666, -1), (key2790, -1), (key2611, -1), (key2825, -1), (key2636, -1), (key2722, -1), (key2781, 2), (key2627, 2), (key2866, 2), (key2666, -1), (key2790, -1), (key2611, -1), (key2825, -1), (key2636, -1), (key2722, -1)]

def rawRow14583 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2981, -1), (key2624, -1), (key2974, -1), (key2636, -1), (key2701, 2), (key2971, 2), (key2627, 2), (key2722, -1), (key2698, -1), (key2981, -1), (key2624, -1), (key2974, -1), (key2636, -1), (key2745, 2), (key2663, 2), (key2958, 2), (key2608, 2), (key2745, 2), (key2651, 2), (key2790, -1), (key2666, -1), (key2825, -1), (key2611, -1), (key2722, -1), (key2636, -1), (key2781, 2), (key2866, 2), (key2627, 2), (key2790, -1), (key2666, -1), (key2825, -1), (key2611, -1), (key2722, -1), (key2636, -1)]

def rawRow14584 : Integer.Sparse Key := [(key2974, -1), (key2981, -1), (key2636, -1), (key2722, -1), (key2624, -1), (key2698, -1), (key2971, 2), (key2627, 2), (key2701, 2), (key2974, -1), (key2981, -1), (key2636, -1), (key2722, -1), (key2624, -1), (key2698, -1), (key2941, 2), (key2958, 2), (key2651, 2), (key2745, 2), (key2608, 2), (key2663, 2), (key2722, -1), (key2825, -1), (key2636, -1), (key2790, -1), (key2611, -1), (key2666, -1), (key2866, 2), (key2627, 2), (key2781, 2), (key2722, -1), (key2825, -1), (key2636, -1), (key2790, -1), (key2611, -1), (key2666, -1)]

def rawRow14585 : Integer.Sparse Key := [(key2981, -1), (key2974, -1), (key2722, -1), (key2636, -1), (key2698, -1), (key2624, -1), (key2971, 2), (key2701, 2), (key2627, 2), (key2981, -1), (key2974, -1), (key2722, -1), (key2636, -1), (key2698, -1), (key2624, -1), (key2958, 2), (key2941, 2), (key2745, 2), (key2651, 2), (key2663, 2), (key2608, 2), (key2825, -1), (key2722, -1), (key2790, -1), (key2636, -1), (key2666, -1), (key2611, -1), (key2866, 2), (key2781, 2), (key2627, 2), (key2825, -1), (key2722, -1), (key2790, -1), (key2636, -1), (key2666, -1), (key2611, -1)]

def rawRow14586 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2611, 2), (key2636, 2), (key2666, 2), (key2790, 2), (key2722, 2), (key2825, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2636, 2), (key2790, 2), (key2856, 2), (key2611, -1), (key2627, -1), (key2666, -1), (key2701, -1), (key2781, -1), (key2804, -1)]

def rawRow14587 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2636, 2), (key2611, 2), (key2790, 2), (key2666, 2), (key2825, 2), (key2722, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2636, 2), (key2856, 2), (key2790, 2), (key2627, -1), (key2611, -1), (key2701, -1), (key2666, -1), (key2804, -1), (key2781, -1)]

def rawRow14588 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2666, 2), (key2722, 2), (key2611, 2), (key2825, 2), (key2636, 2), (key2790, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2790, 2), (key2636, 2), (key2856, 2), (key2666, -1), (key2781, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2701, -1)]

def rawRow14589 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2722, 2), (key2666, 2), (key2825, 2), (key2611, 2), (key2790, 2), (key2636, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2790, 2), (key2856, 2), (key2636, 2), (key2781, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2701, -1), (key2627, -1)]

def rawRow14590 : Integer.Sparse Key := [(key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2790, 2), (key2825, 2), (key2636, 2), (key2722, 2), (key2611, 2), (key2666, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2856, 2), (key2636, 2), (key2790, 2), (key2701, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2611, -1), (key2666, -1)]

def rawRow14591 : Integer.Sparse Key := [(key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, 2), (key2790, 2), (key2722, 2), (key2636, 2), (key2666, 2), (key2611, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2856, 2), (key2790, 2), (key2636, 2), (key2804, -1), (key2701, -1), (key2781, -1), (key2627, -1), (key2666, -1), (key2611, -1)]

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

def rawRow14592 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2627, 2), (key2627, 2), (key2781, 2), (key2781, 2), (key2866, 2), (key2866, 2), (key2636, -1), (key2636, -1), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1)]

def rawRow14593 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2781, 2), (key2866, 2), (key2627, 2), (key2866, 2), (key2627, 2), (key2781, 2), (key2790, -1), (key2856, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1)]

def rawRow14594 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2866, 2), (key2781, 2), (key2866, 2), (key2627, 2), (key2781, 2), (key2627, 2), (key2856, -1), (key2790, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2636, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1)]

def rawRow14595 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2645, 2), (key2734, 2), (key2892, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2611, 2), (key2636, 2), (key2666, 2), (key2790, 2), (key2722, 2), (key2825, 2), (key2611, -1), (key2627, -1), (key2666, -1), (key2781, -1), (key2701, -1), (key2804, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1)]

def rawRow14596 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2645, 2), (key2892, 2), (key2734, 2), (key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2636, 2), (key2611, 2), (key2790, 2), (key2666, 2), (key2825, 2), (key2722, 2), (key2627, -1), (key2611, -1), (key2781, -1), (key2666, -1), (key2804, -1), (key2701, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1)]

def rawRow14597 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2734, 2), (key2645, 2), (key2892, 2), (key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2666, 2), (key2722, 2), (key2611, 2), (key2825, 2), (key2636, 2), (key2790, 2), (key2666, -1), (key2701, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1)]

def rawRow14598 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2734, 2), (key2892, 2), (key2645, 2), (key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2722, 2), (key2666, 2), (key2825, 2), (key2611, 2), (key2790, 2), (key2636, 2), (key2701, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2781, -1), (key2627, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1)]

def rawRow14599 : Integer.Sparse Key := [(key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2892, 2), (key2645, 2), (key2734, 2), (key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2790, 2), (key2825, 2), (key2636, 2), (key2722, 2), (key2611, 2), (key2666, 2), (key2781, -1), (key2804, -1), (key2627, -1), (key2701, -1), (key2611, -1), (key2666, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1)]

def rawRow14600 : Integer.Sparse Key := [(key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2892, 2), (key2734, 2), (key2645, 2), (key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2825, 2), (key2790, 2), (key2722, 2), (key2636, 2), (key2666, 2), (key2611, 2), (key2804, -1), (key2781, -1), (key2701, -1), (key2627, -1), (key2666, -1), (key2611, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1)]

def rawRow14601 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1756, 4), (key1700, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1756, -2), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow14602 : Integer.Sparse Key := [(key1700, 4), (key1756, 4), (key1700, 4), (key1706, -2), (key1700, -2), (key1756, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow14603 : Integer.Sparse Key := [(key1756, 4), (key1700, 4), (key1700, 4), (key1756, -2), (key1756, -2), (key1706, -2), (key1706, -2), (key1700, -2), (key1700, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow14604 : Integer.Sparse Key := [(key1706, 4), (key1706, 4), (key1706, 4), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow14605 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1756, 4), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1700, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1756, -2), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow14606 : Integer.Sparse Key := [(key1700, 4), (key1756, 4), (key1700, 4), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow14607 : Integer.Sparse Key := [(key1756, 4), (key1700, 4), (key1700, 4), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1756, -2), (key1756, -2), (key1706, -2), (key1706, -2), (key1700, -2), (key1700, -2), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow14608 : Integer.Sparse Key := [(key1277, 4), (key1851, 4), (key1886, 4), (key1277, -2), (key1283, -2), (key1700, -2), (key1756, -2), (key1855, -2), (key1886, -2), (key1277, -2), (key1283, -2), (key1700, -2), (key1756, -2), (key1855, -2), (key1886, -2), (key1283, 4), (key1706, 4), (key1756, 4)]

def rawRow14609 : Integer.Sparse Key := [(key1277, 4), (key1886, 4), (key1851, 4), (key1283, -2), (key1277, -2), (key1756, -2), (key1700, -2), (key1886, -2), (key1855, -2), (key1283, -2), (key1277, -2), (key1756, -2), (key1700, -2), (key1886, -2), (key1855, -2), (key1283, 4), (key1756, 4), (key1706, 4)]

def rawRow14610 : Integer.Sparse Key := [(key1851, 4), (key1277, 4), (key1886, 4), (key1700, -2), (key1855, -2), (key1277, -2), (key1886, -2), (key1283, -2), (key1756, -2), (key1700, -2), (key1855, -2), (key1277, -2), (key1886, -2), (key1283, -2), (key1756, -2), (key1706, 4), (key1283, 4), (key1756, 4)]

def rawRow14611 : Integer.Sparse Key := [(key1851, 4), (key1886, 4), (key1277, 4), (key1855, -2), (key1700, -2), (key1886, -2), (key1277, -2), (key1756, -2), (key1283, -2), (key1855, -2), (key1700, -2), (key1886, -2), (key1277, -2), (key1756, -2), (key1283, -2), (key1706, 4), (key1756, 4), (key1283, 4)]

def rawRow14612 : Integer.Sparse Key := [(key1886, 4), (key1277, 4), (key1851, 4), (key1756, -2), (key1886, -2), (key1283, -2), (key1855, -2), (key1277, -2), (key1700, -2), (key1756, -2), (key1886, -2), (key1283, -2), (key1855, -2), (key1277, -2), (key1700, -2), (key1756, 4), (key1283, 4), (key1706, 4)]

def rawRow14613 : Integer.Sparse Key := [(key1886, 4), (key1851, 4), (key1277, 4), (key1886, -2), (key1756, -2), (key1855, -2), (key1283, -2), (key1700, -2), (key1277, -2), (key1886, -2), (key1756, -2), (key1855, -2), (key1283, -2), (key1700, -2), (key1277, -2), (key1756, 4), (key1706, 4), (key1283, 4)]

def rawRow14614 : Integer.Sparse Key := [(key1283, 4), (key1855, 4), (key1855, 4), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1283, -2), (key1283, -2), (key1706, -2), (key1706, -2), (key1855, -2), (key1855, -2), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow14615 : Integer.Sparse Key := [(key1855, 4), (key1283, 4), (key1855, 4), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow14616 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1283, 4), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1855, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1283, -2), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow14617 : Integer.Sparse Key := [(key1706, 4), (key1706, 4), (key1706, 4), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow14618 : Integer.Sparse Key := [(key1283, 4), (key1855, 4), (key1855, 4), (key1283, -2), (key1283, -2), (key1706, -2), (key1706, -2), (key1855, -2), (key1855, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow14619 : Integer.Sparse Key := [(key1855, 4), (key1283, 4), (key1855, 4), (key1706, -2), (key1855, -2), (key1283, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow14620 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1283, 4), (key1855, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1283, -2), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow14621 : Integer.Sparse Key := [(key220, -2), (key225, -2), (key225, -2), (key225, 6), (key492, -2), (key497, -2), (key497, -2), (key492, 2), (key497, 2), (key492, 2), (key551, 2), (key497, 2), (key551, 2), (key497, -2), (key497, -2), (key551, -2), (key664, 6), (key664, -2), (key664, -2), (key681, -2)]

def rawRow14622 : Integer.Sparse Key := [(key225, -2), (key220, -2), (key225, -2), (key225, 6), (key497, -2), (key492, -2), (key497, -2), (key497, 2), (key492, 2), (key551, 2), (key492, 2), (key551, 2), (key497, 2), (key497, -2), (key551, -2), (key497, -2), (key664, 6), (key664, -2), (key681, -2), (key664, -2)]

def rawRow14623 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key220, -2), (key225, 6), (key497, -2), (key497, -2), (key492, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key492, 2), (key492, 2), (key551, -2), (key497, -2), (key497, -2), (key664, 6), (key681, -2), (key664, -2), (key664, -2)]

def rawRow14624 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key225, -2), (key220, 6), (key551, -2), (key551, -2), (key551, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key492, -2), (key492, -2), (key492, -2), (key681, 6), (key664, -2), (key664, -2), (key664, -2)]

def rawRow14625 : Integer.Sparse Key := [(key492, -2), (key497, -2), (key497, -2), (key664, 6), (key220, -2), (key225, -2), (key225, -2), (key492, 2), (key497, 2), (key492, 2), (key551, 2), (key497, 2), (key551, 2), (key664, -2), (key664, -2), (key681, -2), (key225, 6), (key497, -2), (key497, -2), (key551, -2)]

def rawRow14626 : Integer.Sparse Key := [(key497, -2), (key492, -2), (key497, -2), (key664, 6), (key225, -2), (key220, -2), (key225, -2), (key497, 2), (key492, 2), (key551, 2), (key492, 2), (key551, 2), (key497, 2), (key664, -2), (key681, -2), (key664, -2), (key225, 6), (key497, -2), (key551, -2), (key497, -2)]

def rawRow14627 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key492, -2), (key664, 6), (key225, -2), (key225, -2), (key220, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key492, 2), (key492, 2), (key681, -2), (key664, -2), (key664, -2), (key225, 6), (key551, -2), (key497, -2), (key497, -2)]

def rawRow14628 : Integer.Sparse Key := [(key492, -2), (key497, -2), (key664, -2), (key497, 6), (key492, -2), (key497, -2), (key664, -2), (key220, 2), (key225, 2), (key492, 2), (key551, 2), (key664, 2), (key681, 2), (key225, -2), (key497, -2), (key551, -2), (key497, 6), (key225, -2), (key497, -2), (key551, -2)]

def rawRow14629 : Integer.Sparse Key := [(key497, -2), (key492, -2), (key664, -2), (key497, 6), (key497, -2), (key492, -2), (key664, -2), (key225, 2), (key220, 2), (key551, 2), (key492, 2), (key681, 2), (key664, 2), (key225, -2), (key551, -2), (key497, -2), (key497, 6), (key225, -2), (key551, -2), (key497, -2)]

def rawRow14630 : Integer.Sparse Key := [(key492, -2), (key664, -2), (key497, -2), (key497, 6), (key492, -2), (key664, -2), (key497, -2), (key492, 2), (key664, 2), (key220, 2), (key681, 2), (key225, 2), (key551, 2), (key497, -2), (key225, -2), (key551, -2), (key497, 6), (key497, -2), (key225, -2), (key551, -2)]

def rawRow14631 : Integer.Sparse Key := [(key664, -2), (key492, -2), (key497, -2), (key497, 6), (key664, -2), (key492, -2), (key497, -2), (key664, 2), (key492, 2), (key681, 2), (key220, 2), (key551, 2), (key225, 2), (key497, -2), (key551, -2), (key225, -2), (key497, 6), (key497, -2), (key551, -2), (key225, -2)]

def rawRow14632 : Integer.Sparse Key := [(key497, -2), (key664, -2), (key492, -2), (key497, 6), (key497, -2), (key664, -2), (key492, -2), (key551, 2), (key681, 2), (key225, 2), (key664, 2), (key220, 2), (key492, 2), (key551, -2), (key225, -2), (key497, -2), (key497, 6), (key551, -2), (key225, -2), (key497, -2)]

def rawRow14633 : Integer.Sparse Key := [(key664, -2), (key497, -2), (key492, -2), (key497, 6), (key664, -2), (key497, -2), (key492, -2), (key681, 2), (key551, 2), (key664, 2), (key225, 2), (key492, 2), (key220, 2), (key551, -2), (key497, -2), (key225, -2), (key497, 6), (key551, -2), (key497, -2), (key225, -2)]

def rawRow14634 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key664, -2), (key492, 6), (key551, -2), (key551, -2), (key681, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key664, 2), (key664, 2), (key220, -2), (key492, -2), (key492, -2), (key551, 6), (key225, -2), (key497, -2), (key497, -2)]

def rawRow14635 : Integer.Sparse Key := [(key497, -2), (key664, -2), (key497, -2), (key492, 6), (key551, -2), (key681, -2), (key551, -2), (key497, 2), (key664, 2), (key225, 2), (key664, 2), (key225, 2), (key497, 2), (key492, -2), (key220, -2), (key492, -2), (key551, 6), (key497, -2), (key225, -2), (key497, -2)]

def rawRow14636 : Integer.Sparse Key := [(key664, -2), (key497, -2), (key497, -2), (key492, 6), (key681, -2), (key551, -2), (key551, -2), (key664, 2), (key497, 2), (key664, 2), (key225, 2), (key497, 2), (key225, 2), (key492, -2), (key492, -2), (key220, -2), (key551, 6), (key497, -2), (key497, -2), (key225, -2)]

def rawRow14637 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key551, -2), (key681, 6), (key225, -2), (key225, -2), (key225, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key664, -2), (key664, -2), (key664, -2), (key220, 6), (key492, -2), (key492, -2), (key492, -2)]

def rawRow14638 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key681, -2), (key551, 6), (key497, -2), (key497, -2), (key664, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key664, 2), (key664, 2), (key225, -2), (key497, -2), (key497, -2), (key492, 6), (key220, -2), (key492, -2), (key492, -2)]

def rawRow14639 : Integer.Sparse Key := [(key551, -2), (key681, -2), (key551, -2), (key551, 6), (key497, -2), (key664, -2), (key497, -2), (key497, 2), (key664, 2), (key225, 2), (key664, 2), (key225, 2), (key497, 2), (key497, -2), (key225, -2), (key497, -2), (key492, 6), (key492, -2), (key220, -2), (key492, -2)]

def rawRow14640 : Integer.Sparse Key := [(key681, -2), (key551, -2), (key551, -2), (key551, 6), (key664, -2), (key497, -2), (key497, -2), (key664, 2), (key497, 2), (key664, 2), (key225, 2), (key497, 2), (key225, 2), (key497, -2), (key497, -2), (key225, -2), (key492, 6), (key492, -2), (key492, -2), (key220, -2)]

def rawRow14641 : Integer.Sparse Key := [(key1273, -2), (key1278, -2), (key1278, -2), (key1278, 6), (key1696, -2), (key1701, -2), (key1701, -2), (key1696, 2), (key1701, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1701, -2), (key1701, -2), (key1751, -2), (key1933, 6), (key1933, -2), (key1933, -2), (key1953, -2)]

def rawRow14642 : Integer.Sparse Key := [(key1278, -2), (key1273, -2), (key1278, -2), (key1278, 6), (key1701, -2), (key1696, -2), (key1701, -2), (key1701, 2), (key1696, 2), (key1751, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1701, -2), (key1751, -2), (key1701, -2), (key1933, 6), (key1933, -2), (key1953, -2), (key1933, -2)]

def rawRow14643 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1273, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1696, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1696, 2), (key1696, 2), (key1751, -2), (key1701, -2), (key1701, -2), (key1933, 6), (key1953, -2), (key1933, -2), (key1933, -2)]

def rawRow14644 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1278, -2), (key1273, 6), (key1751, -2), (key1751, -2), (key1751, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1696, -2), (key1696, -2), (key1696, -2), (key1953, 6), (key1933, -2), (key1933, -2), (key1933, -2)]

def rawRow14645 : Integer.Sparse Key := [(key1696, -2), (key1701, -2), (key1701, -2), (key1933, 6), (key1273, -2), (key1278, -2), (key1278, -2), (key1696, 2), (key1701, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1933, -2), (key1933, -2), (key1953, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1751, -2)]

def rawRow14646 : Integer.Sparse Key := [(key1701, -2), (key1696, -2), (key1701, -2), (key1933, 6), (key1278, -2), (key1273, -2), (key1278, -2), (key1701, 2), (key1696, 2), (key1751, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1933, -2), (key1953, -2), (key1933, -2), (key1278, 6), (key1701, -2), (key1751, -2), (key1701, -2)]

def rawRow14647 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1696, -2), (key1933, 6), (key1278, -2), (key1278, -2), (key1273, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1696, 2), (key1696, 2), (key1953, -2), (key1933, -2), (key1933, -2), (key1278, 6), (key1751, -2), (key1701, -2), (key1701, -2)]

def rawRow14648 : Integer.Sparse Key := [(key1696, -2), (key1701, -2), (key1933, -2), (key1701, 6), (key1696, -2), (key1701, -2), (key1933, -2), (key1273, 2), (key1278, 2), (key1696, 2), (key1751, 2), (key1933, 2), (key1953, 2), (key1278, -2), (key1701, -2), (key1751, -2), (key1701, 6), (key1278, -2), (key1701, -2), (key1751, -2)]

def rawRow14649 : Integer.Sparse Key := [(key1701, -2), (key1696, -2), (key1933, -2), (key1701, 6), (key1701, -2), (key1696, -2), (key1933, -2), (key1278, 2), (key1273, 2), (key1751, 2), (key1696, 2), (key1953, 2), (key1933, 2), (key1278, -2), (key1751, -2), (key1701, -2), (key1701, 6), (key1278, -2), (key1751, -2), (key1701, -2)]

def rawRow14650 : Integer.Sparse Key := [(key1696, -2), (key1933, -2), (key1701, -2), (key1701, 6), (key1696, -2), (key1933, -2), (key1701, -2), (key1696, 2), (key1933, 2), (key1273, 2), (key1953, 2), (key1278, 2), (key1751, 2), (key1701, -2), (key1278, -2), (key1751, -2), (key1701, 6), (key1701, -2), (key1278, -2), (key1751, -2)]

def rawRow14651 : Integer.Sparse Key := [(key1933, -2), (key1696, -2), (key1701, -2), (key1701, 6), (key1933, -2), (key1696, -2), (key1701, -2), (key1933, 2), (key1696, 2), (key1953, 2), (key1273, 2), (key1751, 2), (key1278, 2), (key1701, -2), (key1751, -2), (key1278, -2), (key1701, 6), (key1701, -2), (key1751, -2), (key1278, -2)]

def rawRow14652 : Integer.Sparse Key := [(key1701, -2), (key1933, -2), (key1696, -2), (key1701, 6), (key1701, -2), (key1933, -2), (key1696, -2), (key1751, 2), (key1953, 2), (key1278, 2), (key1933, 2), (key1273, 2), (key1696, 2), (key1751, -2), (key1278, -2), (key1701, -2), (key1701, 6), (key1751, -2), (key1278, -2), (key1701, -2)]

def rawRow14653 : Integer.Sparse Key := [(key1933, -2), (key1701, -2), (key1696, -2), (key1701, 6), (key1933, -2), (key1701, -2), (key1696, -2), (key1953, 2), (key1751, 2), (key1933, 2), (key1278, 2), (key1696, 2), (key1273, 2), (key1751, -2), (key1701, -2), (key1278, -2), (key1701, 6), (key1751, -2), (key1701, -2), (key1278, -2)]

def rawRow14654 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1933, -2), (key1696, 6), (key1751, -2), (key1751, -2), (key1953, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1933, 2), (key1933, 2), (key1273, -2), (key1696, -2), (key1696, -2), (key1751, 6), (key1278, -2), (key1701, -2), (key1701, -2)]

def rawRow14655 : Integer.Sparse Key := [(key1701, -2), (key1933, -2), (key1701, -2), (key1696, 6), (key1751, -2), (key1953, -2), (key1751, -2), (key1701, 2), (key1933, 2), (key1278, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1696, -2), (key1273, -2), (key1696, -2), (key1751, 6), (key1701, -2), (key1278, -2), (key1701, -2)]

def rawRow14656 : Integer.Sparse Key := [(key1933, -2), (key1701, -2), (key1701, -2), (key1696, 6), (key1953, -2), (key1751, -2), (key1751, -2), (key1933, 2), (key1701, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1696, -2), (key1696, -2), (key1273, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1278, -2)]

def rawRow14657 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1751, -2), (key1953, 6), (key1278, -2), (key1278, -2), (key1278, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1933, -2), (key1933, -2), (key1933, -2), (key1273, 6), (key1696, -2), (key1696, -2), (key1696, -2)]

def rawRow14658 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1953, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1933, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1933, 2), (key1933, 2), (key1278, -2), (key1701, -2), (key1701, -2), (key1696, 6), (key1273, -2), (key1696, -2), (key1696, -2)]

def rawRow14659 : Integer.Sparse Key := [(key1751, -2), (key1953, -2), (key1751, -2), (key1751, 6), (key1701, -2), (key1933, -2), (key1701, -2), (key1701, 2), (key1933, 2), (key1278, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1701, -2), (key1278, -2), (key1701, -2), (key1696, 6), (key1696, -2), (key1273, -2), (key1696, -2)]

def rawRow14660 : Integer.Sparse Key := [(key1953, -2), (key1751, -2), (key1751, -2), (key1751, 6), (key1933, -2), (key1701, -2), (key1701, -2), (key1933, 2), (key1701, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1701, -2), (key1701, -2), (key1278, -2), (key1696, 6), (key1696, -2), (key1696, -2), (key1273, -2)]

def rawRow14661 : Integer.Sparse Key := [(key1360, 6), (key1360, -2), (key1360, -2), (key1372, -2), (key1486, 6), (key1486, -2), (key1486, -2), (key1511, -2), (key1712, -2), (key1712, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, 2), (key1721, 2), (key1712, 2), (key1739, 2), (key1721, 2), (key1739, 2)]

def rawRow14662 : Integer.Sparse Key := [(key1360, 6), (key1360, -2), (key1372, -2), (key1360, -2), (key1486, 6), (key1486, -2), (key1511, -2), (key1486, -2), (key1712, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, -2), (key1721, 2), (key1712, 2), (key1739, 2), (key1712, 2), (key1739, 2), (key1721, 2)]

def rawRow14663 : Integer.Sparse Key := [(key1360, 6), (key1372, -2), (key1360, -2), (key1360, -2), (key1486, 6), (key1511, -2), (key1486, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, -2), (key1712, -2), (key1739, 2), (key1739, 2), (key1721, 2), (key1721, 2), (key1712, 2), (key1712, 2)]

def rawRow14664 : Integer.Sparse Key := [(key1372, 6), (key1360, -2), (key1360, -2), (key1360, -2), (key1511, 6), (key1486, -2), (key1486, -2), (key1486, -2), (key1739, -2), (key1739, -2), (key1739, -2), (key1721, -2), (key1721, -2), (key1721, -2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2)]

def rawRow14665 : Integer.Sparse Key := [(key1486, 6), (key1712, -2), (key1712, -2), (key1721, -2), (key1360, 6), (key1712, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1360, -2), (key1372, -2), (key1486, -2), (key1486, -2), (key1511, -2), (key1712, 2), (key1721, 2), (key1712, 2), (key1739, 2), (key1721, 2), (key1739, 2)]

def rawRow14666 : Integer.Sparse Key := [(key1486, 6), (key1712, -2), (key1721, -2), (key1712, -2), (key1360, 6), (key1712, -2), (key1739, -2), (key1712, -2), (key1360, -2), (key1372, -2), (key1360, -2), (key1486, -2), (key1511, -2), (key1486, -2), (key1721, 2), (key1712, 2), (key1739, 2), (key1712, 2), (key1739, 2), (key1721, 2)]

def rawRow14667 : Integer.Sparse Key := [(key1486, 6), (key1721, -2), (key1712, -2), (key1712, -2), (key1360, 6), (key1739, -2), (key1712, -2), (key1712, -2), (key1372, -2), (key1360, -2), (key1360, -2), (key1511, -2), (key1486, -2), (key1486, -2), (key1739, 2), (key1739, 2), (key1721, 2), (key1721, 2), (key1712, 2), (key1712, 2)]

def rawRow14668 : Integer.Sparse Key := [(key1712, 6), (key1486, -2), (key1712, -2), (key1721, -2), (key1712, 6), (key1360, -2), (key1712, -2), (key1739, -2), (key1486, -2), (key1712, -2), (key1721, -2), (key1360, -2), (key1712, -2), (key1739, -2), (key1360, 2), (key1372, 2), (key1486, 2), (key1511, 2), (key1721, 2), (key1739, 2)]

def rawRow14669 : Integer.Sparse Key := [(key1712, 6), (key1486, -2), (key1721, -2), (key1712, -2), (key1712, 6), (key1360, -2), (key1739, -2), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1712, -2), (key1372, 2), (key1360, 2), (key1511, 2), (key1486, 2), (key1739, 2), (key1721, 2)]

def rawRow14670 : Integer.Sparse Key := [(key1712, 6), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, 6), (key1712, -2), (key1360, -2), (key1739, -2), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1486, 2), (key1721, 2), (key1360, 2), (key1739, 2), (key1372, 2), (key1511, 2)]

def rawRow14671 : Integer.Sparse Key := [(key1712, 6), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, 6), (key1712, -2), (key1739, -2), (key1360, -2), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1721, 2), (key1486, 2), (key1739, 2), (key1360, 2), (key1511, 2), (key1372, 2)]

def rawRow14672 : Integer.Sparse Key := [(key1712, 6), (key1721, -2), (key1486, -2), (key1712, -2), (key1712, 6), (key1739, -2), (key1360, -2), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1712, -2), (key1511, 2), (key1739, 2), (key1372, 2), (key1721, 2), (key1360, 2), (key1486, 2)]

def rawRow14673 : Integer.Sparse Key := [(key1712, 6), (key1721, -2), (key1712, -2), (key1486, -2), (key1712, 6), (key1739, -2), (key1712, -2), (key1360, -2), (key1721, -2), (key1712, -2), (key1486, -2), (key1739, -2), (key1712, -2), (key1360, -2), (key1739, 2), (key1511, 2), (key1721, 2), (key1372, 2), (key1486, 2), (key1360, 2)]

def rawRow14674 : Integer.Sparse Key := [(key1721, 6), (key1486, -2), (key1712, -2), (key1712, -2), (key1739, 6), (key1360, -2), (key1712, -2), (key1712, -2), (key1511, -2), (key1739, -2), (key1739, -2), (key1372, -2), (key1721, -2), (key1721, -2), (key1360, 2), (key1360, 2), (key1486, 2), (key1486, 2), (key1712, 2), (key1712, 2)]

def rawRow14675 : Integer.Sparse Key := [(key1721, 6), (key1712, -2), (key1486, -2), (key1712, -2), (key1739, 6), (key1712, -2), (key1360, -2), (key1712, -2), (key1739, -2), (key1511, -2), (key1739, -2), (key1721, -2), (key1372, -2), (key1721, -2), (key1486, 2), (key1712, 2), (key1360, 2), (key1712, 2), (key1360, 2), (key1486, 2)]

def rawRow14676 : Integer.Sparse Key := [(key1721, 6), (key1712, -2), (key1712, -2), (key1486, -2), (key1739, 6), (key1712, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1739, -2), (key1511, -2), (key1721, -2), (key1721, -2), (key1372, -2), (key1712, 2), (key1486, 2), (key1712, 2), (key1360, 2), (key1486, 2), (key1360, 2)]

def rawRow14677 : Integer.Sparse Key := [(key1511, 6), (key1739, -2), (key1739, -2), (key1739, -2), (key1372, 6), (key1721, -2), (key1721, -2), (key1721, -2), (key1360, -2), (key1360, -2), (key1360, -2), (key1486, -2), (key1486, -2), (key1486, -2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2)]

def rawRow14678 : Integer.Sparse Key := [(key1739, 6), (key1511, -2), (key1739, -2), (key1739, -2), (key1721, 6), (key1372, -2), (key1721, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, -2), (key1712, -2), (key1360, 2), (key1360, 2), (key1486, 2), (key1486, 2), (key1712, 2), (key1712, 2)]

def rawRow14679 : Integer.Sparse Key := [(key1739, 6), (key1739, -2), (key1511, -2), (key1739, -2), (key1721, 6), (key1721, -2), (key1372, -2), (key1721, -2), (key1712, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, -2), (key1486, 2), (key1712, 2), (key1360, 2), (key1712, 2), (key1360, 2), (key1486, 2)]

def rawRow14680 : Integer.Sparse Key := [(key1739, 6), (key1739, -2), (key1739, -2), (key1511, -2), (key1721, 6), (key1721, -2), (key1721, -2), (key1372, -2), (key1712, -2), (key1712, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, 2), (key1486, 2), (key1712, 2), (key1360, 2), (key1486, 2), (key1360, 2)]

def rawRow14681 : Integer.Sparse Key := [(key221, -2), (key225, -2), (key225, -2), (key225, 6), (key493, -2), (key497, -2), (key497, -2), (key493, 2), (key497, 2), (key493, 2), (key551, 2), (key497, 2), (key551, 2), (key497, -2), (key497, -2), (key551, -2), (key619, 6), (key619, -2), (key619, -2), (key645, -2)]

def rawRow14682 : Integer.Sparse Key := [(key225, -2), (key221, -2), (key225, -2), (key225, 6), (key497, -2), (key493, -2), (key497, -2), (key497, 2), (key493, 2), (key551, 2), (key493, 2), (key551, 2), (key497, 2), (key497, -2), (key551, -2), (key497, -2), (key619, 6), (key619, -2), (key645, -2), (key619, -2)]

def rawRow14683 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key221, -2), (key225, 6), (key497, -2), (key497, -2), (key493, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key493, 2), (key493, 2), (key551, -2), (key497, -2), (key497, -2), (key619, 6), (key645, -2), (key619, -2), (key619, -2)]

def rawRow14684 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key225, -2), (key221, 6), (key551, -2), (key551, -2), (key551, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key493, -2), (key493, -2), (key493, -2), (key645, 6), (key619, -2), (key619, -2), (key619, -2)]

def rawRow14685 : Integer.Sparse Key := [(key493, -2), (key497, -2), (key497, -2), (key619, 6), (key221, -2), (key225, -2), (key225, -2), (key493, 2), (key497, 2), (key493, 2), (key551, 2), (key497, 2), (key551, 2), (key619, -2), (key619, -2), (key645, -2), (key225, 6), (key497, -2), (key497, -2), (key551, -2)]

def rawRow14686 : Integer.Sparse Key := [(key497, -2), (key493, -2), (key497, -2), (key619, 6), (key225, -2), (key221, -2), (key225, -2), (key497, 2), (key493, 2), (key551, 2), (key493, 2), (key551, 2), (key497, 2), (key619, -2), (key645, -2), (key619, -2), (key225, 6), (key497, -2), (key551, -2), (key497, -2)]

def rawRow14687 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key493, -2), (key619, 6), (key225, -2), (key225, -2), (key221, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key493, 2), (key493, 2), (key645, -2), (key619, -2), (key619, -2), (key225, 6), (key551, -2), (key497, -2), (key497, -2)]

def rawRow14688 : Integer.Sparse Key := [(key493, -2), (key497, -2), (key619, -2), (key497, 6), (key493, -2), (key497, -2), (key619, -2), (key221, 2), (key225, 2), (key493, 2), (key551, 2), (key619, 2), (key645, 2), (key225, -2), (key497, -2), (key551, -2), (key497, 6), (key225, -2), (key497, -2), (key551, -2)]

def rawRow14689 : Integer.Sparse Key := [(key497, -2), (key493, -2), (key619, -2), (key497, 6), (key497, -2), (key493, -2), (key619, -2), (key225, 2), (key221, 2), (key551, 2), (key493, 2), (key645, 2), (key619, 2), (key225, -2), (key551, -2), (key497, -2), (key497, 6), (key225, -2), (key551, -2), (key497, -2)]

def rawRow14690 : Integer.Sparse Key := [(key493, -2), (key619, -2), (key497, -2), (key497, 6), (key493, -2), (key619, -2), (key497, -2), (key493, 2), (key619, 2), (key221, 2), (key645, 2), (key225, 2), (key551, 2), (key497, -2), (key225, -2), (key551, -2), (key497, 6), (key497, -2), (key225, -2), (key551, -2)]

def rawRow14691 : Integer.Sparse Key := [(key619, -2), (key493, -2), (key497, -2), (key497, 6), (key619, -2), (key493, -2), (key497, -2), (key619, 2), (key493, 2), (key645, 2), (key221, 2), (key551, 2), (key225, 2), (key497, -2), (key551, -2), (key225, -2), (key497, 6), (key497, -2), (key551, -2), (key225, -2)]

def rawRow14692 : Integer.Sparse Key := [(key497, -2), (key619, -2), (key493, -2), (key497, 6), (key497, -2), (key619, -2), (key493, -2), (key551, 2), (key645, 2), (key225, 2), (key619, 2), (key221, 2), (key493, 2), (key551, -2), (key225, -2), (key497, -2), (key497, 6), (key551, -2), (key225, -2), (key497, -2)]

def rawRow14693 : Integer.Sparse Key := [(key619, -2), (key497, -2), (key493, -2), (key497, 6), (key619, -2), (key497, -2), (key493, -2), (key645, 2), (key551, 2), (key619, 2), (key225, 2), (key493, 2), (key221, 2), (key551, -2), (key497, -2), (key225, -2), (key497, 6), (key551, -2), (key497, -2), (key225, -2)]

def rawRow14694 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key619, -2), (key493, 6), (key551, -2), (key551, -2), (key645, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key619, 2), (key619, 2), (key221, -2), (key493, -2), (key493, -2), (key551, 6), (key225, -2), (key497, -2), (key497, -2)]

def rawRow14695 : Integer.Sparse Key := [(key497, -2), (key619, -2), (key497, -2), (key493, 6), (key551, -2), (key645, -2), (key551, -2), (key497, 2), (key619, 2), (key225, 2), (key619, 2), (key225, 2), (key497, 2), (key493, -2), (key221, -2), (key493, -2), (key551, 6), (key497, -2), (key225, -2), (key497, -2)]

def rawRow14696 : Integer.Sparse Key := [(key619, -2), (key497, -2), (key497, -2), (key493, 6), (key645, -2), (key551, -2), (key551, -2), (key619, 2), (key497, 2), (key619, 2), (key225, 2), (key497, 2), (key225, 2), (key493, -2), (key493, -2), (key221, -2), (key551, 6), (key497, -2), (key497, -2), (key225, -2)]

def rawRow14697 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key551, -2), (key645, 6), (key225, -2), (key225, -2), (key225, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key619, -2), (key619, -2), (key619, -2), (key221, 6), (key493, -2), (key493, -2), (key493, -2)]

def rawRow14698 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key645, -2), (key551, 6), (key497, -2), (key497, -2), (key619, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key619, 2), (key619, 2), (key225, -2), (key497, -2), (key497, -2), (key493, 6), (key221, -2), (key493, -2), (key493, -2)]

def rawRow14699 : Integer.Sparse Key := [(key551, -2), (key645, -2), (key551, -2), (key551, 6), (key497, -2), (key619, -2), (key497, -2), (key497, 2), (key619, 2), (key225, 2), (key619, 2), (key225, 2), (key497, 2), (key497, -2), (key225, -2), (key497, -2), (key493, 6), (key493, -2), (key221, -2), (key493, -2)]

def rawRow14700 : Integer.Sparse Key := [(key645, -2), (key551, -2), (key551, -2), (key551, 6), (key619, -2), (key497, -2), (key497, -2), (key619, 2), (key497, 2), (key619, 2), (key225, 2), (key497, 2), (key225, 2), (key497, -2), (key497, -2), (key225, -2), (key493, 6), (key493, -2), (key493, -2), (key221, -2)]

def rawRow14701 : Integer.Sparse Key := [(key496, 4), (key496, 4), (key559, 4), (key496, -2), (key502, -2), (key496, -2), (key559, -2), (key502, -2), (key559, -2), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key622, 4), (key622, 4), (key648, 4)]

def rawRow14702 : Integer.Sparse Key := [(key496, 4), (key559, 4), (key496, 4), (key502, -2), (key496, -2), (key559, -2), (key496, -2), (key559, -2), (key502, -2), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key622, 4), (key648, 4), (key622, 4)]

def rawRow14703 : Integer.Sparse Key := [(key559, 4), (key496, 4), (key496, 4), (key559, -2), (key559, -2), (key502, -2), (key502, -2), (key496, -2), (key496, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key648, 4), (key622, 4), (key622, 4)]

def rawRow14704 : Integer.Sparse Key := [(key502, 4), (key502, 4), (key502, 4), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key618, 4), (key618, 4), (key618, 4)]

def rawRow14705 : Integer.Sparse Key := [(key496, 4), (key496, 4), (key559, 4), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key496, -2), (key502, -2), (key496, -2), (key559, -2), (key502, -2), (key559, -2), (key622, 4), (key622, 4), (key648, 4)]

def rawRow14706 : Integer.Sparse Key := [(key496, 4), (key559, 4), (key496, 4), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key502, -2), (key496, -2), (key559, -2), (key496, -2), (key559, -2), (key502, -2), (key622, 4), (key648, 4), (key622, 4)]

def rawRow14707 : Integer.Sparse Key := [(key559, 4), (key496, 4), (key496, 4), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key559, -2), (key559, -2), (key502, -2), (key502, -2), (key496, -2), (key496, -2), (key648, 4), (key622, 4), (key622, 4)]

def rawRow14708 : Integer.Sparse Key := [(key224, 4), (key618, 4), (key648, 4), (key224, -2), (key230, -2), (key496, -2), (key559, -2), (key622, -2), (key648, -2), (key224, -2), (key230, -2), (key496, -2), (key559, -2), (key622, -2), (key648, -2), (key230, 4), (key502, 4), (key559, 4)]

def rawRow14709 : Integer.Sparse Key := [(key224, 4), (key648, 4), (key618, 4), (key230, -2), (key224, -2), (key559, -2), (key496, -2), (key648, -2), (key622, -2), (key230, -2), (key224, -2), (key559, -2), (key496, -2), (key648, -2), (key622, -2), (key230, 4), (key559, 4), (key502, 4)]

def rawRow14710 : Integer.Sparse Key := [(key618, 4), (key224, 4), (key648, 4), (key496, -2), (key622, -2), (key224, -2), (key648, -2), (key230, -2), (key559, -2), (key496, -2), (key622, -2), (key224, -2), (key648, -2), (key230, -2), (key559, -2), (key502, 4), (key230, 4), (key559, 4)]

def rawRow14711 : Integer.Sparse Key := [(key618, 4), (key648, 4), (key224, 4), (key622, -2), (key496, -2), (key648, -2), (key224, -2), (key559, -2), (key230, -2), (key622, -2), (key496, -2), (key648, -2), (key224, -2), (key559, -2), (key230, -2), (key502, 4), (key559, 4), (key230, 4)]

def rawRow14712 : Integer.Sparse Key := [(key648, 4), (key224, 4), (key618, 4), (key559, -2), (key648, -2), (key230, -2), (key622, -2), (key224, -2), (key496, -2), (key559, -2), (key648, -2), (key230, -2), (key622, -2), (key224, -2), (key496, -2), (key559, 4), (key230, 4), (key502, 4)]

def rawRow14713 : Integer.Sparse Key := [(key648, 4), (key618, 4), (key224, 4), (key648, -2), (key559, -2), (key622, -2), (key230, -2), (key496, -2), (key224, -2), (key648, -2), (key559, -2), (key622, -2), (key230, -2), (key496, -2), (key224, -2), (key559, 4), (key502, 4), (key230, 4)]

def rawRow14714 : Integer.Sparse Key := [(key230, 4), (key622, 4), (key622, 4), (key224, -2), (key224, -2), (key496, -2), (key496, -2), (key618, -2), (key618, -2), (key230, -2), (key230, -2), (key502, -2), (key502, -2), (key622, -2), (key622, -2), (key224, 4), (key496, 4), (key496, 4)]

def rawRow14715 : Integer.Sparse Key := [(key622, 4), (key230, 4), (key622, 4), (key496, -2), (key618, -2), (key224, -2), (key618, -2), (key224, -2), (key496, -2), (key502, -2), (key622, -2), (key230, -2), (key622, -2), (key230, -2), (key502, -2), (key496, 4), (key224, 4), (key496, 4)]

def rawRow14716 : Integer.Sparse Key := [(key622, 4), (key622, 4), (key230, 4), (key618, -2), (key496, -2), (key618, -2), (key224, -2), (key496, -2), (key224, -2), (key622, -2), (key502, -2), (key622, -2), (key230, -2), (key502, -2), (key230, -2), (key496, 4), (key496, 4), (key224, 4)]

def rawRow14717 : Integer.Sparse Key := [(key502, 4), (key502, 4), (key502, 4), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key618, 4), (key618, 4), (key618, 4)]

def rawRow14718 : Integer.Sparse Key := [(key230, 4), (key622, 4), (key622, 4), (key230, -2), (key230, -2), (key502, -2), (key502, -2), (key622, -2), (key622, -2), (key224, -2), (key224, -2), (key496, -2), (key496, -2), (key618, -2), (key618, -2), (key224, 4), (key496, 4), (key496, 4)]

def rawRow14719 : Integer.Sparse Key := [(key622, 4), (key230, 4), (key622, 4), (key502, -2), (key622, -2), (key230, -2), (key622, -2), (key230, -2), (key502, -2), (key496, -2), (key618, -2), (key224, -2), (key618, -2), (key224, -2), (key496, -2), (key496, 4), (key224, 4), (key496, 4)]

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

def rawRow14720 : Integer.Sparse Key := [(key622, 4), (key622, 4), (key230, 4), (key622, -2), (key502, -2), (key622, -2), (key230, -2), (key502, -2), (key230, -2), (key618, -2), (key496, -2), (key618, -2), (key224, -2), (key496, -2), (key224, -2), (key496, 4), (key496, 4), (key224, 4)]

def rawRow14721 : Integer.Sparse Key := [(key1484, -1), (key1490, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1710, -1), (key1716, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, -1), (key1940, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1949, -1)]

def rawRow14722 : Integer.Sparse Key := [(key1490, -1), (key1484, -1), (key1513, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, -1), (key1710, -1), (key1741, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, -1), (key1937, -1), (key1949, -1), (key1937, -1), (key1949, -1), (key1940, -1)]

def rawRow14723 : Integer.Sparse Key := [(key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1484, -1), (key1484, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1710, -1), (key1710, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1), (key1949, 2), (key1937, 2), (key1937, 2), (key1949, -1), (key1949, -1), (key1940, -1), (key1940, -1), (key1937, -1), (key1937, -1)]

def rawRow14724 : Integer.Sparse Key := [(key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1484, 2), (key1484, 2), (key1484, 2), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1940, 2), (key1940, 2), (key1940, 2), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1)]

def rawRow14725 : Integer.Sparse Key := [(key1710, -1), (key1716, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1937, 2), (key1937, 2), (key1949, 2), (key1484, -1), (key1490, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, -1), (key1940, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1949, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1)]

def rawRow14726 : Integer.Sparse Key := [(key1716, -1), (key1710, -1), (key1741, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1937, 2), (key1949, 2), (key1937, 2), (key1490, -1), (key1484, -1), (key1513, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1940, -1), (key1937, -1), (key1949, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1)]

def rawRow14727 : Integer.Sparse Key := [(key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1710, -1), (key1710, -1), (key1949, 2), (key1937, 2), (key1937, 2), (key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1484, -1), (key1484, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1949, -1), (key1949, -1), (key1940, -1), (key1940, -1), (key1937, -1), (key1937, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1)]

def rawRow14728 : Integer.Sparse Key := [(key1358, -1), (key1364, -1), (key1710, -1), (key1741, -1), (key1937, -1), (key1949, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1358, -1), (key1364, -1), (key1710, -1), (key1741, -1), (key1937, -1), (key1949, -1), (key1358, 2), (key1374, 2), (key1484, 2), (key1513, 2), (key1940, 2), (key1949, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1)]

def rawRow14729 : Integer.Sparse Key := [(key1364, -1), (key1358, -1), (key1741, -1), (key1710, -1), (key1949, -1), (key1937, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, -1), (key1358, -1), (key1741, -1), (key1710, -1), (key1949, -1), (key1937, -1), (key1374, 2), (key1358, 2), (key1513, 2), (key1484, 2), (key1949, 2), (key1940, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1)]

def rawRow14730 : Integer.Sparse Key := [(key1710, -1), (key1937, -1), (key1358, -1), (key1949, -1), (key1364, -1), (key1741, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1710, -1), (key1937, -1), (key1358, -1), (key1949, -1), (key1364, -1), (key1741, -1), (key1484, 2), (key1940, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1)]

def rawRow14731 : Integer.Sparse Key := [(key1937, -1), (key1710, -1), (key1949, -1), (key1358, -1), (key1741, -1), (key1364, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1937, -1), (key1710, -1), (key1949, -1), (key1358, -1), (key1741, -1), (key1364, -1), (key1940, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1513, 2), (key1374, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1)]

def rawRow14732 : Integer.Sparse Key := [(key1741, -1), (key1949, -1), (key1364, -1), (key1937, -1), (key1358, -1), (key1710, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, -1), (key1949, -1), (key1364, -1), (key1937, -1), (key1358, -1), (key1710, -1), (key1513, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1358, 2), (key1484, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1)]

def rawRow14733 : Integer.Sparse Key := [(key1949, -1), (key1741, -1), (key1937, -1), (key1364, -1), (key1710, -1), (key1358, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1949, -1), (key1741, -1), (key1937, -1), (key1364, -1), (key1710, -1), (key1358, -1), (key1949, 2), (key1513, 2), (key1940, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1)]

def rawRow14734 : Integer.Sparse Key := [(key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1937, -1), (key1937, -1), (key1358, 2), (key1710, 2), (key1710, 2), (key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1940, -1), (key1940, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1358, -1), (key1358, -1), (key1484, -1), (key1484, -1), (key1710, -1), (key1710, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1)]

def rawRow14735 : Integer.Sparse Key := [(key1716, -1), (key1937, -1), (key1364, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1710, 2), (key1358, 2), (key1710, 2), (key1723, -1), (key1940, -1), (key1374, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1484, -1), (key1710, -1), (key1358, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1)]

def rawRow14736 : Integer.Sparse Key := [(key1937, -1), (key1716, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1710, 2), (key1710, 2), (key1358, 2), (key1940, -1), (key1723, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, -1), (key1484, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1358, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1)]

def rawRow14737 : Integer.Sparse Key := [(key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1940, 2), (key1940, 2), (key1940, 2), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1484, 2), (key1484, 2), (key1484, 2), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1)]

def rawRow14738 : Integer.Sparse Key := [(key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1940, -1), (key1940, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1937, -1), (key1937, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1), (key1358, 2), (key1710, 2), (key1710, 2), (key1358, -1), (key1358, -1), (key1484, -1), (key1484, -1), (key1710, -1), (key1710, -1)]

def rawRow14739 : Integer.Sparse Key := [(key1723, -1), (key1940, -1), (key1374, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, -1), (key1937, -1), (key1364, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, -1), (key1710, -1), (key1358, -1), (key1710, -1), (key1358, -1), (key1484, -1)]

def rawRow14740 : Integer.Sparse Key := [(key1940, -1), (key1723, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1937, -1), (key1716, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, -1), (key1484, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1358, -1)]

def rawRow14741 : Integer.Sparse Key := [(key1501, 4), (key1501, 4), (key1506, 4), (key1501, -4), (key1506, -4), (key1506, -4), (key1733, -4), (key1735, -4), (key1735, -4), (key1735, 12)]

def rawRow14742 : Integer.Sparse Key := [(key1501, 4), (key1506, 4), (key1501, 4), (key1506, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1733, -4), (key1735, -4), (key1735, 12)]

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

def rawRow18455 : Integer.Sparse Key := [(key83, 24), (key0, 24), (key83, 24), (key83, 24), (key83, 24)]

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

def rawRow1358 : Integer.Sparse Key := [(key1192, -2), (key1005, -2), (key1192, -2), (key1111, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1111, 1), (key1198, 2), (key1018, 2), (key1198, 2), (key1033, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1033, -1), (key1126, -1), (key1198, -1), (key1018, -1), (key1198, -1), (key1018, -1), (key1126, -1), (key1040, 1), (key1192, 1), (key1005, 1), (key1192, 1), (key1005, 1), (key1040, 1)]

def rawRow1359 : Integer.Sparse Key := [(key1192, -2), (key1192, -2), (key1005, -2), (key1190, 1), (key1111, 1), (key1190, 1), (key998, 1), (key1111, 1), (key998, 1), (key1198, 2), (key1198, 2), (key1018, 2), (key1190, -1), (key1033, -1), (key1190, -1), (key998, -1), (key1033, -1), (key998, -1), (key1198, -1), (key1126, -1), (key1198, -1), (key1018, -1), (key1126, -1), (key1018, -1), (key1192, 1), (key1040, 1), (key1192, 1), (key1005, 1), (key1040, 1), (key1005, 1)]

def rawRow1360 : Integer.Sparse Key := [(key1126, -2), (key1126, -2), (key1126, -2), (key1198, 1), (key1198, 1), (key1198, 1), (key1198, 1), (key1198, 1), (key1198, 1), (key1040, 2), (key1040, 2), (key1040, 2), (key1192, -1), (key1192, -1), (key1192, -1), (key1192, -1), (key1192, -1), (key1192, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1)]

def rawRow1361 : Integer.Sparse Key := [(key1018, -2), (key1198, -2), (key1198, -2), (key1018, 1), (key1018, 1), (key1126, 1), (key1126, 1), (key1198, 1), (key1198, 1), (key1005, 2), (key1192, 2), (key1192, 2), (key1005, -1), (key1005, -1), (key1040, -1), (key1040, -1), (key1192, -1), (key1192, -1), (key998, -1), (key998, -1), (key1111, -1), (key1111, -1), (key1190, -1), (key1190, -1), (key998, 1), (key998, 1), (key1033, 1), (key1033, 1), (key1190, 1), (key1190, 1)]

def rawRow1362 : Integer.Sparse Key := [(key1198, -2), (key1018, -2), (key1198, -2), (key1126, 1), (key1198, 1), (key1018, 1), (key1198, 1), (key1018, 1), (key1126, 1), (key1192, 2), (key1005, 2), (key1192, 2), (key1040, -1), (key1192, -1), (key1005, -1), (key1192, -1), (key1005, -1), (key1040, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1111, -1), (key1033, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1033, 1)]

def rawRow1363 : Integer.Sparse Key := [(key1198, -2), (key1198, -2), (key1018, -2), (key1198, 1), (key1126, 1), (key1198, 1), (key1018, 1), (key1126, 1), (key1018, 1), (key1192, 2), (key1192, 2), (key1005, 2), (key1192, -1), (key1040, -1), (key1192, -1), (key1005, -1), (key1040, -1), (key1005, -1), (key1190, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1111, -1), (key998, -1), (key1190, 1), (key1033, 1), (key1190, 1), (key998, 1), (key1033, 1), (key998, 1)]

def rawRow1364 : Integer.Sparse Key := [(key17, -6), (key17, 2), (key17, 2), (key28, 2), (key42, 6), (key42, -2), (key42, -2), (key69, -2), (key99, -2), (key99, -2), (key108, -2), (key99, 2), (key99, 2), (key132, 2)]

def rawRow1365 : Integer.Sparse Key := [(key17, -6), (key17, 2), (key28, 2), (key17, 2), (key42, 6), (key42, -2), (key69, -2), (key42, -2), (key99, -2), (key108, -2), (key99, -2), (key99, 2), (key132, 2), (key99, 2)]

def rawRow1366 : Integer.Sparse Key := [(key17, -6), (key28, 2), (key17, 2), (key17, 2), (key42, 6), (key69, -2), (key42, -2), (key42, -2), (key108, -2), (key99, -2), (key99, -2), (key132, 2), (key99, 2), (key99, 2)]

def rawRow1367 : Integer.Sparse Key := [(key28, -6), (key17, 2), (key17, 2), (key17, 2), (key69, 6), (key42, -2), (key42, -2), (key42, -2), (key132, -2), (key132, -2), (key132, -2), (key108, 2), (key108, 2), (key108, 2)]

def rawRow1368 : Integer.Sparse Key := [(key42, -6), (key99, 2), (key99, 2), (key108, 2), (key17, 6), (key99, -2), (key99, -2), (key132, -2), (key17, -2), (key17, -2), (key28, -2), (key42, 2), (key42, 2), (key69, 2)]

def rawRow1369 : Integer.Sparse Key := [(key42, -6), (key99, 2), (key108, 2), (key99, 2), (key17, 6), (key99, -2), (key132, -2), (key99, -2), (key17, -2), (key28, -2), (key17, -2), (key42, 2), (key69, 2), (key42, 2)]

def rawRow1370 : Integer.Sparse Key := [(key42, -6), (key108, 2), (key99, 2), (key99, 2), (key17, 6), (key132, -2), (key99, -2), (key99, -2), (key28, -2), (key17, -2), (key17, -2), (key69, 2), (key42, 2), (key42, 2)]

def rawRow1371 : Integer.Sparse Key := [(key108, -6), (key42, 2), (key99, 2), (key99, 2), (key132, 6), (key17, -2), (key99, -2), (key99, -2), (key69, -2), (key132, -2), (key132, -2), (key28, 2), (key108, 2), (key108, 2)]

def rawRow1372 : Integer.Sparse Key := [(key108, -6), (key99, 2), (key42, 2), (key99, 2), (key132, 6), (key99, -2), (key17, -2), (key99, -2), (key132, -2), (key69, -2), (key132, -2), (key108, 2), (key28, 2), (key108, 2)]

def rawRow1373 : Integer.Sparse Key := [(key108, -6), (key99, 2), (key99, 2), (key42, 2), (key132, 6), (key99, -2), (key99, -2), (key17, -2), (key132, -2), (key132, -2), (key69, -2), (key108, 2), (key108, 2), (key28, 2)]

def rawRow1374 : Integer.Sparse Key := [(key69, -6), (key132, 2), (key132, 2), (key132, 2), (key28, 6), (key108, -2), (key108, -2), (key108, -2), (key17, -2), (key17, -2), (key17, -2), (key42, 2), (key42, 2), (key42, 2)]

def rawRow1375 : Integer.Sparse Key := [(key132, -6), (key69, 2), (key132, 2), (key132, 2), (key108, 6), (key28, -2), (key108, -2), (key108, -2), (key42, -2), (key99, -2), (key99, -2), (key17, 2), (key99, 2), (key99, 2)]

def rawRow1376 : Integer.Sparse Key := [(key132, -6), (key132, 2), (key69, 2), (key132, 2), (key108, 6), (key108, -2), (key28, -2), (key108, -2), (key99, -2), (key42, -2), (key99, -2), (key99, 2), (key17, 2), (key99, 2)]

def rawRow1377 : Integer.Sparse Key := [(key132, -6), (key132, 2), (key132, 2), (key69, 2), (key108, 6), (key108, -2), (key108, -2), (key28, -2), (key99, -2), (key99, -2), (key42, -2), (key99, 2), (key99, 2), (key17, 2)]

def rawRow1378 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1000, -2), (key994, 1), (key1000, 1), (key994, 1), (key1014, 1), (key1000, 1), (key1014, 1), (key1029, 2), (key1035, 2), (key1035, 2), (key1029, -1), (key1035, -1), (key1029, -1), (key1070, -1), (key1035, -1), (key1070, -1), (key1107, -1), (key1113, -1), (key1107, -1), (key1122, -1), (key1113, -1), (key1122, -1), (key1107, 1), (key1113, 1), (key1107, 1), (key1149, 1), (key1113, 1), (key1149, 1)]

def rawRow1379 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1000, -2), (key1000, 1), (key994, 1), (key1014, 1), (key994, 1), (key1014, 1), (key1000, 1), (key1035, 2), (key1029, 2), (key1035, 2), (key1035, -1), (key1029, -1), (key1070, -1), (key1029, -1), (key1070, -1), (key1035, -1), (key1113, -1), (key1107, -1), (key1122, -1), (key1107, -1), (key1122, -1), (key1113, -1), (key1113, 1), (key1107, 1), (key1149, 1), (key1107, 1), (key1149, 1), (key1113, 1)]

def rawRow1380 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key994, -2), (key1014, 1), (key1014, 1), (key1000, 1), (key1000, 1), (key994, 1), (key994, 1), (key1035, 2), (key1035, 2), (key1029, 2), (key1070, -1), (key1070, -1), (key1035, -1), (key1035, -1), (key1029, -1), (key1029, -1), (key1122, -1), (key1122, -1), (key1113, -1), (key1113, -1), (key1107, -1), (key1107, -1), (key1149, 1), (key1149, 1), (key1113, 1), (key1113, 1), (key1107, 1), (key1107, 1)]

def rawRow1381 : Integer.Sparse Key := [(key1014, -2), (key1014, -2), (key1014, -2), (key1000, 1), (key1000, 1), (key1000, 1), (key1000, 1), (key1000, 1), (key1000, 1), (key1070, 2), (key1070, 2), (key1070, 2), (key1035, -1), (key1035, -1), (key1035, -1), (key1035, -1), (key1035, -1), (key1035, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1122, 1), (key1122, 1), (key1122, 1), (key1122, 1), (key1122, 1), (key1122, 1)]

def rawRow1382 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1035, -2), (key1107, 1), (key1113, 1), (key1107, 1), (key1122, 1), (key1113, 1), (key1122, 1), (key994, 2), (key1000, 2), (key1000, 2), (key1107, -1), (key1113, -1), (key1107, -1), (key1149, -1), (key1113, -1), (key1149, -1), (key994, -1), (key1000, -1), (key994, -1), (key1014, -1), (key1000, -1), (key1014, -1), (key1029, 1), (key1035, 1), (key1029, 1), (key1070, 1), (key1035, 1), (key1070, 1)]

def rawRow1383 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1035, -2), (key1113, 1), (key1107, 1), (key1122, 1), (key1107, 1), (key1122, 1), (key1113, 1), (key1000, 2), (key994, 2), (key1000, 2), (key1113, -1), (key1107, -1), (key1149, -1), (key1107, -1), (key1149, -1), (key1113, -1), (key1000, -1), (key994, -1), (key1014, -1), (key994, -1), (key1014, -1), (key1000, -1), (key1035, 1), (key1029, 1), (key1070, 1), (key1029, 1), (key1070, 1), (key1035, 1)]

def rawRow1384 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1029, -2), (key1122, 1), (key1122, 1), (key1113, 1), (key1113, 1), (key1107, 1), (key1107, 1), (key1000, 2), (key1000, 2), (key994, 2), (key1149, -1), (key1149, -1), (key1113, -1), (key1113, -1), (key1107, -1), (key1107, -1), (key1014, -1), (key1014, -1), (key1000, -1), (key1000, -1), (key994, -1), (key994, -1), (key1070, 1), (key1070, 1), (key1035, 1), (key1035, 1), (key1029, 1), (key1029, 1)]

def rawRow1385 : Integer.Sparse Key := [(key1122, -2), (key1122, -2), (key1234, -2), (key1035, 1), (key1035, 1), (key1113, 1), (key1113, 1), (key1231, 1), (key1231, 1), (key1149, 2), (key1149, 2), (key1241, 2), (key1000, -1), (key1000, -1), (key1113, -1), (key1113, -1), (key1231, -1), (key1231, -1), (key1070, -1), (key1070, -1), (key1149, -1), (key1149, -1), (key1241, -1), (key1241, -1), (key1014, 1), (key1014, 1), (key1122, 1), (key1122, 1), (key1234, 1), (key1234, 1)]

def rawRow1386 : Integer.Sparse Key := [(key1122, -2), (key1234, -2), (key1122, -2), (key1113, 1), (key1231, 1), (key1035, 1), (key1231, 1), (key1035, 1), (key1113, 1), (key1149, 2), (key1241, 2), (key1149, 2), (key1113, -1), (key1231, -1), (key1000, -1), (key1231, -1), (key1000, -1), (key1113, -1), (key1149, -1), (key1241, -1), (key1070, -1), (key1241, -1), (key1070, -1), (key1149, -1), (key1122, 1), (key1234, 1), (key1014, 1), (key1234, 1), (key1014, 1), (key1122, 1)]

def rawRow1387 : Integer.Sparse Key := [(key1234, -2), (key1122, -2), (key1122, -2), (key1231, 1), (key1113, 1), (key1231, 1), (key1035, 1), (key1113, 1), (key1035, 1), (key1241, 2), (key1149, 2), (key1149, 2), (key1231, -1), (key1113, -1), (key1231, -1), (key1000, -1), (key1113, -1), (key1000, -1), (key1241, -1), (key1149, -1), (key1241, -1), (key1070, -1), (key1149, -1), (key1070, -1), (key1234, 1), (key1122, 1), (key1234, 1), (key1014, 1), (key1122, 1), (key1014, 1)]

def rawRow1388 : Integer.Sparse Key := [(key1070, -2), (key1070, -2), (key1070, -2), (key1149, 1), (key1149, 1), (key1149, 1), (key1149, 1), (key1149, 1), (key1149, 1), (key1014, 2), (key1014, 2), (key1014, 2), (key1122, -1), (key1122, -1), (key1122, -1), (key1122, -1), (key1122, -1), (key1122, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1035, 1), (key1035, 1), (key1035, 1), (key1035, 1), (key1035, 1), (key1035, 1)]

def rawRow1389 : Integer.Sparse Key := [(key1149, -2), (key1149, -2), (key1241, -2), (key1070, 1), (key1070, 1), (key1149, 1), (key1149, 1), (key1241, 1), (key1241, 1), (key1122, 2), (key1122, 2), (key1234, 2), (key1014, -1), (key1014, -1), (key1122, -1), (key1122, -1), (key1234, -1), (key1234, -1), (key1035, -1), (key1035, -1), (key1113, -1), (key1113, -1), (key1231, -1), (key1231, -1), (key1000, 1), (key1000, 1), (key1113, 1), (key1113, 1), (key1231, 1), (key1231, 1)]

def rawRow1390 : Integer.Sparse Key := [(key1149, -2), (key1241, -2), (key1149, -2), (key1149, 1), (key1241, 1), (key1070, 1), (key1241, 1), (key1070, 1), (key1149, 1), (key1122, 2), (key1234, 2), (key1122, 2), (key1122, -1), (key1234, -1), (key1014, -1), (key1234, -1), (key1014, -1), (key1122, -1), (key1113, -1), (key1231, -1), (key1035, -1), (key1231, -1), (key1035, -1), (key1113, -1), (key1113, 1), (key1231, 1), (key1000, 1), (key1231, 1), (key1000, 1), (key1113, 1)]

def rawRow1391 : Integer.Sparse Key := [(key1241, -2), (key1149, -2), (key1149, -2), (key1241, 1), (key1149, 1), (key1241, 1), (key1070, 1), (key1149, 1), (key1070, 1), (key1234, 2), (key1122, 2), (key1122, 2), (key1234, -1), (key1122, -1), (key1234, -1), (key1014, -1), (key1122, -1), (key1014, -1), (key1231, -1), (key1113, -1), (key1231, -1), (key1035, -1), (key1113, -1), (key1035, -1), (key1231, 1), (key1113, 1), (key1231, 1), (key1000, 1), (key1113, 1), (key1000, 1)]

def rawRow1392 : Integer.Sparse Key := [(key2, -2), (key6, -2), (key6, -2), (key6, 6), (key85, 2), (key89, 2), (key89, 2), (key89, -2), (key89, -2), (key166, -2), (key150, -6), (key150, 2), (key150, 2), (key186, 2)]

def rawRow1393 : Integer.Sparse Key := [(key6, -2), (key2, -2), (key6, -2), (key6, 6), (key89, 2), (key85, 2), (key89, 2), (key89, -2), (key166, -2), (key89, -2), (key150, -6), (key150, 2), (key186, 2), (key150, 2)]

def rawRow1394 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key2, -2), (key6, 6), (key89, 2), (key89, 2), (key85, 2), (key166, -2), (key89, -2), (key89, -2), (key150, -6), (key186, 2), (key150, 2), (key150, 2)]

def rawRow1395 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key6, -2), (key2, 6), (key166, 2), (key166, 2), (key166, 2), (key85, -2), (key85, -2), (key85, -2), (key186, -6), (key150, 2), (key150, 2), (key150, 2)]

def rawRow1396 : Integer.Sparse Key := [(key85, -2), (key89, -2), (key89, -2), (key150, 6), (key2, 2), (key6, 2), (key6, 2), (key150, -2), (key150, -2), (key186, -2), (key6, -6), (key89, 2), (key89, 2), (key166, 2)]

def rawRow1397 : Integer.Sparse Key := [(key89, -2), (key85, -2), (key89, -2), (key150, 6), (key6, 2), (key2, 2), (key6, 2), (key150, -2), (key186, -2), (key150, -2), (key6, -6), (key89, 2), (key166, 2), (key89, 2)]

def rawRow1398 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key85, -2), (key150, 6), (key6, 2), (key6, 2), (key2, 2), (key186, -2), (key150, -2), (key150, -2), (key6, -6), (key166, 2), (key89, 2), (key89, 2)]

def rawRow1399 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key150, -2), (key85, 6), (key166, 2), (key166, 2), (key186, 2), (key2, -2), (key85, -2), (key85, -2), (key166, -6), (key6, 2), (key89, 2), (key89, 2)]

def rawRow1400 : Integer.Sparse Key := [(key89, -2), (key150, -2), (key89, -2), (key85, 6), (key166, 2), (key186, 2), (key166, 2), (key85, -2), (key2, -2), (key85, -2), (key166, -6), (key89, 2), (key6, 2), (key89, 2)]

def rawRow1401 : Integer.Sparse Key := [(key150, -2), (key89, -2), (key89, -2), (key85, 6), (key186, 2), (key166, 2), (key166, 2), (key85, -2), (key85, -2), (key2, -2), (key166, -6), (key89, 2), (key89, 2), (key6, 2)]

def rawRow1402 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key166, -2), (key186, 6), (key6, 2), (key6, 2), (key6, 2), (key150, -2), (key150, -2), (key150, -2), (key2, -6), (key85, 2), (key85, 2), (key85, 2)]

def rawRow1403 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key186, -2), (key166, 6), (key89, 2), (key89, 2), (key150, 2), (key6, -2), (key89, -2), (key89, -2), (key85, -6), (key2, 2), (key85, 2), (key85, 2)]

def rawRow1404 : Integer.Sparse Key := [(key166, -2), (key186, -2), (key166, -2), (key166, 6), (key89, 2), (key150, 2), (key89, 2), (key89, -2), (key6, -2), (key89, -2), (key85, -6), (key85, 2), (key2, 2), (key85, 2)]

def rawRow1405 : Integer.Sparse Key := [(key186, -2), (key166, -2), (key166, -2), (key166, 6), (key150, 2), (key89, 2), (key89, 2), (key89, -2), (key89, -2), (key6, -2), (key85, -6), (key85, 2), (key85, 2), (key2, 2)]

def rawRow1406 : Integer.Sparse Key := [(key992, -6), (key992, 2), (key992, 2), (key1010, 2), (key1027, 6), (key1027, -2), (key1027, -2), (key1066, -2), (key1105, -2), (key1105, -2), (key1118, -2), (key1105, 2), (key1105, 2), (key1145, 2)]

def rawRow1407 : Integer.Sparse Key := [(key992, -6), (key992, 2), (key1010, 2), (key992, 2), (key1027, 6), (key1027, -2), (key1066, -2), (key1027, -2), (key1105, -2), (key1118, -2), (key1105, -2), (key1105, 2), (key1145, 2), (key1105, 2)]

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

def rawRow1408 : Integer.Sparse Key := [(key992, -6), (key1010, 2), (key992, 2), (key992, 2), (key1027, 6), (key1066, -2), (key1027, -2), (key1027, -2), (key1118, -2), (key1105, -2), (key1105, -2), (key1145, 2), (key1105, 2), (key1105, 2)]

def rawRow1409 : Integer.Sparse Key := [(key1010, -6), (key992, 2), (key992, 2), (key992, 2), (key1066, 6), (key1027, -2), (key1027, -2), (key1027, -2), (key1145, -2), (key1145, -2), (key1145, -2), (key1118, 2), (key1118, 2), (key1118, 2)]

def rawRow1410 : Integer.Sparse Key := [(key1027, -6), (key1105, 2), (key1105, 2), (key1118, 2), (key992, 6), (key1105, -2), (key1105, -2), (key1145, -2), (key992, -2), (key992, -2), (key1010, -2), (key1027, 2), (key1027, 2), (key1066, 2)]

def rawRow1411 : Integer.Sparse Key := [(key1027, -6), (key1105, 2), (key1118, 2), (key1105, 2), (key992, 6), (key1105, -2), (key1145, -2), (key1105, -2), (key992, -2), (key1010, -2), (key992, -2), (key1027, 2), (key1066, 2), (key1027, 2)]

def rawRow1412 : Integer.Sparse Key := [(key1027, -6), (key1118, 2), (key1105, 2), (key1105, 2), (key992, 6), (key1145, -2), (key1105, -2), (key1105, -2), (key1010, -2), (key992, -2), (key992, -2), (key1066, 2), (key1027, 2), (key1027, 2)]

def rawRow1413 : Integer.Sparse Key := [(key1118, -6), (key1027, 2), (key1105, 2), (key1105, 2), (key1145, 6), (key992, -2), (key1105, -2), (key1105, -2), (key1066, -2), (key1145, -2), (key1145, -2), (key1010, 2), (key1118, 2), (key1118, 2)]

def rawRow1414 : Integer.Sparse Key := [(key1118, -6), (key1105, 2), (key1027, 2), (key1105, 2), (key1145, 6), (key1105, -2), (key992, -2), (key1105, -2), (key1145, -2), (key1066, -2), (key1145, -2), (key1118, 2), (key1010, 2), (key1118, 2)]

def rawRow1415 : Integer.Sparse Key := [(key1118, -6), (key1105, 2), (key1105, 2), (key1027, 2), (key1145, 6), (key1105, -2), (key1105, -2), (key992, -2), (key1145, -2), (key1145, -2), (key1066, -2), (key1118, 2), (key1118, 2), (key1010, 2)]

def rawRow1416 : Integer.Sparse Key := [(key1066, -6), (key1145, 2), (key1145, 2), (key1145, 2), (key1010, 6), (key1118, -2), (key1118, -2), (key1118, -2), (key992, -2), (key992, -2), (key992, -2), (key1027, 2), (key1027, 2), (key1027, 2)]

def rawRow1417 : Integer.Sparse Key := [(key1145, -6), (key1066, 2), (key1145, 2), (key1145, 2), (key1118, 6), (key1010, -2), (key1118, -2), (key1118, -2), (key1027, -2), (key1105, -2), (key1105, -2), (key992, 2), (key1105, 2), (key1105, 2)]

def rawRow1418 : Integer.Sparse Key := [(key1145, -6), (key1145, 2), (key1066, 2), (key1145, 2), (key1118, 6), (key1118, -2), (key1010, -2), (key1118, -2), (key1105, -2), (key1027, -2), (key1105, -2), (key1105, 2), (key992, 2), (key1105, 2)]

def rawRow1419 : Integer.Sparse Key := [(key1145, -6), (key1145, 2), (key1145, 2), (key1066, 2), (key1118, 6), (key1118, -2), (key1118, -2), (key1010, -2), (key1105, -2), (key1105, -2), (key1027, -2), (key1105, 2), (key1105, 2), (key992, 2)]

def rawRow1420 : Integer.Sparse Key := [(key376, -1), (key380, -1), (key376, -1), (key566, -1), (key380, -1), (key566, -1), (key380, 2), (key380, 2), (key566, 2), (key427, 1), (key431, 1), (key427, 1), (key591, 1), (key431, 1), (key591, 1), (key431, -1), (key465, -1), (key431, -1), (key591, -1), (key465, -1), (key591, -1), (key459, -2), (key459, -2), (key608, -2), (key459, 1), (key482, 1), (key459, 1), (key608, 1), (key482, 1), (key608, 1)]

def rawRow1421 : Integer.Sparse Key := [(key380, -1), (key376, -1), (key566, -1), (key376, -1), (key566, -1), (key380, -1), (key380, 2), (key566, 2), (key380, 2), (key431, 1), (key427, 1), (key591, 1), (key427, 1), (key591, 1), (key431, 1), (key465, -1), (key431, -1), (key591, -1), (key431, -1), (key591, -1), (key465, -1), (key459, -2), (key608, -2), (key459, -2), (key482, 1), (key459, 1), (key608, 1), (key459, 1), (key608, 1), (key482, 1)]

def rawRow1422 : Integer.Sparse Key := [(key566, -1), (key566, -1), (key380, -1), (key380, -1), (key376, -1), (key376, -1), (key566, 2), (key380, 2), (key380, 2), (key591, 1), (key591, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1), (key591, -1), (key591, -1), (key465, -1), (key465, -1), (key431, -1), (key431, -1), (key608, -2), (key459, -2), (key459, -2), (key608, 1), (key608, 1), (key482, 1), (key482, 1), (key459, 1), (key459, 1)]

def rawRow1423 : Integer.Sparse Key := [(key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key376, 2), (key376, 2), (key376, 2), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key427, -1), (key427, -1), (key427, -1), (key427, -1), (key427, -1), (key427, -1), (key482, -2), (key482, -2), (key482, -2), (key459, 1), (key459, 1), (key459, 1), (key459, 1), (key459, 1), (key459, 1)]

def rawRow1424 : Integer.Sparse Key := [(key427, -1), (key431, -1), (key427, -1), (key591, -1), (key431, -1), (key591, -1), (key459, 2), (key459, 2), (key608, 2), (key376, 1), (key380, 1), (key376, 1), (key566, 1), (key380, 1), (key566, 1), (key459, -1), (key482, -1), (key459, -1), (key608, -1), (key482, -1), (key608, -1), (key380, -2), (key380, -2), (key566, -2), (key431, 1), (key465, 1), (key431, 1), (key591, 1), (key465, 1), (key591, 1)]

def rawRow1425 : Integer.Sparse Key := [(key431, -1), (key427, -1), (key591, -1), (key427, -1), (key591, -1), (key431, -1), (key459, 2), (key608, 2), (key459, 2), (key380, 1), (key376, 1), (key566, 1), (key376, 1), (key566, 1), (key380, 1), (key482, -1), (key459, -1), (key608, -1), (key459, -1), (key608, -1), (key482, -1), (key380, -2), (key566, -2), (key380, -2), (key465, 1), (key431, 1), (key591, 1), (key431, 1), (key591, 1), (key465, 1)]

def rawRow1426 : Integer.Sparse Key := [(key591, -1), (key591, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key608, 2), (key459, 2), (key459, 2), (key566, 1), (key566, 1), (key380, 1), (key380, 1), (key376, 1), (key376, 1), (key608, -1), (key608, -1), (key482, -1), (key482, -1), (key459, -1), (key459, -1), (key566, -2), (key380, -2), (key380, -2), (key591, 1), (key591, 1), (key465, 1), (key465, 1), (key431, 1), (key431, 1)]

def rawRow1427 : Integer.Sparse Key := [(key211, -1), (key211, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key207, 2), (key427, 2), (key427, 2), (key216, 1), (key216, 1), (key465, 1), (key465, 1), (key482, 1), (key482, 1), (key207, -1), (key207, -1), (key376, -1), (key376, -1), (key427, -1), (key427, -1), (key216, -2), (key465, -2), (key465, -2), (key211, 1), (key211, 1), (key380, 1), (key380, 1), (key431, 1), (key431, 1)]

def rawRow1428 : Integer.Sparse Key := [(key431, -1), (key459, -1), (key211, -1), (key459, -1), (key211, -1), (key431, -1), (key427, 2), (key207, 2), (key427, 2), (key465, 1), (key482, 1), (key216, 1), (key482, 1), (key216, 1), (key465, 1), (key376, -1), (key427, -1), (key207, -1), (key427, -1), (key207, -1), (key376, -1), (key465, -2), (key216, -2), (key465, -2), (key380, 1), (key431, 1), (key211, 1), (key431, 1), (key211, 1), (key380, 1)]

def rawRow1429 : Integer.Sparse Key := [(key459, -1), (key431, -1), (key459, -1), (key211, -1), (key431, -1), (key211, -1), (key427, 2), (key427, 2), (key207, 2), (key482, 1), (key465, 1), (key482, 1), (key216, 1), (key465, 1), (key216, 1), (key427, -1), (key376, -1), (key427, -1), (key207, -1), (key376, -1), (key207, -1), (key465, -2), (key465, -2), (key216, -2), (key431, 1), (key380, 1), (key431, 1), (key211, 1), (key380, 1), (key211, 1)]

def rawRow1430 : Integer.Sparse Key := [(key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key482, 2), (key482, 2), (key482, 2), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key376, -2), (key376, -2), (key376, -2), (key427, 1), (key427, 1), (key427, 1), (key427, 1), (key427, 1), (key427, 1)]

def rawRow1431 : Integer.Sparse Key := [(key216, -1), (key216, -1), (key465, -1), (key465, -1), (key482, -1), (key482, -1), (key216, 2), (key465, 2), (key465, 2), (key211, 1), (key211, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1), (key211, -1), (key211, -1), (key380, -1), (key380, -1), (key431, -1), (key431, -1), (key207, -2), (key427, -2), (key427, -2), (key207, 1), (key207, 1), (key376, 1), (key376, 1), (key427, 1), (key427, 1)]

def rawRow1432 : Integer.Sparse Key := [(key465, -1), (key482, -1), (key216, -1), (key482, -1), (key216, -1), (key465, -1), (key465, 2), (key216, 2), (key465, 2), (key431, 1), (key459, 1), (key211, 1), (key459, 1), (key211, 1), (key431, 1), (key380, -1), (key431, -1), (key211, -1), (key431, -1), (key211, -1), (key380, -1), (key427, -2), (key207, -2), (key427, -2), (key376, 1), (key427, 1), (key207, 1), (key427, 1), (key207, 1), (key376, 1)]

def rawRow1433 : Integer.Sparse Key := [(key482, -1), (key465, -1), (key482, -1), (key216, -1), (key465, -1), (key216, -1), (key465, 2), (key465, 2), (key216, 2), (key459, 1), (key431, 1), (key459, 1), (key211, 1), (key431, 1), (key211, 1), (key431, -1), (key380, -1), (key431, -1), (key211, -1), (key380, -1), (key211, -1), (key427, -2), (key427, -2), (key207, -2), (key427, 1), (key376, 1), (key427, 1), (key207, 1), (key376, 1), (key207, 1)]

def rawRow1434 : Integer.Sparse Key := [(key1049, -2), (key1061, -2), (key1061, -2), (key1053, 2), (key1061, 2), (key1061, 2), (key1135, 2), (key1141, 2), (key1141, 2), (key1141, -6), (key1237, -2), (key1239, -2), (key1239, -2), (key1239, 6)]

def rawRow1435 : Integer.Sparse Key := [(key1061, -2), (key1049, -2), (key1061, -2), (key1061, 2), (key1053, 2), (key1061, 2), (key1141, 2), (key1135, 2), (key1141, 2), (key1141, -6), (key1239, -2), (key1237, -2), (key1239, -2), (key1239, 6)]

def rawRow1436 : Integer.Sparse Key := [(key1061, -2), (key1061, -2), (key1049, -2), (key1061, 2), (key1061, 2), (key1053, 2), (key1141, 2), (key1141, 2), (key1135, 2), (key1141, -6), (key1239, -2), (key1239, -2), (key1237, -2), (key1239, 6)]

def rawRow1437 : Integer.Sparse Key := [(key1053, -2), (key1053, -2), (key1053, -2), (key1049, 2), (key1049, 2), (key1049, 2), (key1141, 2), (key1141, 2), (key1141, 2), (key1135, -6), (key1239, -2), (key1239, -2), (key1239, -2), (key1237, 6)]

def rawRow1438 : Integer.Sparse Key := [(key1135, -2), (key1141, -2), (key1141, -2), (key1237, 2), (key1239, 2), (key1239, 2), (key1049, 2), (key1061, 2), (key1061, 2), (key1239, -6), (key1053, -2), (key1061, -2), (key1061, -2), (key1141, 6)]

def rawRow1439 : Integer.Sparse Key := [(key1141, -2), (key1135, -2), (key1141, -2), (key1239, 2), (key1237, 2), (key1239, 2), (key1061, 2), (key1049, 2), (key1061, 2), (key1239, -6), (key1061, -2), (key1053, -2), (key1061, -2), (key1141, 6)]

def rawRow1440 : Integer.Sparse Key := [(key1141, -2), (key1141, -2), (key1135, -2), (key1239, 2), (key1239, 2), (key1237, 2), (key1061, 2), (key1061, 2), (key1049, 2), (key1239, -6), (key1061, -2), (key1061, -2), (key1053, -2), (key1141, 6)]

def rawRow1441 : Integer.Sparse Key := [(key1053, -2), (key1053, -2), (key1237, -2), (key1049, 2), (key1049, 2), (key1135, 2), (key1061, 2), (key1061, 2), (key1239, 2), (key1049, -6), (key1061, -2), (key1061, -2), (key1141, -2), (key1053, 6)]

def rawRow1442 : Integer.Sparse Key := [(key1053, -2), (key1237, -2), (key1053, -2), (key1049, 2), (key1135, 2), (key1049, 2), (key1061, 2), (key1239, 2), (key1061, 2), (key1049, -6), (key1061, -2), (key1141, -2), (key1061, -2), (key1053, 6)]

def rawRow1443 : Integer.Sparse Key := [(key1237, -2), (key1053, -2), (key1053, -2), (key1135, 2), (key1049, 2), (key1049, 2), (key1239, 2), (key1061, 2), (key1061, 2), (key1049, -6), (key1141, -2), (key1061, -2), (key1061, -2), (key1053, 6)]

def rawRow1444 : Integer.Sparse Key := [(key1141, -2), (key1141, -2), (key1141, -2), (key1239, 2), (key1239, 2), (key1239, 2), (key1053, 2), (key1053, 2), (key1053, 2), (key1237, -6), (key1049, -2), (key1049, -2), (key1049, -2), (key1135, 6)]

def rawRow1445 : Integer.Sparse Key := [(key1061, -2), (key1061, -2), (key1239, -2), (key1061, 2), (key1061, 2), (key1141, 2), (key1053, 2), (key1053, 2), (key1237, 2), (key1053, -6), (key1049, -2), (key1049, -2), (key1135, -2), (key1049, 6)]

def rawRow1446 : Integer.Sparse Key := [(key1061, -2), (key1239, -2), (key1061, -2), (key1061, 2), (key1141, 2), (key1061, 2), (key1053, 2), (key1237, 2), (key1053, 2), (key1053, -6), (key1049, -2), (key1135, -2), (key1049, -2), (key1049, 6)]

def rawRow1447 : Integer.Sparse Key := [(key1239, -2), (key1061, -2), (key1061, -2), (key1141, 2), (key1061, 2), (key1061, 2), (key1237, 2), (key1053, 2), (key1053, 2), (key1053, -6), (key1135, -2), (key1049, -2), (key1049, -2), (key1049, 6)]

def rawRow1448 : Integer.Sparse Key := [(key207, -2), (key211, -2), (key211, -2), (key207, 1), (key211, 1), (key207, 1), (key216, 1), (key211, 1), (key216, 1), (key376, 2), (key380, 2), (key380, 2), (key376, -1), (key380, -1), (key376, -1), (key566, -1), (key380, -1), (key566, -1), (key427, -1), (key431, -1), (key427, -1), (key465, -1), (key431, -1), (key465, -1), (key427, 1), (key431, 1), (key427, 1), (key591, 1), (key431, 1), (key591, 1)]

def rawRow1449 : Integer.Sparse Key := [(key211, -2), (key207, -2), (key211, -2), (key211, 1), (key207, 1), (key216, 1), (key207, 1), (key216, 1), (key211, 1), (key380, 2), (key376, 2), (key380, 2), (key380, -1), (key376, -1), (key566, -1), (key376, -1), (key566, -1), (key380, -1), (key431, -1), (key427, -1), (key465, -1), (key427, -1), (key465, -1), (key431, -1), (key431, 1), (key427, 1), (key591, 1), (key427, 1), (key591, 1), (key431, 1)]

def rawRow1450 : Integer.Sparse Key := [(key211, -2), (key211, -2), (key207, -2), (key216, 1), (key216, 1), (key211, 1), (key211, 1), (key207, 1), (key207, 1), (key380, 2), (key380, 2), (key376, 2), (key566, -1), (key566, -1), (key380, -1), (key380, -1), (key376, -1), (key376, -1), (key465, -1), (key465, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key591, 1), (key591, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1)]

def rawRow1451 : Integer.Sparse Key := [(key216, -2), (key216, -2), (key216, -2), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key566, 2), (key566, 2), (key566, 2), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1)]

def rawRow1452 : Integer.Sparse Key := [(key376, -2), (key380, -2), (key380, -2), (key427, 1), (key431, 1), (key427, 1), (key465, 1), (key431, 1), (key465, 1), (key207, 2), (key211, 2), (key211, 2), (key427, -1), (key431, -1), (key427, -1), (key591, -1), (key431, -1), (key591, -1), (key207, -1), (key211, -1), (key207, -1), (key216, -1), (key211, -1), (key216, -1), (key376, 1), (key380, 1), (key376, 1), (key566, 1), (key380, 1), (key566, 1)]

def rawRow1453 : Integer.Sparse Key := [(key380, -2), (key376, -2), (key380, -2), (key431, 1), (key427, 1), (key465, 1), (key427, 1), (key465, 1), (key431, 1), (key211, 2), (key207, 2), (key211, 2), (key431, -1), (key427, -1), (key591, -1), (key427, -1), (key591, -1), (key431, -1), (key211, -1), (key207, -1), (key216, -1), (key207, -1), (key216, -1), (key211, -1), (key380, 1), (key376, 1), (key566, 1), (key376, 1), (key566, 1), (key380, 1)]

def rawRow1454 : Integer.Sparse Key := [(key380, -2), (key380, -2), (key376, -2), (key465, 1), (key465, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1), (key211, 2), (key211, 2), (key207, 2), (key591, -1), (key591, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key216, -1), (key216, -1), (key211, -1), (key211, -1), (key207, -1), (key207, -1), (key566, 1), (key566, 1), (key380, 1), (key380, 1), (key376, 1), (key376, 1)]

def rawRow1455 : Integer.Sparse Key := [(key465, -2), (key465, -2), (key482, -2), (key380, 1), (key380, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1), (key591, 2), (key591, 2), (key608, 2), (key211, -1), (key211, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key566, -1), (key566, -1), (key591, -1), (key591, -1), (key608, -1), (key608, -1), (key216, 1), (key216, 1), (key465, 1), (key465, 1), (key482, 1), (key482, 1)]

def rawRow1456 : Integer.Sparse Key := [(key465, -2), (key482, -2), (key465, -2), (key431, 1), (key459, 1), (key380, 1), (key459, 1), (key380, 1), (key431, 1), (key591, 2), (key608, 2), (key591, 2), (key431, -1), (key459, -1), (key211, -1), (key459, -1), (key211, -1), (key431, -1), (key591, -1), (key608, -1), (key566, -1), (key608, -1), (key566, -1), (key591, -1), (key465, 1), (key482, 1), (key216, 1), (key482, 1), (key216, 1), (key465, 1)]

def rawRow1457 : Integer.Sparse Key := [(key482, -2), (key465, -2), (key465, -2), (key459, 1), (key431, 1), (key459, 1), (key380, 1), (key431, 1), (key380, 1), (key608, 2), (key591, 2), (key591, 2), (key459, -1), (key431, -1), (key459, -1), (key211, -1), (key431, -1), (key211, -1), (key608, -1), (key591, -1), (key608, -1), (key566, -1), (key591, -1), (key566, -1), (key482, 1), (key465, 1), (key482, 1), (key216, 1), (key465, 1), (key216, 1)]

def rawRow1458 : Integer.Sparse Key := [(key566, -2), (key566, -2), (key566, -2), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key216, 2), (key216, 2), (key216, 2), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1)]

def rawRow1459 : Integer.Sparse Key := [(key591, -2), (key591, -2), (key608, -2), (key566, 1), (key566, 1), (key591, 1), (key591, 1), (key608, 1), (key608, 1), (key465, 2), (key465, 2), (key482, 2), (key216, -1), (key216, -1), (key465, -1), (key465, -1), (key482, -1), (key482, -1), (key380, -1), (key380, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key211, 1), (key211, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1)]

def rawRow1460 : Integer.Sparse Key := [(key591, -2), (key608, -2), (key591, -2), (key591, 1), (key608, 1), (key566, 1), (key608, 1), (key566, 1), (key591, 1), (key465, 2), (key482, 2), (key465, 2), (key465, -1), (key482, -1), (key216, -1), (key482, -1), (key216, -1), (key465, -1), (key431, -1), (key459, -1), (key380, -1), (key459, -1), (key380, -1), (key431, -1), (key431, 1), (key459, 1), (key211, 1), (key459, 1), (key211, 1), (key431, 1)]

def rawRow1461 : Integer.Sparse Key := [(key608, -2), (key591, -2), (key591, -2), (key608, 1), (key591, 1), (key608, 1), (key566, 1), (key591, 1), (key566, 1), (key482, 2), (key465, 2), (key465, 2), (key482, -1), (key465, -1), (key482, -1), (key216, -1), (key465, -1), (key216, -1), (key459, -1), (key431, -1), (key459, -1), (key380, -1), (key431, -1), (key380, -1), (key459, 1), (key431, 1), (key459, 1), (key211, 1), (key431, 1), (key211, 1)]

def rawRow1462 : Integer.Sparse Key := [(key1, -2), (key4, -2), (key4, -2), (key4, 6), (key84, 2), (key87, 2), (key87, 2), (key87, -2), (key87, -2), (key148, -2), (key164, -6), (key164, 2), (key164, 2), (key184, 2)]

def rawRow1463 : Integer.Sparse Key := [(key4, -2), (key1, -2), (key4, -2), (key4, 6), (key87, 2), (key84, 2), (key87, 2), (key87, -2), (key148, -2), (key87, -2), (key164, -6), (key164, 2), (key184, 2), (key164, 2)]

def rawRow1464 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key1, -2), (key4, 6), (key87, 2), (key87, 2), (key84, 2), (key148, -2), (key87, -2), (key87, -2), (key164, -6), (key184, 2), (key164, 2), (key164, 2)]

def rawRow1465 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key4, -2), (key1, 6), (key148, 2), (key148, 2), (key148, 2), (key84, -2), (key84, -2), (key84, -2), (key184, -6), (key164, 2), (key164, 2), (key164, 2)]

def rawRow1466 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key87, -2), (key148, 6), (key1, 2), (key4, 2), (key4, 2), (key164, -2), (key164, -2), (key184, -2), (key4, -6), (key87, 2), (key87, 2), (key148, 2)]

def rawRow1467 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key87, -2), (key148, 6), (key4, 2), (key1, 2), (key4, 2), (key164, -2), (key184, -2), (key164, -2), (key4, -6), (key87, 2), (key148, 2), (key87, 2)]

def rawRow1468 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key84, -2), (key148, 6), (key4, 2), (key4, 2), (key1, 2), (key184, -2), (key164, -2), (key164, -2), (key4, -6), (key148, 2), (key87, 2), (key87, 2)]

def rawRow1469 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key148, -2), (key84, 6), (key164, 2), (key164, 2), (key184, 2), (key1, -2), (key84, -2), (key84, -2), (key148, -6), (key4, 2), (key87, 2), (key87, 2)]

def rawRow1470 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key87, -2), (key84, 6), (key164, 2), (key184, 2), (key164, 2), (key84, -2), (key1, -2), (key84, -2), (key148, -6), (key87, 2), (key4, 2), (key87, 2)]

def rawRow1471 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key87, -2), (key84, 6), (key184, 2), (key164, 2), (key164, 2), (key84, -2), (key84, -2), (key1, -2), (key148, -6), (key87, 2), (key87, 2), (key4, 2)]

def rawRow1472 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key164, -2), (key184, 6), (key4, 2), (key4, 2), (key4, 2), (key148, -2), (key148, -2), (key148, -2), (key1, -6), (key84, 2), (key84, 2), (key84, 2)]

def rawRow1473 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key184, -2), (key164, 6), (key87, 2), (key87, 2), (key148, 2), (key4, -2), (key87, -2), (key87, -2), (key84, -6), (key1, 2), (key84, 2), (key84, 2)]

def rawRow1474 : Integer.Sparse Key := [(key164, -2), (key184, -2), (key164, -2), (key164, 6), (key87, 2), (key148, 2), (key87, 2), (key87, -2), (key4, -2), (key87, -2), (key84, -6), (key84, 2), (key1, 2), (key84, 2)]

end MUB6.Certificate.GramRows

end OAI
end


