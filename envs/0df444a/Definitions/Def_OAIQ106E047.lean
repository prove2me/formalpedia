-- Prove2me | Definitions.Def_OAIQ106E047
-- name    : OAIQ106E047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:00:19.297991+00:00
-- url     : https://prove2.me/theorems/79ee26a9-30a7-4fd1-879f-d99a4bef8ad3
-- title:
--   Definitions bundle OAIQ106E047 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1605 declarations of OpenAI's Lean: 1605 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow14743`, `OAI.MUB6.Certificate.GramRows.rawRow14744`, `OAI.MUB6.Certificate.GramRows.rawRow14745`, `OAI.MUB6.Certificate.GramRows.rawRow14746`, `OAI.MUB6.Certificate.GramRows.rawRow14747`, `OAI.MUB6.Certificate.GramRows.rawRow14748`, `OAI.MUB6.Certificate.GramRows.rawRow14749`, `OAI.MUB6.Certificate.GramRows.rawRow1475`, `OAI.MUB6.Certificate.GramRows.rawRow14750`, `OAI.MUB6.Certificate.GramRows.rawRow14751`, `OAI.MUB6.Certificate.GramRows.rawRow14752`, `OAI.MUB6.Certificate.GramRows.rawRow14753`, `OAI.MUB6.Certificate.GramRows.rawRow14754`, `OAI.MUB6.Certificate.GramRows.rawRow14755`, `OAI.MUB6.Certificate.GramRows.rawRow14756`, `OAI.MUB6.Certificate.GramRows.rawRow14757`, `OAI.MUB6.Certificate.GramRows.rawRow14758`, `OAI.MUB6.Certificate.GramRows.rawRow14759`, `OAI.MUB6.Certificate.GramRows.rawRow1476`, `OAI.MUB6.Certificate.GramRows.rawRow14760`, `OAI.MUB6.Certificate.GramRows.rawRow14761`, `OAI.MUB6.Certificate.GramRows.rawRow14762`, `OAI.MUB6.Certificate.GramRows.rawRow14763`, `OAI.MUB6.Certificate.GramRows.rawRow14764`, `OAI.MUB6.Certificate.GramRows.rawRow14765`, `OAI.MUB6.Certificate.GramRows.rawRow14766`, `OAI.MUB6.Certificate.GramRows.rawRow14767`, `OAI.MUB6.Certificate.GramRows.rawRow14768`, `OAI.MUB6.Certificate.GramRows.rawRow14769`, `OAI.MUB6.Certificate.GramRows.rawRow1477`, `OAI.MUB6.Certificate.GramRows.rawRow14770`, `OAI.MUB6.Certificate.GramRows.rawRow14771`, `OAI.MUB6.Certificate.GramRows.rawRow14772`, `OAI.MUB6.Certificate.GramRows.rawRow14773`, `OAI.MUB6.Certificate.GramRows.rawRow14774`, `OAI.MUB6.Certificate.GramRows.rawRow14775`, `OAI.MUB6.Certificate.GramRows.rawRow14776`, `OAI.MUB6.Certificate.GramRows.rawRow14777`, `OAI.MUB6.Certificate.GramRows.rawRow14778`, `OAI.MUB6.Certificate.GramRows.rawRow14779` and 1565 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block139`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block141`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block143`, `MutuallyUnbiased_GramRows_Block144`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block146`, `MutuallyUnbiased_GramRows_Block147`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block149`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`.
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

def rawRow15 : Integer.Sparse Key := [(key319, -1), (key328, -1), (key316, 2), (key335, 1), (key340, 1), (key302, -1), (key316, -1), (key335, -2), (key305, 1), (key319, 1), (key409, 1), (key418, 1), (key406, -2), (key578, -1), (key583, -1), (key236, 1), (key406, 1), (key418, 2), (key239, -1), (key409, -1), (key442, -1), (key595, -1), (key316, 1), (key435, 1), (key450, 1), (key601, 1), (key248, -1), (key435, -1), (key328, -1), (key450, -1), (key260, 1), (key442, 1), (key469, 2), (key335, -1), (key467, -1), (key475, -2), (key267, 1), (key467, 1), (key340, 1), (key475, 1), (key271, -1), (key469, -1)]

def rawRow16 : Integer.Sparse Key := [(key328, -1), (key319, -1), (key316, 2), (key340, 1), (key335, 1), (key316, -1), (key302, -1), (key335, -2), (key319, 1), (key305, 1), (key418, 1), (key409, 1), (key406, -2), (key583, -1), (key578, -1), (key406, 1), (key236, 1), (key418, 2), (key409, -1), (key239, -1), (key595, -1), (key442, -1), (key435, 1), (key316, 1), (key601, 1), (key450, 1), (key435, -1), (key248, -1), (key450, -1), (key328, -1), (key442, 1), (key260, 1), (key469, 2), (key467, -1), (key335, -1), (key475, -2), (key467, 1), (key267, 1), (key475, 1), (key340, 1), (key469, -1), (key271, -1)]

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

def rawRow148 : Integer.Sparse Key := [(key1548, -1), (key1556, -1), (key1542, 2), (key1681, 1), (key1683, 1), (key1569, -1), (key1618, -1), (key1689, -2), (key1593, 1), (key1633, 1), (key1318, 1), (key1326, 1), (key1312, -2), (key1918, -1), (key1920, -1), (key1420, 1), (key1618, 1), (key1926, 2), (key1444, -1), (key1633, -1), (key1351, -1), (key1354, -1), (key1292, 1), (key1312, 1), (key1896, 1), (key1899, 1), (key1387, -1), (key1542, -1), (key1911, -1), (key1926, -1), (key1480, 1), (key1689, 1), (key1351, 2), (key1298, -1), (key1318, -1), (key1896, -2), (key1393, 1), (key1548, 1), (key1903, 1), (key1918, 1), (key1472, -1), (key1681, -1)]

def rawRow149 : Integer.Sparse Key := [(key1556, -1), (key1548, -1), (key1542, 2), (key1683, 1), (key1681, 1), (key1618, -1), (key1569, -1), (key1689, -2), (key1633, 1), (key1593, 1), (key1326, 1), (key1318, 1), (key1312, -2), (key1920, -1), (key1918, -1), (key1618, 1), (key1420, 1), (key1926, 2), (key1633, -1), (key1444, -1), (key1354, -1), (key1351, -1), (key1312, 1), (key1292, 1), (key1899, 1), (key1896, 1), (key1542, -1), (key1387, -1), (key1926, -1), (key1911, -1), (key1689, 1), (key1480, 1), (key1351, 2), (key1318, -1), (key1298, -1), (key1896, -2), (key1548, 1), (key1393, 1), (key1918, 1), (key1903, 1), (key1681, -1), (key1472, -1)]

def rawRow150 : Integer.Sparse Key := [(key1569, -1), (key1575, -1), (key1593, 2), (key1542, 1), (key1548, 1), (key1633, -1), (key1689, -1), (key1556, -2), (key1624, 1), (key1683, 1), (key1420, 1), (key1426, 1), (key1444, -2), (key1312, -1), (key1318, -1), (key1633, 1), (key1926, 1), (key1326, 2), (key1624, -1), (key1920, -1), (key1387, -1), (key1393, -1), (key1444, 1), (key1480, 1), (key1292, 1), (key1298, 1), (key1593, -1), (key1911, -1), (key1326, -1), (key1354, -1), (key1556, 1), (key1899, 1), (key1393, 2), (key1426, -1), (key1472, -1), (key1298, -2), (key1575, 1), (key1903, 1), (key1318, 1), (key1351, 1), (key1548, -1), (key1896, -1)]

def rawRow151 : Integer.Sparse Key := [(key1575, -1), (key1569, -1), (key1593, 2), (key1548, 1), (key1542, 1), (key1689, -1), (key1633, -1), (key1556, -2), (key1683, 1), (key1624, 1), (key1426, 1), (key1420, 1), (key1444, -2), (key1318, -1), (key1312, -1), (key1926, 1), (key1633, 1), (key1326, 2), (key1920, -1), (key1624, -1), (key1393, -1), (key1387, -1), (key1480, 1), (key1444, 1), (key1298, 1), (key1292, 1), (key1911, -1), (key1593, -1), (key1354, -1), (key1326, -1), (key1899, 1), (key1556, 1), (key1393, 2), (key1472, -1), (key1426, -1), (key1298, -2), (key1903, 1), (key1575, 1), (key1351, 1), (key1318, 1), (key1896, -1), (key1548, -1)]

def rawRow152 : Integer.Sparse Key := [(key1575, -1), (key1593, -1), (key1569, 2), (key1681, 1), (key1689, 1), (key1542, -1), (key1618, -1), (key1683, -2), (key1556, 1), (key1624, 1), (key1426, 1), (key1444, 1), (key1420, -2), (key1918, -1), (key1926, -1), (key1312, 1), (key1618, 1), (key1920, 2), (key1326, -1), (key1624, -1), (key1472, -1), (key1480, -1), (key1387, 1), (key1420, 1), (key1903, 1), (key1911, 1), (key1292, -1), (key1569, -1), (key1899, -1), (key1920, -1), (key1354, 1), (key1683, 1), (key1472, 2), (key1393, -1), (key1426, -1), (key1903, -2), (key1298, 1), (key1575, 1), (key1896, 1), (key1918, 1), (key1351, -1), (key1681, -1)]

def rawRow153 : Integer.Sparse Key := [(key1593, -1), (key1575, -1), (key1569, 2), (key1689, 1), (key1681, 1), (key1618, -1), (key1542, -1), (key1683, -2), (key1624, 1), (key1556, 1), (key1444, 1), (key1426, 1), (key1420, -2), (key1926, -1), (key1918, -1), (key1618, 1), (key1312, 1), (key1920, 2), (key1624, -1), (key1326, -1), (key1480, -1), (key1472, -1), (key1420, 1), (key1387, 1), (key1911, 1), (key1903, 1), (key1569, -1), (key1292, -1), (key1920, -1), (key1899, -1), (key1683, 1), (key1354, 1), (key1472, 2), (key1426, -1), (key1393, -1), (key1903, -2), (key1575, 1), (key1298, 1), (key1918, 1), (key1896, 1), (key1681, -1), (key1351, -1)]

def rawRow154 : Integer.Sparse Key := [(key1681, -1), (key1683, -1), (key1689, 2), (key1548, 1), (key1556, 1), (key1593, -1), (key1633, -1), (key1542, -2), (key1569, 1), (key1618, 1), (key1918, 1), (key1920, 1), (key1926, -2), (key1318, -1), (key1326, -1), (key1444, 1), (key1633, 1), (key1312, 2), (key1420, -1), (key1618, -1), (key1896, -1), (key1899, -1), (key1911, 1), (key1926, 1), (key1351, 1), (key1354, 1), (key1480, -1), (key1689, -1), (key1292, -1), (key1312, -1), (key1387, 1), (key1542, 1), (key1896, 2), (key1903, -1), (key1918, -1), (key1351, -2), (key1472, 1), (key1681, 1), (key1298, 1), (key1318, 1), (key1393, -1), (key1548, -1)]

def rawRow155 : Integer.Sparse Key := [(key1683, -1), (key1681, -1), (key1689, 2), (key1556, 1), (key1548, 1), (key1633, -1), (key1593, -1), (key1542, -2), (key1618, 1), (key1569, 1), (key1920, 1), (key1918, 1), (key1926, -2), (key1326, -1), (key1318, -1), (key1633, 1), (key1444, 1), (key1312, 2), (key1618, -1), (key1420, -1), (key1899, -1), (key1896, -1), (key1926, 1), (key1911, 1), (key1354, 1), (key1351, 1), (key1689, -1), (key1480, -1), (key1312, -1), (key1292, -1), (key1542, 1), (key1387, 1), (key1896, 2), (key1918, -1), (key1903, -1), (key1351, -2), (key1681, 1), (key1472, 1), (key1318, 1), (key1298, 1), (key1548, -1), (key1393, -1)]

def rawRow156 : Integer.Sparse Key := [(key1681, -1), (key1689, -1), (key1683, 2), (key1575, 1), (key1593, 1), (key1556, -1), (key1624, -1), (key1569, -2), (key1542, 1), (key1618, 1), (key1918, 1), (key1926, 1), (key1920, -2), (key1426, -1), (key1444, -1), (key1326, 1), (key1624, 1), (key1420, 2), (key1312, -1), (key1618, -1), (key1903, -1), (key1911, -1), (key1899, 1), (key1920, 1), (key1472, 1), (key1480, 1), (key1354, -1), (key1683, -1), (key1387, -1), (key1420, -1), (key1292, 1), (key1569, 1), (key1903, 2), (key1896, -1), (key1918, -1), (key1472, -2), (key1351, 1), (key1681, 1), (key1393, 1), (key1426, 1), (key1298, -1), (key1575, -1)]

def rawRow157 : Integer.Sparse Key := [(key1689, -1), (key1681, -1), (key1683, 2), (key1593, 1), (key1575, 1), (key1624, -1), (key1556, -1), (key1569, -2), (key1618, 1), (key1542, 1), (key1926, 1), (key1918, 1), (key1920, -2), (key1444, -1), (key1426, -1), (key1624, 1), (key1326, 1), (key1420, 2), (key1618, -1), (key1312, -1), (key1911, -1), (key1903, -1), (key1920, 1), (key1899, 1), (key1480, 1), (key1472, 1), (key1683, -1), (key1354, -1), (key1420, -1), (key1387, -1), (key1569, 1), (key1292, 1), (key1903, 2), (key1918, -1), (key1896, -1), (key1472, -2), (key1681, 1), (key1351, 1), (key1426, 1), (key1393, 1), (key1575, -1), (key1298, -1)]

def rawRow158 : Integer.Sparse Key := [(key1896, -1), (key1896, -1), (key1899, 2), (key1903, 1), (key1903, 1), (key1920, -1), (key1920, -1), (key1911, -2), (key1926, 1), (key1926, 1), (key1351, 1), (key1351, 1), (key1354, -2), (key1472, -1), (key1472, -1), (key1683, 1), (key1683, 1), (key1480, 2), (key1689, -1), (key1689, -1), (key1298, -1), (key1298, -1), (key1326, 1), (key1326, 1), (key1393, 1), (key1393, 1), (key1556, -1), (key1556, -1), (key1444, -1), (key1444, -1), (key1593, 1), (key1593, 1), (key1292, 2), (key1312, -1), (key1312, -1), (key1387, -2), (key1542, 1), (key1542, 1), (key1420, 1), (key1420, 1), (key1569, -1), (key1569, -1)]

def rawRow159 : Integer.Sparse Key := [(key1896, -1), (key1899, -1), (key1896, 2), (key1918, 1), (key1920, 1), (key1903, -1), (key1918, -1), (key1926, -2), (key1911, 1), (key1926, 1), (key1351, 1), (key1354, 1), (key1351, -2), (key1681, -1), (key1683, -1), (key1472, 1), (key1681, 1), (key1689, 2), (key1480, -1), (key1689, -1), (key1318, -1), (key1326, -1), (key1298, 1), (key1318, 1), (key1548, 1), (key1556, 1), (key1393, -1), (key1548, -1), (key1593, -1), (key1633, -1), (key1444, 1), (key1633, 1), (key1312, 2), (key1292, -1), (key1312, -1), (key1542, -2), (key1387, 1), (key1542, 1), (key1569, 1), (key1618, 1), (key1420, -1), (key1618, -1)]

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

def rawRow14743 : Integer.Sparse Key := [(key1506, 4), (key1501, 4), (key1501, 4), (key1506, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1735, -4), (key1733, -4), (key1735, 12)]

def rawRow14744 : Integer.Sparse Key := [(key1506, 4), (key1506, 4), (key1506, 4), (key1501, -4), (key1501, -4), (key1501, -4), (key1735, -4), (key1735, -4), (key1735, -4), (key1733, 12)]

def rawRow14745 : Integer.Sparse Key := [(key1501, 4), (key1501, 4), (key1506, 4), (key1733, -4), (key1735, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1506, -4), (key1735, 12)]

def rawRow14746 : Integer.Sparse Key := [(key1501, 4), (key1506, 4), (key1501, 4), (key1735, -4), (key1733, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1506, -4), (key1735, 12)]

def rawRow14747 : Integer.Sparse Key := [(key1506, 4), (key1501, 4), (key1501, 4), (key1735, -4), (key1735, -4), (key1733, -4), (key1506, -4), (key1506, -4), (key1501, -4), (key1735, 12)]

def rawRow14748 : Integer.Sparse Key := [(key1501, 4), (key1733, 4), (key1735, 4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1506, 12)]

def rawRow14749 : Integer.Sparse Key := [(key1501, 4), (key1735, 4), (key1733, 4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, 12)]

def rawRow14750 : Integer.Sparse Key := [(key1733, 4), (key1501, 4), (key1735, 4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1506, 12)]

def rawRow14751 : Integer.Sparse Key := [(key1733, 4), (key1735, 4), (key1501, 4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1506, 12)]

def rawRow14752 : Integer.Sparse Key := [(key1735, 4), (key1501, 4), (key1733, 4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, 12)]

def rawRow14753 : Integer.Sparse Key := [(key1735, 4), (key1733, 4), (key1501, 4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1506, 12)]

def rawRow14754 : Integer.Sparse Key := [(key1506, 4), (key1735, 4), (key1735, 4), (key1501, -4), (key1501, -4), (key1733, -4), (key1506, -4), (key1506, -4), (key1735, -4), (key1501, 12)]

def rawRow14755 : Integer.Sparse Key := [(key1735, 4), (key1506, 4), (key1735, 4), (key1501, -4), (key1733, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1506, -4), (key1501, 12)]

def rawRow14756 : Integer.Sparse Key := [(key1735, 4), (key1735, 4), (key1506, 4), (key1733, -4), (key1501, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1506, -4), (key1501, 12)]

def rawRow14757 : Integer.Sparse Key := [(key1506, 4), (key1506, 4), (key1506, 4), (key1735, -4), (key1735, -4), (key1735, -4), (key1501, -4), (key1501, -4), (key1501, -4), (key1733, 12)]

def rawRow14758 : Integer.Sparse Key := [(key1506, 4), (key1735, 4), (key1735, 4), (key1506, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1501, -4), (key1733, -4), (key1501, 12)]

def rawRow14759 : Integer.Sparse Key := [(key1735, 4), (key1506, 4), (key1735, 4), (key1506, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1733, -4), (key1501, -4), (key1501, 12)]

def rawRow14760 : Integer.Sparse Key := [(key1735, 4), (key1735, 4), (key1506, 4), (key1735, -4), (key1506, -4), (key1506, -4), (key1733, -4), (key1501, -4), (key1501, -4), (key1501, 12)]

def rawRow14761 : Integer.Sparse Key := [(key1274, -2), (key1278, -2), (key1278, -2), (key1278, 6), (key1697, -2), (key1701, -2), (key1701, -2), (key1697, 2), (key1701, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1701, -2), (key1701, -2), (key1751, -2), (key1852, 6), (key1852, -2), (key1852, -2), (key1884, -2)]

def rawRow14762 : Integer.Sparse Key := [(key1278, -2), (key1274, -2), (key1278, -2), (key1278, 6), (key1701, -2), (key1697, -2), (key1701, -2), (key1701, 2), (key1697, 2), (key1751, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1701, -2), (key1751, -2), (key1701, -2), (key1852, 6), (key1852, -2), (key1884, -2), (key1852, -2)]

def rawRow14763 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1274, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1697, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1697, 2), (key1697, 2), (key1751, -2), (key1701, -2), (key1701, -2), (key1852, 6), (key1884, -2), (key1852, -2), (key1852, -2)]

def rawRow14764 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1278, -2), (key1274, 6), (key1751, -2), (key1751, -2), (key1751, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1697, -2), (key1697, -2), (key1697, -2), (key1884, 6), (key1852, -2), (key1852, -2), (key1852, -2)]

def rawRow14765 : Integer.Sparse Key := [(key1697, -2), (key1701, -2), (key1701, -2), (key1852, 6), (key1274, -2), (key1278, -2), (key1278, -2), (key1697, 2), (key1701, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1852, -2), (key1852, -2), (key1884, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1751, -2)]

def rawRow14766 : Integer.Sparse Key := [(key1701, -2), (key1697, -2), (key1701, -2), (key1852, 6), (key1278, -2), (key1274, -2), (key1278, -2), (key1701, 2), (key1697, 2), (key1751, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1852, -2), (key1884, -2), (key1852, -2), (key1278, 6), (key1701, -2), (key1751, -2), (key1701, -2)]

def rawRow14767 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1697, -2), (key1852, 6), (key1278, -2), (key1278, -2), (key1274, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1697, 2), (key1697, 2), (key1884, -2), (key1852, -2), (key1852, -2), (key1278, 6), (key1751, -2), (key1701, -2), (key1701, -2)]

def rawRow14768 : Integer.Sparse Key := [(key1697, -2), (key1701, -2), (key1852, -2), (key1701, 6), (key1697, -2), (key1701, -2), (key1852, -2), (key1274, 2), (key1278, 2), (key1697, 2), (key1751, 2), (key1852, 2), (key1884, 2), (key1278, -2), (key1701, -2), (key1751, -2), (key1701, 6), (key1278, -2), (key1701, -2), (key1751, -2)]

def rawRow14769 : Integer.Sparse Key := [(key1701, -2), (key1697, -2), (key1852, -2), (key1701, 6), (key1701, -2), (key1697, -2), (key1852, -2), (key1278, 2), (key1274, 2), (key1751, 2), (key1697, 2), (key1884, 2), (key1852, 2), (key1278, -2), (key1751, -2), (key1701, -2), (key1701, 6), (key1278, -2), (key1751, -2), (key1701, -2)]

def rawRow14770 : Integer.Sparse Key := [(key1697, -2), (key1852, -2), (key1701, -2), (key1701, 6), (key1697, -2), (key1852, -2), (key1701, -2), (key1697, 2), (key1852, 2), (key1274, 2), (key1884, 2), (key1278, 2), (key1751, 2), (key1701, -2), (key1278, -2), (key1751, -2), (key1701, 6), (key1701, -2), (key1278, -2), (key1751, -2)]

def rawRow14771 : Integer.Sparse Key := [(key1852, -2), (key1697, -2), (key1701, -2), (key1701, 6), (key1852, -2), (key1697, -2), (key1701, -2), (key1852, 2), (key1697, 2), (key1884, 2), (key1274, 2), (key1751, 2), (key1278, 2), (key1701, -2), (key1751, -2), (key1278, -2), (key1701, 6), (key1701, -2), (key1751, -2), (key1278, -2)]

def rawRow14772 : Integer.Sparse Key := [(key1701, -2), (key1852, -2), (key1697, -2), (key1701, 6), (key1701, -2), (key1852, -2), (key1697, -2), (key1751, 2), (key1884, 2), (key1278, 2), (key1852, 2), (key1274, 2), (key1697, 2), (key1751, -2), (key1278, -2), (key1701, -2), (key1701, 6), (key1751, -2), (key1278, -2), (key1701, -2)]

def rawRow14773 : Integer.Sparse Key := [(key1852, -2), (key1701, -2), (key1697, -2), (key1701, 6), (key1852, -2), (key1701, -2), (key1697, -2), (key1884, 2), (key1751, 2), (key1852, 2), (key1278, 2), (key1697, 2), (key1274, 2), (key1751, -2), (key1701, -2), (key1278, -2), (key1701, 6), (key1751, -2), (key1701, -2), (key1278, -2)]

def rawRow14774 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1852, -2), (key1697, 6), (key1751, -2), (key1751, -2), (key1884, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1852, 2), (key1852, 2), (key1274, -2), (key1697, -2), (key1697, -2), (key1751, 6), (key1278, -2), (key1701, -2), (key1701, -2)]

def rawRow14775 : Integer.Sparse Key := [(key1701, -2), (key1852, -2), (key1701, -2), (key1697, 6), (key1751, -2), (key1884, -2), (key1751, -2), (key1701, 2), (key1852, 2), (key1278, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1697, -2), (key1274, -2), (key1697, -2), (key1751, 6), (key1701, -2), (key1278, -2), (key1701, -2)]

def rawRow14776 : Integer.Sparse Key := [(key1852, -2), (key1701, -2), (key1701, -2), (key1697, 6), (key1884, -2), (key1751, -2), (key1751, -2), (key1852, 2), (key1701, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1697, -2), (key1697, -2), (key1274, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1278, -2)]

def rawRow14777 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1751, -2), (key1884, 6), (key1278, -2), (key1278, -2), (key1278, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1852, -2), (key1852, -2), (key1852, -2), (key1274, 6), (key1697, -2), (key1697, -2), (key1697, -2)]

def rawRow14778 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1884, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1852, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1852, 2), (key1852, 2), (key1278, -2), (key1701, -2), (key1701, -2), (key1697, 6), (key1274, -2), (key1697, -2), (key1697, -2)]

def rawRow14779 : Integer.Sparse Key := [(key1751, -2), (key1884, -2), (key1751, -2), (key1751, 6), (key1701, -2), (key1852, -2), (key1701, -2), (key1701, 2), (key1852, 2), (key1278, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1701, -2), (key1278, -2), (key1701, -2), (key1697, 6), (key1697, -2), (key1274, -2), (key1697, -2)]

def rawRow14780 : Integer.Sparse Key := [(key1884, -2), (key1751, -2), (key1751, -2), (key1751, 6), (key1852, -2), (key1701, -2), (key1701, -2), (key1852, 2), (key1701, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1701, -2), (key1701, -2), (key1278, -2), (key1697, 6), (key1697, -2), (key1697, -2), (key1274, -2)]

def rawRow14781 : Integer.Sparse Key := [(key358, 4), (key358, 4), (key363, 4), (key358, -4), (key363, -4), (key363, -4), (key528, -4), (key532, -4), (key532, -4), (key532, 12)]

def rawRow14782 : Integer.Sparse Key := [(key358, 4), (key363, 4), (key358, 4), (key363, -4), (key358, -4), (key363, -4), (key532, -4), (key528, -4), (key532, -4), (key532, 12)]

def rawRow14783 : Integer.Sparse Key := [(key363, 4), (key358, 4), (key358, 4), (key363, -4), (key363, -4), (key358, -4), (key532, -4), (key532, -4), (key528, -4), (key532, 12)]

def rawRow14784 : Integer.Sparse Key := [(key363, 4), (key363, 4), (key363, 4), (key358, -4), (key358, -4), (key358, -4), (key532, -4), (key532, -4), (key532, -4), (key528, 12)]

def rawRow14785 : Integer.Sparse Key := [(key358, 4), (key358, 4), (key363, 4), (key528, -4), (key532, -4), (key532, -4), (key358, -4), (key363, -4), (key363, -4), (key532, 12)]

def rawRow14786 : Integer.Sparse Key := [(key358, 4), (key363, 4), (key358, 4), (key532, -4), (key528, -4), (key532, -4), (key363, -4), (key358, -4), (key363, -4), (key532, 12)]

def rawRow14787 : Integer.Sparse Key := [(key363, 4), (key358, 4), (key358, 4), (key532, -4), (key532, -4), (key528, -4), (key363, -4), (key363, -4), (key358, -4), (key532, 12)]

def rawRow14788 : Integer.Sparse Key := [(key358, 4), (key528, 4), (key532, 4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key363, 12)]

def rawRow14789 : Integer.Sparse Key := [(key358, 4), (key532, 4), (key528, 4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, 12)]

def rawRow14790 : Integer.Sparse Key := [(key528, 4), (key358, 4), (key532, 4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key363, 12)]

def rawRow14791 : Integer.Sparse Key := [(key528, 4), (key532, 4), (key358, 4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key363, 12)]

def rawRow14792 : Integer.Sparse Key := [(key532, 4), (key358, 4), (key528, 4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, 12)]

def rawRow14793 : Integer.Sparse Key := [(key532, 4), (key528, 4), (key358, 4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key363, 12)]

def rawRow14794 : Integer.Sparse Key := [(key363, 4), (key532, 4), (key532, 4), (key358, -4), (key358, -4), (key528, -4), (key363, -4), (key363, -4), (key532, -4), (key358, 12)]

def rawRow14795 : Integer.Sparse Key := [(key532, 4), (key363, 4), (key532, 4), (key358, -4), (key528, -4), (key358, -4), (key363, -4), (key532, -4), (key363, -4), (key358, 12)]

def rawRow14796 : Integer.Sparse Key := [(key532, 4), (key532, 4), (key363, 4), (key528, -4), (key358, -4), (key358, -4), (key532, -4), (key363, -4), (key363, -4), (key358, 12)]

def rawRow14797 : Integer.Sparse Key := [(key363, 4), (key363, 4), (key363, 4), (key532, -4), (key532, -4), (key532, -4), (key358, -4), (key358, -4), (key358, -4), (key528, 12)]

def rawRow14798 : Integer.Sparse Key := [(key363, 4), (key532, 4), (key532, 4), (key363, -4), (key363, -4), (key532, -4), (key358, -4), (key358, -4), (key528, -4), (key358, 12)]

def rawRow14799 : Integer.Sparse Key := [(key532, 4), (key363, 4), (key532, 4), (key363, -4), (key532, -4), (key363, -4), (key358, -4), (key528, -4), (key358, -4), (key358, 12)]

def rawRow14800 : Integer.Sparse Key := [(key532, 4), (key532, 4), (key363, 4), (key532, -4), (key363, -4), (key363, -4), (key528, -4), (key358, -4), (key358, -4), (key358, 12)]

def rawRow14801 : Integer.Sparse Key := [(key1485, -1), (key1490, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1711, -1), (key1716, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1711, 2), (key1723, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, -1), (key1867, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1877, -1)]

def rawRow14802 : Integer.Sparse Key := [(key1490, -1), (key1485, -1), (key1513, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, -1), (key1711, -1), (key1741, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1723, 2), (key1711, 2), (key1741, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, -1), (key1861, -1), (key1877, -1), (key1861, -1), (key1877, -1), (key1867, -1)]

def rawRow14803 : Integer.Sparse Key := [(key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1485, -1), (key1485, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1711, -1), (key1711, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1711, 2), (key1711, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, -1), (key1877, -1), (key1867, -1), (key1867, -1), (key1861, -1), (key1861, -1)]

def rawRow14804 : Integer.Sparse Key := [(key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1485, 2), (key1485, 2), (key1485, 2), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1)]

def rawRow14805 : Integer.Sparse Key := [(key1711, -1), (key1716, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1861, 2), (key1861, 2), (key1877, 2), (key1485, -1), (key1490, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1711, 2), (key1723, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1861, -1), (key1867, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1877, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1)]

def rawRow14806 : Integer.Sparse Key := [(key1716, -1), (key1711, -1), (key1741, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1861, 2), (key1877, 2), (key1861, 2), (key1490, -1), (key1485, -1), (key1513, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1723, 2), (key1711, 2), (key1741, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1867, -1), (key1861, -1), (key1877, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1)]

def rawRow14807 : Integer.Sparse Key := [(key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1711, -1), (key1711, -1), (key1877, 2), (key1861, 2), (key1861, 2), (key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1485, -1), (key1485, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1711, 2), (key1711, 2), (key1877, -1), (key1877, -1), (key1867, -1), (key1867, -1), (key1861, -1), (key1861, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1)]

def rawRow14808 : Integer.Sparse Key := [(key1359, -1), (key1364, -1), (key1711, -1), (key1741, -1), (key1861, -1), (key1877, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1359, -1), (key1364, -1), (key1711, -1), (key1741, -1), (key1861, -1), (key1877, -1), (key1359, 2), (key1374, 2), (key1485, 2), (key1513, 2), (key1867, 2), (key1877, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1)]

def rawRow14809 : Integer.Sparse Key := [(key1364, -1), (key1359, -1), (key1741, -1), (key1711, -1), (key1877, -1), (key1861, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, -1), (key1359, -1), (key1741, -1), (key1711, -1), (key1877, -1), (key1861, -1), (key1374, 2), (key1359, 2), (key1513, 2), (key1485, 2), (key1877, 2), (key1867, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1)]

def rawRow14810 : Integer.Sparse Key := [(key1711, -1), (key1861, -1), (key1359, -1), (key1877, -1), (key1364, -1), (key1741, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1711, -1), (key1861, -1), (key1359, -1), (key1877, -1), (key1364, -1), (key1741, -1), (key1485, 2), (key1867, 2), (key1359, 2), (key1877, 2), (key1374, 2), (key1513, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1)]

def rawRow14811 : Integer.Sparse Key := [(key1861, -1), (key1711, -1), (key1877, -1), (key1359, -1), (key1741, -1), (key1364, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1861, -1), (key1711, -1), (key1877, -1), (key1359, -1), (key1741, -1), (key1364, -1), (key1867, 2), (key1485, 2), (key1877, 2), (key1359, 2), (key1513, 2), (key1374, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1)]

def rawRow14812 : Integer.Sparse Key := [(key1741, -1), (key1877, -1), (key1364, -1), (key1861, -1), (key1359, -1), (key1711, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, -1), (key1877, -1), (key1364, -1), (key1861, -1), (key1359, -1), (key1711, -1), (key1513, 2), (key1877, 2), (key1374, 2), (key1867, 2), (key1359, 2), (key1485, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1)]

def rawRow14813 : Integer.Sparse Key := [(key1877, -1), (key1741, -1), (key1861, -1), (key1364, -1), (key1711, -1), (key1359, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1877, -1), (key1741, -1), (key1861, -1), (key1364, -1), (key1711, -1), (key1359, -1), (key1877, 2), (key1513, 2), (key1867, 2), (key1374, 2), (key1485, 2), (key1359, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1)]

def rawRow14814 : Integer.Sparse Key := [(key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1861, -1), (key1861, -1), (key1359, 2), (key1711, 2), (key1711, 2), (key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1867, -1), (key1867, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1861, 2), (key1861, 2), (key1359, -1), (key1359, -1), (key1485, -1), (key1485, -1), (key1711, -1), (key1711, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1)]

def rawRow14815 : Integer.Sparse Key := [(key1716, -1), (key1861, -1), (key1364, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1711, 2), (key1359, 2), (key1711, 2), (key1723, -1), (key1867, -1), (key1374, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1490, 2), (key1861, 2), (key1364, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1485, -1), (key1711, -1), (key1359, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1)]

def rawRow14816 : Integer.Sparse Key := [(key1861, -1), (key1716, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1711, 2), (key1711, 2), (key1359, 2), (key1867, -1), (key1723, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1861, 2), (key1490, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1711, -1), (key1485, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1359, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1)]

def rawRow14817 : Integer.Sparse Key := [(key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1867, 2), (key1867, 2), (key1867, 2), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1485, 2), (key1485, 2), (key1485, 2), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1)]

def rawRow14818 : Integer.Sparse Key := [(key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1867, -1), (key1867, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1861, -1), (key1861, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1861, 2), (key1861, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, -1), (key1359, -1), (key1485, -1), (key1485, -1), (key1711, -1), (key1711, -1)]

def rawRow14819 : Integer.Sparse Key := [(key1723, -1), (key1867, -1), (key1374, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, -1), (key1861, -1), (key1364, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1490, 2), (key1861, 2), (key1364, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1711, 2), (key1359, 2), (key1711, 2), (key1485, -1), (key1711, -1), (key1359, -1), (key1711, -1), (key1359, -1), (key1485, -1)]

def rawRow14820 : Integer.Sparse Key := [(key1867, -1), (key1723, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1861, -1), (key1716, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1861, 2), (key1490, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1), (key1711, 2), (key1711, 2), (key1359, 2), (key1711, -1), (key1485, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1359, -1)]

def rawRow14821 : Integer.Sparse Key := [(key288, -2), (key289, -2), (key289, -2), (key289, 6), (key513, -2), (key515, -2), (key515, -2), (key513, 2), (key515, 2), (key513, 2), (key547, 2), (key515, 2), (key547, 2), (key515, -2), (key515, -2), (key547, -2), (key670, 6), (key670, -2), (key670, -2), (key680, -2)]

def rawRow14822 : Integer.Sparse Key := [(key289, -2), (key288, -2), (key289, -2), (key289, 6), (key515, -2), (key513, -2), (key515, -2), (key515, 2), (key513, 2), (key547, 2), (key513, 2), (key547, 2), (key515, 2), (key515, -2), (key547, -2), (key515, -2), (key670, 6), (key670, -2), (key680, -2), (key670, -2)]

def rawRow14823 : Integer.Sparse Key := [(key289, -2), (key289, -2), (key288, -2), (key289, 6), (key515, -2), (key515, -2), (key513, -2), (key547, 2), (key547, 2), (key515, 2), (key515, 2), (key513, 2), (key513, 2), (key547, -2), (key515, -2), (key515, -2), (key670, 6), (key680, -2), (key670, -2), (key670, -2)]

def rawRow14824 : Integer.Sparse Key := [(key289, -2), (key289, -2), (key289, -2), (key288, 6), (key547, -2), (key547, -2), (key547, -2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key513, -2), (key513, -2), (key513, -2), (key680, 6), (key670, -2), (key670, -2), (key670, -2)]

def rawRow14825 : Integer.Sparse Key := [(key513, -2), (key515, -2), (key515, -2), (key547, 6), (key288, -2), (key289, -2), (key289, -2), (key513, 2), (key515, 2), (key513, 2), (key547, 2), (key515, 2), (key547, 2), (key670, -2), (key670, -2), (key680, -2), (key289, 6), (key515, -2), (key515, -2), (key547, -2)]

def rawRow14826 : Integer.Sparse Key := [(key515, -2), (key513, -2), (key515, -2), (key547, 6), (key289, -2), (key288, -2), (key289, -2), (key515, 2), (key513, 2), (key547, 2), (key513, 2), (key547, 2), (key515, 2), (key670, -2), (key680, -2), (key670, -2), (key289, 6), (key515, -2), (key547, -2), (key515, -2)]

def rawRow14827 : Integer.Sparse Key := [(key515, -2), (key515, -2), (key513, -2), (key547, 6), (key289, -2), (key289, -2), (key288, -2), (key547, 2), (key547, 2), (key515, 2), (key515, 2), (key513, 2), (key513, 2), (key680, -2), (key670, -2), (key670, -2), (key289, 6), (key547, -2), (key515, -2), (key515, -2)]

def rawRow14828 : Integer.Sparse Key := [(key513, -2), (key515, -2), (key547, -2), (key515, 6), (key513, -2), (key515, -2), (key547, -2), (key288, 2), (key289, 2), (key513, 2), (key547, 2), (key670, 2), (key680, 2), (key289, -2), (key515, -2), (key547, -2), (key515, 6), (key289, -2), (key515, -2), (key547, -2)]

def rawRow14829 : Integer.Sparse Key := [(key515, -2), (key513, -2), (key547, -2), (key515, 6), (key515, -2), (key513, -2), (key547, -2), (key289, 2), (key288, 2), (key547, 2), (key513, 2), (key680, 2), (key670, 2), (key289, -2), (key547, -2), (key515, -2), (key515, 6), (key289, -2), (key547, -2), (key515, -2)]

def rawRow14830 : Integer.Sparse Key := [(key513, -2), (key547, -2), (key515, -2), (key515, 6), (key513, -2), (key547, -2), (key515, -2), (key513, 2), (key547, 2), (key288, 2), (key680, 2), (key289, 2), (key547, 2), (key515, -2), (key289, -2), (key547, -2), (key515, 6), (key515, -2), (key289, -2), (key547, -2)]

def rawRow14831 : Integer.Sparse Key := [(key547, -2), (key513, -2), (key515, -2), (key515, 6), (key547, -2), (key513, -2), (key515, -2), (key547, 2), (key513, 2), (key680, 2), (key288, 2), (key547, 2), (key289, 2), (key515, -2), (key547, -2), (key289, -2), (key515, 6), (key515, -2), (key547, -2), (key289, -2)]

def rawRow14832 : Integer.Sparse Key := [(key515, -2), (key547, -2), (key513, -2), (key515, 6), (key515, -2), (key547, -2), (key513, -2), (key670, 2), (key680, 2), (key289, 2), (key547, 2), (key288, 2), (key513, 2), (key547, -2), (key289, -2), (key515, -2), (key515, 6), (key547, -2), (key289, -2), (key515, -2)]

def rawRow14833 : Integer.Sparse Key := [(key547, -2), (key515, -2), (key513, -2), (key515, 6), (key547, -2), (key515, -2), (key513, -2), (key680, 2), (key670, 2), (key547, 2), (key289, 2), (key513, 2), (key288, 2), (key547, -2), (key515, -2), (key289, -2), (key515, 6), (key547, -2), (key515, -2), (key289, -2)]

def rawRow14834 : Integer.Sparse Key := [(key515, -2), (key515, -2), (key547, -2), (key513, 6), (key670, -2), (key670, -2), (key680, -2), (key289, 2), (key289, 2), (key515, 2), (key515, 2), (key547, 2), (key547, 2), (key288, -2), (key513, -2), (key513, -2), (key547, 6), (key289, -2), (key515, -2), (key515, -2)]

def rawRow14835 : Integer.Sparse Key := [(key515, -2), (key547, -2), (key515, -2), (key513, 6), (key670, -2), (key680, -2), (key670, -2), (key515, 2), (key547, 2), (key289, 2), (key547, 2), (key289, 2), (key515, 2), (key513, -2), (key288, -2), (key513, -2), (key547, 6), (key515, -2), (key289, -2), (key515, -2)]

def rawRow14836 : Integer.Sparse Key := [(key547, -2), (key515, -2), (key515, -2), (key513, 6), (key680, -2), (key670, -2), (key670, -2), (key547, 2), (key515, 2), (key547, 2), (key289, 2), (key515, 2), (key289, 2), (key513, -2), (key513, -2), (key288, -2), (key547, 6), (key515, -2), (key515, -2), (key289, -2)]

def rawRow14837 : Integer.Sparse Key := [(key670, -2), (key670, -2), (key670, -2), (key680, 6), (key289, -2), (key289, -2), (key289, -2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key547, -2), (key547, -2), (key547, -2), (key288, 6), (key513, -2), (key513, -2), (key513, -2)]

def rawRow14838 : Integer.Sparse Key := [(key670, -2), (key670, -2), (key680, -2), (key670, 6), (key515, -2), (key515, -2), (key547, -2), (key289, 2), (key289, 2), (key515, 2), (key515, 2), (key547, 2), (key547, 2), (key289, -2), (key515, -2), (key515, -2), (key513, 6), (key288, -2), (key513, -2), (key513, -2)]

def rawRow14839 : Integer.Sparse Key := [(key670, -2), (key680, -2), (key670, -2), (key670, 6), (key515, -2), (key547, -2), (key515, -2), (key515, 2), (key547, 2), (key289, 2), (key547, 2), (key289, 2), (key515, 2), (key515, -2), (key289, -2), (key515, -2), (key513, 6), (key513, -2), (key288, -2), (key513, -2)]

def rawRow14840 : Integer.Sparse Key := [(key680, -2), (key670, -2), (key670, -2), (key670, 6), (key547, -2), (key515, -2), (key515, -2), (key547, 2), (key515, 2), (key547, 2), (key289, 2), (key515, 2), (key289, 2), (key515, -2), (key515, -2), (key289, -2), (key513, 6), (key513, -2), (key513, -2), (key288, -2)]

def rawRow14841 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow14842 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow14843 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow14844 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2525, 4), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow14845 : Integer.Sparse Key := [(key2460, 4), (key2525, 4), (key2460, 4), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow14846 : Integer.Sparse Key := [(key2525, 4), (key2460, 4), (key2460, 4), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow14847 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2533, 4), (key2564, 4), (key2564, 4)]

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

def rawRow14848 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow14849 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow14850 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2533, 4), (key2521, -2), (key2525, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2564, -2), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow14851 : Integer.Sparse Key := [(key2460, 4), (key2533, 4), (key2460, 4), (key2525, -2), (key2521, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow14852 : Integer.Sparse Key := [(key2533, 4), (key2460, 4), (key2460, 4), (key2564, -2), (key2564, -2), (key2525, -2), (key2525, -2), (key2521, -2), (key2521, -2), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow14853 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key984, -2), (key984, 6), (key1090, -2), (key1090, -2), (key1098, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, -2), (key1183, -2), (key1183, -2), (key1169, 6), (key1169, -2), (key1220, -2), (key1220, -2)]

def rawRow14854 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key976, -2), (key984, 6), (key1090, -2), (key1098, -2), (key1090, -2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1183, -2), (key1098, -2), (key1183, -2), (key1169, 6), (key1220, -2), (key1169, -2), (key1220, -2)]

def rawRow14855 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key976, -2), (key984, 6), (key1098, -2), (key1090, -2), (key1090, -2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1098, -2), (key1169, 6), (key1220, -2), (key1220, -2), (key1169, -2)]

def rawRow14856 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key984, -2), (key976, 6), (key1180, -2), (key1183, -2), (key1183, -2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1220, 6), (key1169, -2), (key1169, -2), (key1220, -2)]

def rawRow14857 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key984, -2), (key976, 6), (key1183, -2), (key1180, -2), (key1183, -2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1220, 6), (key1169, -2), (key1220, -2), (key1169, -2)]

def rawRow14858 : Integer.Sparse Key := [(key984, -2), (key984, -2), (key976, -2), (key976, 6), (key1183, -2), (key1183, -2), (key1180, -2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1220, 6), (key1220, -2), (key1169, -2), (key1169, -2)]

def rawRow14859 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1098, -2), (key1169, 6), (key976, -2), (key976, -2), (key984, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1169, -2), (key1220, -2), (key1220, -2), (key984, 6), (key1098, -2), (key1183, -2), (key1183, -2)]

def rawRow14860 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1090, -2), (key1169, 6), (key976, -2), (key984, -2), (key976, -2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, -2), (key1169, -2), (key1220, -2), (key984, 6), (key1183, -2), (key1098, -2), (key1183, -2)]

def rawRow14861 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1090, -2), (key1169, 6), (key984, -2), (key976, -2), (key976, -2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1220, -2), (key1220, -2), (key1169, -2), (key984, 6), (key1183, -2), (key1183, -2), (key1098, -2)]

def rawRow14862 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1169, -2), (key1090, 6), (key1180, -2), (key1183, -2), (key1220, -2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1183, 6), (key984, -2), (key1098, -2), (key1183, -2)]

def rawRow14863 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1169, -2), (key1090, 6), (key1183, -2), (key1180, -2), (key1220, -2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1183, 6), (key984, -2), (key1183, -2), (key1098, -2)]

def rawRow14864 : Integer.Sparse Key := [(key1090, -2), (key1169, -2), (key1098, -2), (key1090, 6), (key1180, -2), (key1220, -2), (key1183, -2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1183, 6), (key1098, -2), (key984, -2), (key1183, -2)]

def rawRow14865 : Integer.Sparse Key := [(key1169, -2), (key1090, -2), (key1098, -2), (key1090, 6), (key1220, -2), (key1180, -2), (key1183, -2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1183, 6), (key1098, -2), (key1183, -2), (key984, -2)]

def rawRow14866 : Integer.Sparse Key := [(key1098, -2), (key1169, -2), (key1090, -2), (key1090, 6), (key1183, -2), (key1220, -2), (key1180, -2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1183, 6), (key1183, -2), (key984, -2), (key1098, -2)]

def rawRow14867 : Integer.Sparse Key := [(key1169, -2), (key1098, -2), (key1090, -2), (key1090, 6), (key1220, -2), (key1183, -2), (key1180, -2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1183, 6), (key1183, -2), (key1098, -2), (key984, -2)]

def rawRow14868 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1183, -2), (key1220, 6), (key976, -2), (key984, -2), (key984, -2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key976, 6), (key1090, -2), (key1090, -2), (key1180, -2)]

def rawRow14869 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1183, -2), (key1220, 6), (key984, -2), (key976, -2), (key984, -2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key976, 6), (key1090, -2), (key1180, -2), (key1090, -2)]

def rawRow14870 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1180, -2), (key1220, 6), (key984, -2), (key984, -2), (key976, -2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key976, 6), (key1180, -2), (key1090, -2), (key1090, -2)]

def rawRow14871 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1220, -2), (key1183, 6), (key1090, -2), (key1098, -2), (key1169, -2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key984, -2), (key1098, -2), (key1183, -2), (key1090, 6), (key976, -2), (key1090, -2), (key1180, -2)]

def rawRow14872 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1220, -2), (key1183, 6), (key1098, -2), (key1090, -2), (key1169, -2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key984, -2), (key1183, -2), (key1098, -2), (key1090, 6), (key976, -2), (key1180, -2), (key1090, -2)]

def rawRow14873 : Integer.Sparse Key := [(key1180, -2), (key1220, -2), (key1183, -2), (key1183, 6), (key1090, -2), (key1169, -2), (key1098, -2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1098, -2), (key984, -2), (key1183, -2), (key1090, 6), (key1090, -2), (key976, -2), (key1180, -2)]

def rawRow14874 : Integer.Sparse Key := [(key1220, -2), (key1180, -2), (key1183, -2), (key1183, 6), (key1169, -2), (key1090, -2), (key1098, -2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1098, -2), (key1183, -2), (key984, -2), (key1090, 6), (key1090, -2), (key1180, -2), (key976, -2)]

def rawRow14875 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1180, -2), (key1183, 6), (key1098, -2), (key1169, -2), (key1090, -2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, 6), (key1180, -2), (key976, -2), (key1090, -2)]

def rawRow14876 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1180, -2), (key1183, 6), (key1169, -2), (key1098, -2), (key1090, -2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1183, -2), (key1098, -2), (key984, -2), (key1090, 6), (key1180, -2), (key1090, -2), (key976, -2)]

def rawRow14877 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1220, -2), (key1180, 6), (key1183, -2), (key1183, -2), (key1220, -2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1169, 2), (key1169, 2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, 6), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow14878 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1183, -2), (key1180, 6), (key1183, -2), (key1220, -2), (key1183, -2), (key1098, 2), (key1169, 2), (key984, 2), (key1169, 2), (key984, 2), (key1098, 2), (key1090, -2), (key976, -2), (key1090, -2), (key1180, 6), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow14879 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1183, -2), (key1180, 6), (key1220, -2), (key1183, -2), (key1183, -2), (key1169, 2), (key1098, 2), (key1169, 2), (key984, 2), (key1098, 2), (key984, 2), (key1090, -2), (key1090, -2), (key976, -2), (key1180, 6), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow14880 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, -2), (key2366, 6), (key2456, -2), (key2456, -2), (key2461, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, -2), (key2523, -2), (key2523, -2), (key2567, 6), (key2567, -2), (key2579, -2), (key2579, -2)]

def rawRow14881 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2361, -2), (key2366, 6), (key2456, -2), (key2461, -2), (key2456, -2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2523, -2), (key2461, -2), (key2523, -2), (key2567, 6), (key2579, -2), (key2567, -2), (key2579, -2)]

def rawRow14882 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2361, -2), (key2366, 6), (key2461, -2), (key2456, -2), (key2456, -2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2523, -2), (key2523, -2), (key2461, -2), (key2567, 6), (key2579, -2), (key2579, -2), (key2567, -2)]

def rawRow14883 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2363, -2), (key2361, 6), (key2517, -2), (key2523, -2), (key2523, -2), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2579, 6), (key2567, -2), (key2567, -2), (key2579, -2)]

def rawRow14884 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2363, -2), (key2361, 6), (key2523, -2), (key2517, -2), (key2523, -2), (key2461, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2579, 6), (key2567, -2), (key2579, -2), (key2567, -2)]

def rawRow14885 : Integer.Sparse Key := [(key2363, -2), (key2363, -2), (key2357, -2), (key2361, 6), (key2523, -2), (key2523, -2), (key2517, -2), (key2523, 2), (key2523, 2), (key2461, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2579, 6), (key2579, -2), (key2567, -2), (key2567, -2)]

def rawRow14886 : Integer.Sparse Key := [(key2452, -2), (key2452, -2), (key2458, -2), (key2519, 6), (key2357, -2), (key2361, -2), (key2366, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2567, -2), (key2579, -2), (key2579, -2), (key2366, 6), (key2461, -2), (key2523, -2), (key2523, -2)]

def rawRow14887 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2452, -2), (key2519, 6), (key2357, -2), (key2363, -2), (key2361, -2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2579, -2), (key2567, -2), (key2579, -2), (key2366, 6), (key2523, -2), (key2461, -2), (key2523, -2)]

def rawRow14888 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2452, -2), (key2519, 6), (key2363, -2), (key2357, -2), (key2361, -2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2579, -2), (key2579, -2), (key2567, -2), (key2366, 6), (key2523, -2), (key2523, -2), (key2461, -2)]

def rawRow14889 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2519, -2), (key2452, 6), (key2528, -2), (key2530, -2), (key2560, -2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2523, 6), (key2366, -2), (key2461, -2), (key2523, -2)]

def rawRow14890 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2519, -2), (key2452, 6), (key2530, -2), (key2528, -2), (key2560, -2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2523, 6), (key2366, -2), (key2523, -2), (key2461, -2)]

def rawRow14891 : Integer.Sparse Key := [(key2452, -2), (key2519, -2), (key2458, -2), (key2452, 6), (key2528, -2), (key2560, -2), (key2530, -2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2523, 6), (key2461, -2), (key2366, -2), (key2523, -2)]

def rawRow14892 : Integer.Sparse Key := [(key2519, -2), (key2452, -2), (key2458, -2), (key2452, 6), (key2560, -2), (key2528, -2), (key2530, -2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2523, 6), (key2461, -2), (key2523, -2), (key2366, -2)]

def rawRow14893 : Integer.Sparse Key := [(key2458, -2), (key2519, -2), (key2452, -2), (key2452, 6), (key2530, -2), (key2560, -2), (key2528, -2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2523, 6), (key2523, -2), (key2366, -2), (key2461, -2)]

def rawRow14894 : Integer.Sparse Key := [(key2519, -2), (key2458, -2), (key2452, -2), (key2452, 6), (key2560, -2), (key2530, -2), (key2528, -2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2523, 6), (key2523, -2), (key2461, -2), (key2366, -2)]

def rawRow14895 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2530, -2), (key2560, 6), (key2357, -2), (key2363, -2), (key2363, -2), (key2452, 2), (key2458, 2), (key2452, 2), (key2530, 2), (key2458, 2), (key2530, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2361, 6), (key2456, -2), (key2456, -2), (key2517, -2)]

def rawRow14896 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2530, -2), (key2560, 6), (key2363, -2), (key2357, -2), (key2363, -2), (key2458, 2), (key2452, 2), (key2530, 2), (key2452, 2), (key2530, 2), (key2458, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2361, 6), (key2456, -2), (key2517, -2), (key2456, -2)]

def rawRow14897 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2528, -2), (key2560, 6), (key2363, -2), (key2363, -2), (key2357, -2), (key2530, 2), (key2530, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2361, 6), (key2517, -2), (key2456, -2), (key2456, -2)]

def rawRow14898 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2560, -2), (key2530, 6), (key2452, -2), (key2458, -2), (key2519, -2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2363, -2), (key2458, -2), (key2530, -2), (key2456, 6), (key2361, -2), (key2456, -2), (key2517, -2)]

def rawRow14899 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2560, -2), (key2530, 6), (key2458, -2), (key2452, -2), (key2519, -2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2363, -2), (key2530, -2), (key2458, -2), (key2456, 6), (key2361, -2), (key2517, -2), (key2456, -2)]

def rawRow14900 : Integer.Sparse Key := [(key2528, -2), (key2560, -2), (key2530, -2), (key2530, 6), (key2452, -2), (key2519, -2), (key2458, -2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2458, -2), (key2363, -2), (key2530, -2), (key2456, 6), (key2456, -2), (key2361, -2), (key2517, -2)]

def rawRow14901 : Integer.Sparse Key := [(key2560, -2), (key2528, -2), (key2530, -2), (key2530, 6), (key2519, -2), (key2452, -2), (key2458, -2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2458, -2), (key2530, -2), (key2363, -2), (key2456, 6), (key2456, -2), (key2517, -2), (key2361, -2)]

def rawRow14902 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2528, -2), (key2530, 6), (key2458, -2), (key2519, -2), (key2452, -2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2530, -2), (key2363, -2), (key2458, -2), (key2456, 6), (key2517, -2), (key2361, -2), (key2456, -2)]

def rawRow14903 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2528, -2), (key2530, 6), (key2519, -2), (key2458, -2), (key2452, -2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2530, -2), (key2458, -2), (key2363, -2), (key2456, 6), (key2517, -2), (key2456, -2), (key2361, -2)]

def rawRow14904 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2560, -2), (key2528, 6), (key2530, -2), (key2530, -2), (key2560, -2), (key2363, 2), (key2363, 2), (key2458, 2), (key2458, 2), (key2519, 2), (key2519, 2), (key2357, -2), (key2452, -2), (key2452, -2), (key2517, 6), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow14905 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2530, -2), (key2528, 6), (key2530, -2), (key2560, -2), (key2530, -2), (key2458, 2), (key2519, 2), (key2363, 2), (key2519, 2), (key2363, 2), (key2458, 2), (key2452, -2), (key2357, -2), (key2452, -2), (key2517, 6), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow14906 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2530, -2), (key2528, 6), (key2560, -2), (key2530, -2), (key2530, -2), (key2519, 2), (key2458, 2), (key2519, 2), (key2363, 2), (key2458, 2), (key2363, 2), (key2452, -2), (key2452, -2), (key2357, -2), (key2517, 6), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow14907 : Integer.Sparse Key := [(key2377, 6), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, 6), (key2405, -2), (key2436, -2), (key2436, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

def rawRow14908 : Integer.Sparse Key := [(key2377, 6), (key2389, -2), (key2377, -2), (key2389, -2), (key2405, 6), (key2436, -2), (key2405, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

def rawRow14909 : Integer.Sparse Key := [(key2377, 6), (key2389, -2), (key2389, -2), (key2377, -2), (key2405, 6), (key2436, -2), (key2436, -2), (key2405, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2471, -2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

def rawRow14910 : Integer.Sparse Key := [(key2389, 6), (key2377, -2), (key2377, -2), (key2389, -2), (key2436, 6), (key2405, -2), (key2405, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

def rawRow14911 : Integer.Sparse Key := [(key2389, 6), (key2377, -2), (key2389, -2), (key2377, -2), (key2436, 6), (key2405, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2479, -2), (key2518, -2), (key2479, -2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

def rawRow14912 : Integer.Sparse Key := [(key2389, 6), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, 6), (key2436, -2), (key2405, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

def rawRow14913 : Integer.Sparse Key := [(key2405, 6), (key2471, -2), (key2479, -2), (key2479, -2), (key2377, 6), (key2471, -2), (key2502, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, -2), (key2436, -2), (key2436, -2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

def rawRow14914 : Integer.Sparse Key := [(key2405, 6), (key2479, -2), (key2471, -2), (key2479, -2), (key2377, 6), (key2502, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2389, -2), (key2436, -2), (key2405, -2), (key2436, -2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

def rawRow14915 : Integer.Sparse Key := [(key2405, 6), (key2479, -2), (key2479, -2), (key2471, -2), (key2377, 6), (key2502, -2), (key2502, -2), (key2471, -2), (key2389, -2), (key2389, -2), (key2377, -2), (key2436, -2), (key2436, -2), (key2405, -2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

def rawRow14916 : Integer.Sparse Key := [(key2479, 6), (key2405, -2), (key2471, -2), (key2479, -2), (key2502, 6), (key2377, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2518, -2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

def rawRow14917 : Integer.Sparse Key := [(key2479, 6), (key2405, -2), (key2479, -2), (key2471, -2), (key2502, 6), (key2377, -2), (key2502, -2), (key2471, -2), (key2436, -2), (key2518, -2), (key2502, -2), (key2389, -2), (key2518, -2), (key2479, -2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

def rawRow14918 : Integer.Sparse Key := [(key2479, 6), (key2471, -2), (key2405, -2), (key2479, -2), (key2502, 6), (key2471, -2), (key2377, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, -2), (key2389, -2), (key2518, -2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

def rawRow14919 : Integer.Sparse Key := [(key2479, 6), (key2471, -2), (key2479, -2), (key2405, -2), (key2502, 6), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

def rawRow14920 : Integer.Sparse Key := [(key2479, 6), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 6), (key2502, -2), (key2377, -2), (key2471, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

def rawRow14921 : Integer.Sparse Key := [(key2479, 6), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, 6), (key2502, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, -2), (key2389, -2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

def rawRow14922 : Integer.Sparse Key := [(key2436, 6), (key2502, -2), (key2502, -2), (key2518, -2), (key2389, 6), (key2479, -2), (key2479, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2405, -2), (key2436, -2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

def rawRow14923 : Integer.Sparse Key := [(key2436, 6), (key2502, -2), (key2518, -2), (key2502, -2), (key2389, 6), (key2479, -2), (key2518, -2), (key2479, -2), (key2377, -2), (key2389, -2), (key2377, -2), (key2405, -2), (key2436, -2), (key2405, -2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

def rawRow14924 : Integer.Sparse Key := [(key2436, 6), (key2518, -2), (key2502, -2), (key2502, -2), (key2389, 6), (key2518, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, -2), (key2405, -2), (key2405, -2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

def rawRow14925 : Integer.Sparse Key := [(key2502, 6), (key2436, -2), (key2502, -2), (key2518, -2), (key2479, 6), (key2389, -2), (key2479, -2), (key2518, -2), (key2405, -2), (key2471, -2), (key2479, -2), (key2377, -2), (key2471, -2), (key2502, -2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

def rawRow14926 : Integer.Sparse Key := [(key2502, 6), (key2436, -2), (key2518, -2), (key2502, -2), (key2479, 6), (key2389, -2), (key2518, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, -2), (key2502, -2), (key2471, -2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

def rawRow14927 : Integer.Sparse Key := [(key2502, 6), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, 6), (key2479, -2), (key2389, -2), (key2518, -2), (key2471, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, -2), (key2502, -2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

def rawRow14928 : Integer.Sparse Key := [(key2502, 6), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, 6), (key2479, -2), (key2518, -2), (key2389, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

def rawRow14929 : Integer.Sparse Key := [(key2502, 6), (key2518, -2), (key2436, -2), (key2502, -2), (key2479, 6), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

def rawRow14930 : Integer.Sparse Key := [(key2502, 6), (key2518, -2), (key2502, -2), (key2436, -2), (key2479, 6), (key2518, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, -2), (key2471, -2), (key2377, -2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

def rawRow14931 : Integer.Sparse Key := [(key2518, 6), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, 6), (key2389, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2377, 2), (key2377, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2)]

def rawRow14932 : Integer.Sparse Key := [(key2518, 6), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, 6), (key2479, -2), (key2389, -2), (key2479, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2405, 2), (key2471, 2), (key2377, 2), (key2471, 2), (key2377, 2), (key2405, 2)]

def rawRow14933 : Integer.Sparse Key := [(key2518, 6), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, 6), (key2479, -2), (key2479, -2), (key2389, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2471, 2), (key2405, 2), (key2471, 2), (key2377, 2), (key2405, 2), (key2377, 2)]

def rawRow14934 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key983, -2), (key983, 6), (key1090, -2), (key1090, -2), (key1097, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1182, 2), (key1182, 2), (key1097, -2), (key1182, -2), (key1182, -2), (key1168, 6), (key1168, -2), (key1219, -2), (key1219, -2)]

def rawRow14935 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key976, -2), (key983, 6), (key1090, -2), (key1097, -2), (key1090, -2), (key1180, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1182, -2), (key1097, -2), (key1182, -2), (key1168, 6), (key1219, -2), (key1168, -2), (key1219, -2)]

def rawRow14936 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key976, -2), (key983, 6), (key1097, -2), (key1090, -2), (key1090, -2), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1182, -2), (key1182, -2), (key1097, -2), (key1168, 6), (key1219, -2), (key1219, -2), (key1168, -2)]

def rawRow14937 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key983, -2), (key976, 6), (key1180, -2), (key1182, -2), (key1182, -2), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1182, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1219, 6), (key1168, -2), (key1168, -2), (key1219, -2)]

def rawRow14938 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key983, -2), (key976, 6), (key1182, -2), (key1180, -2), (key1182, -2), (key1097, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1219, 6), (key1168, -2), (key1219, -2), (key1168, -2)]

def rawRow14939 : Integer.Sparse Key := [(key983, -2), (key983, -2), (key976, -2), (key976, 6), (key1182, -2), (key1182, -2), (key1180, -2), (key1182, 2), (key1182, 2), (key1097, 2), (key1097, 2), (key1090, 2), (key1090, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1219, 6), (key1219, -2), (key1168, -2), (key1168, -2)]

def rawRow14940 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1097, -2), (key1168, 6), (key976, -2), (key976, -2), (key983, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1182, 2), (key1182, 2), (key1168, -2), (key1219, -2), (key1219, -2), (key983, 6), (key1097, -2), (key1182, -2), (key1182, -2)]

def rawRow14941 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1090, -2), (key1168, 6), (key976, -2), (key983, -2), (key976, -2), (key1180, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1219, -2), (key1168, -2), (key1219, -2), (key983, 6), (key1182, -2), (key1097, -2), (key1182, -2)]

def rawRow14942 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1090, -2), (key1168, 6), (key983, -2), (key976, -2), (key976, -2), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1219, -2), (key1219, -2), (key1168, -2), (key983, 6), (key1182, -2), (key1182, -2), (key1097, -2)]

def rawRow14943 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1168, -2), (key1090, 6), (key1180, -2), (key1182, -2), (key1219, -2), (key976, 2), (key983, 2), (key1090, 2), (key1182, 2), (key1168, 2), (key1219, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1182, 6), (key983, -2), (key1097, -2), (key1182, -2)]

def rawRow14944 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1168, -2), (key1090, 6), (key1182, -2), (key1180, -2), (key1219, -2), (key983, 2), (key976, 2), (key1182, 2), (key1090, 2), (key1219, 2), (key1168, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1182, 6), (key983, -2), (key1182, -2), (key1097, -2)]

def rawRow14945 : Integer.Sparse Key := [(key1090, -2), (key1168, -2), (key1097, -2), (key1090, 6), (key1180, -2), (key1219, -2), (key1182, -2), (key1090, 2), (key1168, 2), (key976, 2), (key1219, 2), (key983, 2), (key1182, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1182, 6), (key1097, -2), (key983, -2), (key1182, -2)]

def rawRow14946 : Integer.Sparse Key := [(key1168, -2), (key1090, -2), (key1097, -2), (key1090, 6), (key1219, -2), (key1180, -2), (key1182, -2), (key1168, 2), (key1090, 2), (key1219, 2), (key976, 2), (key1182, 2), (key983, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1182, 6), (key1097, -2), (key1182, -2), (key983, -2)]

def rawRow14947 : Integer.Sparse Key := [(key1097, -2), (key1168, -2), (key1090, -2), (key1090, 6), (key1182, -2), (key1219, -2), (key1180, -2), (key1182, 2), (key1219, 2), (key983, 2), (key1168, 2), (key976, 2), (key1090, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1182, 6), (key1182, -2), (key983, -2), (key1097, -2)]

def rawRow14948 : Integer.Sparse Key := [(key1168, -2), (key1097, -2), (key1090, -2), (key1090, 6), (key1219, -2), (key1182, -2), (key1180, -2), (key1219, 2), (key1182, 2), (key1168, 2), (key983, 2), (key1090, 2), (key976, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1182, 6), (key1182, -2), (key1097, -2), (key983, -2)]

def rawRow14949 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1182, -2), (key1219, 6), (key976, -2), (key983, -2), (key983, -2), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1182, 2), (key1168, -2), (key1168, -2), (key1219, -2), (key976, 6), (key1090, -2), (key1090, -2), (key1180, -2)]

def rawRow14950 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1182, -2), (key1219, 6), (key983, -2), (key976, -2), (key983, -2), (key1097, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1168, -2), (key1219, -2), (key1168, -2), (key976, 6), (key1090, -2), (key1180, -2), (key1090, -2)]

def rawRow14951 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1180, -2), (key1219, 6), (key983, -2), (key983, -2), (key976, -2), (key1182, 2), (key1182, 2), (key1097, 2), (key1097, 2), (key1090, 2), (key1090, 2), (key1219, -2), (key1168, -2), (key1168, -2), (key976, 6), (key1180, -2), (key1090, -2), (key1090, -2)]

def rawRow14952 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1219, -2), (key1182, 6), (key1090, -2), (key1097, -2), (key1168, -2), (key976, 2), (key983, 2), (key1090, 2), (key1182, 2), (key1168, 2), (key1219, 2), (key983, -2), (key1097, -2), (key1182, -2), (key1090, 6), (key976, -2), (key1090, -2), (key1180, -2)]

def rawRow14953 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1219, -2), (key1182, 6), (key1097, -2), (key1090, -2), (key1168, -2), (key983, 2), (key976, 2), (key1182, 2), (key1090, 2), (key1219, 2), (key1168, 2), (key983, -2), (key1182, -2), (key1097, -2), (key1090, 6), (key976, -2), (key1180, -2), (key1090, -2)]

def rawRow14954 : Integer.Sparse Key := [(key1180, -2), (key1219, -2), (key1182, -2), (key1182, 6), (key1090, -2), (key1168, -2), (key1097, -2), (key1090, 2), (key1168, 2), (key976, 2), (key1219, 2), (key983, 2), (key1182, 2), (key1097, -2), (key983, -2), (key1182, -2), (key1090, 6), (key1090, -2), (key976, -2), (key1180, -2)]

def rawRow14955 : Integer.Sparse Key := [(key1219, -2), (key1180, -2), (key1182, -2), (key1182, 6), (key1168, -2), (key1090, -2), (key1097, -2), (key1168, 2), (key1090, 2), (key1219, 2), (key976, 2), (key1182, 2), (key983, 2), (key1097, -2), (key1182, -2), (key983, -2), (key1090, 6), (key1090, -2), (key1180, -2), (key976, -2)]

def rawRow14956 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1180, -2), (key1182, 6), (key1097, -2), (key1168, -2), (key1090, -2), (key1182, 2), (key1219, 2), (key983, 2), (key1168, 2), (key976, 2), (key1090, 2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, 6), (key1180, -2), (key976, -2), (key1090, -2)]

def rawRow14957 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1180, -2), (key1182, 6), (key1168, -2), (key1097, -2), (key1090, -2), (key1219, 2), (key1182, 2), (key1168, 2), (key983, 2), (key1090, 2), (key976, 2), (key1182, -2), (key1097, -2), (key983, -2), (key1090, 6), (key1180, -2), (key1090, -2), (key976, -2)]

def rawRow14958 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1219, -2), (key1180, 6), (key1182, -2), (key1182, -2), (key1219, -2), (key983, 2), (key983, 2), (key1097, 2), (key1097, 2), (key1168, 2), (key1168, 2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, 6), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow14959 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1182, -2), (key1180, 6), (key1182, -2), (key1219, -2), (key1182, -2), (key1097, 2), (key1168, 2), (key983, 2), (key1168, 2), (key983, 2), (key1097, 2), (key1090, -2), (key976, -2), (key1090, -2), (key1180, 6), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow14960 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1182, -2), (key1180, 6), (key1219, -2), (key1182, -2), (key1182, -2), (key1168, 2), (key1097, 2), (key1168, 2), (key983, 2), (key1097, 2), (key983, 2), (key1090, -2), (key1090, -2), (key976, -2), (key1180, 6), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow14961 : Integer.Sparse Key := [(key1096, 4), (key1185, 4), (key1185, 4), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, 4), (key1224, 4), (key1224, 4)]

def rawRow14962 : Integer.Sparse Key := [(key1185, 4), (key1096, 4), (key1185, 4), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1224, 4), (key1175, 4), (key1224, 4)]

def rawRow14963 : Integer.Sparse Key := [(key1185, 4), (key1185, 4), (key1096, 4), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1224, 4), (key1224, 4), (key1175, 4)]

def rawRow14964 : Integer.Sparse Key := [(key1100, 4), (key1100, 4), (key1186, 4), (key1096, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1171, 4), (key1171, 4), (key1222, 4)]

def rawRow14965 : Integer.Sparse Key := [(key1100, 4), (key1186, 4), (key1100, 4), (key1100, -2), (key1096, -2), (key1185, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1171, 4), (key1222, 4), (key1171, 4)]

def rawRow14966 : Integer.Sparse Key := [(key1186, 4), (key1100, 4), (key1100, 4), (key1185, -2), (key1185, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, 4), (key1171, 4), (key1171, 4)]

def rawRow14967 : Integer.Sparse Key := [(key1096, 4), (key1185, 4), (key1185, 4), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1175, 4), (key1224, 4), (key1224, 4)]

def rawRow14968 : Integer.Sparse Key := [(key1185, 4), (key1096, 4), (key1185, 4), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1224, 4), (key1175, 4), (key1224, 4)]

def rawRow14969 : Integer.Sparse Key := [(key1185, 4), (key1185, 4), (key1096, 4), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, 4), (key1224, 4), (key1175, 4)]

def rawRow14970 : Integer.Sparse Key := [(key986, 4), (key1171, 4), (key1224, 4), (key982, -2), (key986, -2), (key1096, -2), (key1185, -2), (key1171, -2), (key1222, -2), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key986, 4), (key1100, 4), (key1185, 4)]

def rawRow14971 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1171, 4), (key986, -2), (key982, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, 4), (key1185, 4), (key1100, 4)]

def rawRow14972 : Integer.Sparse Key := [(key1171, 4), (key986, 4), (key1224, 4), (key1096, -2), (key1171, -2), (key982, -2), (key1222, -2), (key986, -2), (key1185, -2), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1100, 4), (key986, 4), (key1185, 4)]

def rawRow14973 : Integer.Sparse Key := [(key1171, 4), (key1224, 4), (key986, 4), (key1171, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1185, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1100, 4), (key1185, 4), (key986, 4)]

def rawRow14974 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1171, 4), (key1185, -2), (key1222, -2), (key986, -2), (key1171, -2), (key982, -2), (key1096, -2), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, 4), (key986, 4), (key1100, 4)]

def rawRow14975 : Integer.Sparse Key := [(key1224, 4), (key1171, 4), (key986, 4), (key1222, -2), (key1185, -2), (key1171, -2), (key986, -2), (key1096, -2), (key982, -2), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1185, 4), (key1100, 4), (key986, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14976 : Integer.Sparse Key := [(key1100, 4), (key1100, 4), (key1186, 4), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1096, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key1171, 4), (key1171, 4), (key1222, 4)]

def rawRow14977 : Integer.Sparse Key := [(key1100, 4), (key1186, 4), (key1100, 4), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1171, 4), (key1222, 4), (key1171, 4)]

def rawRow14978 : Integer.Sparse Key := [(key1186, 4), (key1100, 4), (key1100, 4), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1185, -2), (key1185, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1222, 4), (key1171, 4), (key1171, 4)]

def rawRow14979 : Integer.Sparse Key := [(key986, 4), (key1171, 4), (key1224, 4), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key982, -2), (key986, -2), (key1096, -2), (key1185, -2), (key1171, -2), (key1222, -2), (key986, 4), (key1100, 4), (key1185, 4)]

def rawRow14980 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1171, 4), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, -2), (key982, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key986, 4), (key1185, 4), (key1100, 4)]

def rawRow14981 : Integer.Sparse Key := [(key1171, 4), (key986, 4), (key1224, 4), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1096, -2), (key1171, -2), (key982, -2), (key1222, -2), (key986, -2), (key1185, -2), (key1100, 4), (key986, 4), (key1185, 4)]

def rawRow14982 : Integer.Sparse Key := [(key1171, 4), (key1224, 4), (key986, 4), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1185, -2), (key986, -2), (key1100, 4), (key1185, 4), (key986, 4)]

def rawRow14983 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1171, 4), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key986, -2), (key1171, -2), (key982, -2), (key1096, -2), (key1185, 4), (key986, 4), (key1100, 4)]

def rawRow14984 : Integer.Sparse Key := [(key1224, 4), (key1171, 4), (key986, 4), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1222, -2), (key1185, -2), (key1171, -2), (key986, -2), (key1096, -2), (key982, -2), (key1185, 4), (key1100, 4), (key986, 4)]

def rawRow14985 : Integer.Sparse Key := [(key988, 4), (key1175, 4), (key1175, 4), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key982, 4), (key1096, 4), (key1096, 4)]

def rawRow14986 : Integer.Sparse Key := [(key1175, 4), (key988, 4), (key1175, 4), (key1100, -2), (key1171, -2), (key986, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1096, 4), (key982, 4), (key1096, 4)]

def rawRow14987 : Integer.Sparse Key := [(key1175, 4), (key1175, 4), (key988, 4), (key1171, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2), (key986, -2), (key1171, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, 4), (key1096, 4), (key982, 4)]

def rawRow14988 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2411, 2), (key2443, 2), (key2443, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2509, -1), (key2509, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, -1), (key2484, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1), (key2569, 2), (key2576, 2), (key2576, 2), (key2571, -1), (key2571, -1), (key2576, -1), (key2576, -1), (key2580, -1), (key2580, -1)]

def rawRow14989 : Integer.Sparse Key := [(key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2443, 2), (key2411, 2), (key2443, 2), (key2503, -1), (key2509, -1), (key2472, -1), (key2509, -1), (key2472, -1), (key2503, -1), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2509, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2576, 2), (key2569, 2), (key2576, 2), (key2576, -1), (key2580, -1), (key2571, -1), (key2580, -1), (key2571, -1), (key2576, -1)]

def rawRow14990 : Integer.Sparse Key := [(key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2443, 2), (key2443, 2), (key2411, 2), (key2509, -1), (key2503, -1), (key2509, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2484, -1), (key2576, 2), (key2576, 2), (key2569, 2), (key2580, -1), (key2576, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2571, -1)]

def rawRow14991 : Integer.Sparse Key := [(key2406, -1), (key2411, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2443, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2480, -1), (key2484, -1), (key2480, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2472, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2509, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1), (key2571, 2), (key2571, 2), (key2580, 2), (key2569, -1), (key2571, -1), (key2569, -1), (key2576, -1), (key2571, -1), (key2576, -1)]

def rawRow14992 : Integer.Sparse Key := [(key2411, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2484, -1), (key2480, -1), (key2524, -1), (key2480, -1), (key2524, -1), (key2484, -1), (key2484, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2571, 2), (key2580, 2), (key2571, 2), (key2571, -1), (key2569, -1), (key2576, -1), (key2569, -1), (key2576, -1), (key2571, -1)]

def rawRow14993 : Integer.Sparse Key := [(key2443, -1), (key2443, -1), (key2411, -1), (key2411, -1), (key2406, -1), (key2406, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2524, -1), (key2524, -1), (key2484, -1), (key2484, -1), (key2480, -1), (key2480, -1), (key2509, 2), (key2509, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1), (key2580, 2), (key2571, 2), (key2571, 2), (key2576, -1), (key2576, -1), (key2571, -1), (key2571, -1), (key2569, -1), (key2569, -1)]

def rawRow14994 : Integer.Sparse Key := [(key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2968, -1), (key2968, -1), (key2880, 2), (key2989, 2), (key2989, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2571, -1), (key2571, -1), (key2576, -1), (key2576, -1), (key2580, -1), (key2580, -1), (key2411, 2), (key2443, 2), (key2443, 2), (key2484, -1), (key2484, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1)]

def rawRow14995 : Integer.Sparse Key := [(key2966, -1), (key2968, -1), (key2843, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2989, 2), (key2880, 2), (key2989, 2), (key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2576, -1), (key2580, -1), (key2571, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2443, 2), (key2411, 2), (key2443, 2), (key2509, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2484, -1), (key2509, -1)]

def rawRow14996 : Integer.Sparse Key := [(key2968, -1), (key2966, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2843, -1), (key2989, 2), (key2989, 2), (key2880, 2), (key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2580, -1), (key2576, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2571, -1), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2484, -1)]

def rawRow14997 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2587, 2), (key2843, 2), (key2966, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1), (key2394, 2), (key2484, 2), (key2524, 2), (key2383, -1), (key2394, -1), (key2411, -1), (key2443, -1), (key2484, -1), (key2509, -1)]

def rawRow14998 : Integer.Sparse Key := [(key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2587, 2), (key2966, 2), (key2843, 2), (key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1), (key2394, 2), (key2524, 2), (key2484, 2), (key2394, -1), (key2383, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2484, -1)]

def rawRow14999 : Integer.Sparse Key := [(key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2843, 2), (key2587, 2), (key2966, 2), (key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2484, 2), (key2394, 2), (key2524, 2), (key2411, -1), (key2484, -1), (key2383, -1), (key2509, -1), (key2394, -1), (key2443, -1)]

def rawRow15000 : Integer.Sparse Key := [(key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2843, 2), (key2966, 2), (key2587, 2), (key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2443, -1), (key2394, -1)]

def rawRow15001 : Integer.Sparse Key := [(key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2966, 2), (key2587, 2), (key2843, 2), (key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1), (key2524, 2), (key2394, 2), (key2484, 2), (key2443, -1), (key2509, -1), (key2394, -1), (key2484, -1), (key2383, -1), (key2411, -1)]

def rawRow15002 : Integer.Sparse Key := [(key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2966, 2), (key2843, 2), (key2587, 2), (key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2524, 2), (key2484, 2), (key2394, 2), (key2509, -1), (key2443, -1), (key2484, -1), (key2394, -1), (key2411, -1), (key2383, -1)]

def rawRow15003 : Integer.Sparse Key := [(key2887, -1), (key2889, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2995, -1), (key2910, 2), (key2910, 2), (key3002, 2), (key2766, -1), (key2772, -1), (key2766, -1), (key2931, -1), (key2772, -1), (key2931, -1), (key2843, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2968, 2), (key2880, -1), (key2910, -1), (key2880, -1), (key2989, -1), (key2910, -1), (key2989, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1)]

def rawRow15004 : Integer.Sparse Key := [(key2889, -1), (key2887, -1), (key2995, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2910, 2), (key3002, 2), (key2910, 2), (key2772, -1), (key2766, -1), (key2931, -1), (key2766, -1), (key2931, -1), (key2772, -1), (key2889, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2910, -1), (key2880, -1), (key2989, -1), (key2880, -1), (key2989, -1), (key2910, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1)]

def rawRow15005 : Integer.Sparse Key := [(key2995, -1), (key2995, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key3002, 2), (key2910, 2), (key2910, 2), (key2931, -1), (key2931, -1), (key2772, -1), (key2772, -1), (key2766, -1), (key2766, -1), (key2968, 2), (key2968, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2989, -1), (key2989, -1), (key2910, -1), (key2910, -1), (key2880, -1), (key2880, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1)]

def rawRow15006 : Integer.Sparse Key := [(key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2600, 2), (key2889, 2), (key2995, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2593, -1), (key2600, -1), (key2772, -1), (key2931, -1), (key2889, -1), (key2968, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1)]

def rawRow15007 : Integer.Sparse Key := [(key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2600, 2), (key2995, 2), (key2889, 2), (key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2600, -1), (key2593, -1), (key2931, -1), (key2772, -1), (key2968, -1), (key2889, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1)]

def rawRow15008 : Integer.Sparse Key := [(key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2889, 2), (key2600, 2), (key2995, 2), (key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2772, -1), (key2889, -1), (key2593, -1), (key2968, -1), (key2600, -1), (key2931, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1)]

def rawRow15009 : Integer.Sparse Key := [(key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2889, 2), (key2995, 2), (key2600, 2), (key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2889, -1), (key2772, -1), (key2968, -1), (key2593, -1), (key2931, -1), (key2600, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1)]

def rawRow15010 : Integer.Sparse Key := [(key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2995, 2), (key2600, 2), (key2889, 2), (key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2931, -1), (key2968, -1), (key2600, -1), (key2889, -1), (key2593, -1), (key2772, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1)]

def rawRow15011 : Integer.Sparse Key := [(key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2995, 2), (key2889, 2), (key2600, 2), (key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, -1), (key2931, -1), (key2889, -1), (key2600, -1), (key2772, -1), (key2593, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1)]

def rawRow15012 : Integer.Sparse Key := [(key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2910, -1), (key2910, -1), (key2598, 2), (key2887, 2), (key2887, 2), (key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2910, -1), (key2910, -1), (key2593, 2), (key2593, 2), (key2772, 2), (key2772, 2), (key2880, 2), (key2880, 2), (key2587, -1), (key2587, -1), (key2766, -1), (key2766, -1), (key2843, -1), (key2843, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1)]

def rawRow15013 : Integer.Sparse Key := [(key2889, -1), (key2910, -1), (key2600, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2887, 2), (key2598, 2), (key2887, 2), (key2889, -1), (key2910, -1), (key2600, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2772, 2), (key2880, 2), (key2593, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2766, -1), (key2843, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key2766, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1)]

def rawRow15014 : Integer.Sparse Key := [(key2910, -1), (key2889, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2887, 2), (key2887, 2), (key2598, 2), (key2910, -1), (key2889, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2880, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2593, 2), (key2843, -1), (key2766, -1), (key2843, -1), (key2587, -1), (key2766, -1), (key2587, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1)]

def rawRow15015 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2427, -4), (key2427, -4), (key2438, -4), (key2495, -4), (key2495, -4), (key2504, -4), (key2504, 12)]

def rawRow15016 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2427, -4), (key2438, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2495, -4), (key2504, 12)]

def rawRow15017 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2495, -4), (key2495, -4), (key2504, 12)]

def rawRow15018 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2504, -4), (key2495, 12)]

def rawRow15019 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2427, -4), (key2420, -4), (key2427, -4), (key2504, -4), (key2495, -4), (key2504, -4), (key2495, 12)]

def rawRow15020 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2427, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2504, -4), (key2495, -4), (key2495, 12)]

def rawRow15021 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2495, -4), (key2495, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2504, 12)]

def rawRow15022 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2495, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2438, -4), (key2427, -4), (key2504, 12)]

def rawRow15023 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2504, -4), (key2495, -4), (key2495, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, 12)]

def rawRow15024 : Integer.Sparse Key := [(key2427, 4), (key2495, 4), (key2504, 4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2438, -4), (key2504, -4), (key2427, 12)]

def rawRow15025 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2495, 4), (key2427, -4), (key2420, -4), (key2495, -4), (key2438, -4), (key2427, -4), (key2504, -4), (key2427, 12)]

def rawRow15026 : Integer.Sparse Key := [(key2495, 4), (key2427, 4), (key2504, 4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2438, -4), (key2427, 12)]

def rawRow15027 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2427, 4), (key2495, -4), (key2420, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2438, -4), (key2427, 12)]

def rawRow15028 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2495, 4), (key2427, -4), (key2495, -4), (key2420, -4), (key2438, -4), (key2504, -4), (key2427, -4), (key2427, 12)]

def rawRow15029 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2427, 4), (key2495, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2438, -4), (key2427, -4), (key2427, 12)]

def rawRow15030 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2495, -4), (key2504, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, 12)]

def rawRow15031 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2504, -4), (key2495, -4), (key2504, -4), (key2427, -4), (key2420, -4), (key2427, -4), (key2495, 12)]

def rawRow15032 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2504, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2495, 12)]

def rawRow15033 : Integer.Sparse Key := [(key2427, 4), (key2495, 4), (key2504, 4), (key2427, -4), (key2438, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, 12)]

def rawRow15034 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2495, 4), (key2438, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2420, -4), (key2495, -4), (key2427, 12)]

def rawRow15035 : Integer.Sparse Key := [(key2495, 4), (key2427, 4), (key2504, 4), (key2427, -4), (key2504, -4), (key2438, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, 12)]

def rawRow15036 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2427, 4), (key2504, -4), (key2427, -4), (key2438, -4), (key2495, -4), (key2420, -4), (key2427, -4), (key2427, 12)]

def rawRow15037 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2495, 4), (key2438, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2427, 12)]

def rawRow15038 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2427, 4), (key2504, -4), (key2438, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2427, 12)]

def rawRow15039 : Integer.Sparse Key := [(key2438, 4), (key2504, 4), (key2504, 4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2420, 12)]

def rawRow15040 : Integer.Sparse Key := [(key2504, 4), (key2438, 4), (key2504, 4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, 12)]

def rawRow15041 : Integer.Sparse Key := [(key2504, 4), (key2504, 4), (key2438, 4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2420, 12)]

def rawRow15042 : Integer.Sparse Key := [(key2361, -2), (key2361, -2), (key2364, -2), (key2364, 6), (key2456, -2), (key2456, -2), (key2459, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, -2), (key2520, -2), (key2520, -2), (key2531, 6), (key2531, -2), (key2561, -2), (key2561, -2)]

def rawRow15043 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2361, -2), (key2364, 6), (key2456, -2), (key2459, -2), (key2456, -2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2520, -2), (key2459, -2), (key2520, -2), (key2531, 6), (key2561, -2), (key2531, -2), (key2561, -2)]

def rawRow15044 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2361, -2), (key2364, 6), (key2459, -2), (key2456, -2), (key2456, -2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2459, -2), (key2531, 6), (key2561, -2), (key2561, -2), (key2531, -2)]

def rawRow15045 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2364, -2), (key2361, 6), (key2517, -2), (key2520, -2), (key2520, -2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2561, 6), (key2531, -2), (key2531, -2), (key2561, -2)]

def rawRow15046 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2364, -2), (key2361, 6), (key2520, -2), (key2517, -2), (key2520, -2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2561, 6), (key2531, -2), (key2561, -2), (key2531, -2)]

def rawRow15047 : Integer.Sparse Key := [(key2364, -2), (key2364, -2), (key2361, -2), (key2361, 6), (key2520, -2), (key2520, -2), (key2517, -2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2561, 6), (key2561, -2), (key2531, -2), (key2531, -2)]

def rawRow15048 : Integer.Sparse Key := [(key2456, -2), (key2456, -2), (key2459, -2), (key2531, 6), (key2361, -2), (key2361, -2), (key2364, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2531, -2), (key2561, -2), (key2561, -2), (key2364, 6), (key2459, -2), (key2520, -2), (key2520, -2)]

def rawRow15049 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2456, -2), (key2531, 6), (key2361, -2), (key2364, -2), (key2361, -2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, -2), (key2531, -2), (key2561, -2), (key2364, 6), (key2520, -2), (key2459, -2), (key2520, -2)]

def rawRow15050 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2456, -2), (key2531, 6), (key2364, -2), (key2361, -2), (key2361, -2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2561, -2), (key2561, -2), (key2531, -2), (key2364, 6), (key2520, -2), (key2520, -2), (key2459, -2)]

def rawRow15051 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2531, -2), (key2456, 6), (key2517, -2), (key2520, -2), (key2561, -2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2520, 6), (key2364, -2), (key2459, -2), (key2520, -2)]

def rawRow15052 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2531, -2), (key2456, 6), (key2520, -2), (key2517, -2), (key2561, -2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2520, 6), (key2364, -2), (key2520, -2), (key2459, -2)]

def rawRow15053 : Integer.Sparse Key := [(key2456, -2), (key2531, -2), (key2459, -2), (key2456, 6), (key2517, -2), (key2561, -2), (key2520, -2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2520, 6), (key2459, -2), (key2364, -2), (key2520, -2)]

def rawRow15054 : Integer.Sparse Key := [(key2531, -2), (key2456, -2), (key2459, -2), (key2456, 6), (key2561, -2), (key2517, -2), (key2520, -2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2520, 6), (key2459, -2), (key2520, -2), (key2364, -2)]

def rawRow15055 : Integer.Sparse Key := [(key2459, -2), (key2531, -2), (key2456, -2), (key2456, 6), (key2520, -2), (key2561, -2), (key2517, -2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2520, 6), (key2520, -2), (key2364, -2), (key2459, -2)]

def rawRow15056 : Integer.Sparse Key := [(key2531, -2), (key2459, -2), (key2456, -2), (key2456, 6), (key2561, -2), (key2520, -2), (key2517, -2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2520, 6), (key2520, -2), (key2459, -2), (key2364, -2)]

def rawRow15057 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2520, -2), (key2561, 6), (key2361, -2), (key2364, -2), (key2364, -2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2361, 6), (key2456, -2), (key2456, -2), (key2517, -2)]

def rawRow15058 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2520, -2), (key2561, 6), (key2364, -2), (key2361, -2), (key2364, -2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2361, 6), (key2456, -2), (key2517, -2), (key2456, -2)]

def rawRow15059 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2517, -2), (key2561, 6), (key2364, -2), (key2364, -2), (key2361, -2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2361, 6), (key2517, -2), (key2456, -2), (key2456, -2)]

def rawRow15060 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2561, -2), (key2520, 6), (key2456, -2), (key2459, -2), (key2531, -2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2364, -2), (key2459, -2), (key2520, -2), (key2456, 6), (key2361, -2), (key2456, -2), (key2517, -2)]

def rawRow15061 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2561, -2), (key2520, 6), (key2459, -2), (key2456, -2), (key2531, -2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2364, -2), (key2520, -2), (key2459, -2), (key2456, 6), (key2361, -2), (key2517, -2), (key2456, -2)]

def rawRow15062 : Integer.Sparse Key := [(key2517, -2), (key2561, -2), (key2520, -2), (key2520, 6), (key2456, -2), (key2531, -2), (key2459, -2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2459, -2), (key2364, -2), (key2520, -2), (key2456, 6), (key2456, -2), (key2361, -2), (key2517, -2)]

def rawRow15063 : Integer.Sparse Key := [(key2561, -2), (key2517, -2), (key2520, -2), (key2520, 6), (key2531, -2), (key2456, -2), (key2459, -2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2459, -2), (key2520, -2), (key2364, -2), (key2456, 6), (key2456, -2), (key2517, -2), (key2361, -2)]

def rawRow15064 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2517, -2), (key2520, 6), (key2459, -2), (key2531, -2), (key2456, -2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, 6), (key2517, -2), (key2361, -2), (key2456, -2)]

def rawRow15065 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2517, -2), (key2520, 6), (key2531, -2), (key2459, -2), (key2456, -2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2520, -2), (key2459, -2), (key2364, -2), (key2456, 6), (key2517, -2), (key2456, -2), (key2361, -2)]

def rawRow15066 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2561, -2), (key2517, 6), (key2520, -2), (key2520, -2), (key2561, -2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2531, 2), (key2531, 2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, 6), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow15067 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2520, -2), (key2517, 6), (key2520, -2), (key2561, -2), (key2520, -2), (key2459, 2), (key2531, 2), (key2364, 2), (key2531, 2), (key2364, 2), (key2459, 2), (key2456, -2), (key2361, -2), (key2456, -2), (key2517, 6), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow15068 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2520, -2), (key2517, 6), (key2561, -2), (key2520, -2), (key2520, -2), (key2531, 2), (key2459, 2), (key2531, 2), (key2364, 2), (key2459, 2), (key2364, 2), (key2456, -2), (key2456, -2), (key2361, -2), (key2517, 6), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow15069 : Integer.Sparse Key := [(key1975, 4), (key1980, 4), (key1980, 4), (key1980, -4), (key1980, -4), (key1996, -4), (key2217, -4), (key2217, -4), (key2261, -4), (key2261, 12)]

def rawRow15070 : Integer.Sparse Key := [(key1980, 4), (key1975, 4), (key1980, 4), (key1980, -4), (key1996, -4), (key1980, -4), (key2217, -4), (key2261, -4), (key2217, -4), (key2261, 12)]

def rawRow15071 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1975, 4), (key1996, -4), (key1980, -4), (key1980, -4), (key2261, -4), (key2217, -4), (key2217, -4), (key2261, 12)]

def rawRow15072 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1996, 4), (key1975, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key2261, -4), (key2261, -4), (key2217, 12)]

def rawRow15073 : Integer.Sparse Key := [(key1980, 4), (key1996, 4), (key1980, 4), (key1980, -4), (key1975, -4), (key1980, -4), (key2261, -4), (key2217, -4), (key2261, -4), (key2217, 12)]

def rawRow15074 : Integer.Sparse Key := [(key1996, 4), (key1980, 4), (key1980, 4), (key1980, -4), (key1980, -4), (key1975, -4), (key2261, -4), (key2261, -4), (key2217, -4), (key2217, 12)]

def rawRow15075 : Integer.Sparse Key := [(key1975, 4), (key1980, 4), (key1980, 4), (key2217, -4), (key2217, -4), (key2261, -4), (key1980, -4), (key1980, -4), (key1996, -4), (key2261, 12)]

def rawRow15076 : Integer.Sparse Key := [(key1980, 4), (key1975, 4), (key1980, 4), (key2217, -4), (key2261, -4), (key2217, -4), (key1980, -4), (key1996, -4), (key1980, -4), (key2261, 12)]

def rawRow15077 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1975, 4), (key2261, -4), (key2217, -4), (key2217, -4), (key1996, -4), (key1980, -4), (key1980, -4), (key2261, 12)]

def rawRow15078 : Integer.Sparse Key := [(key1980, 4), (key2217, 4), (key2261, 4), (key1975, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1996, -4), (key2261, -4), (key1980, 12)]

def rawRow15079 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key2217, 4), (key1980, -4), (key1975, -4), (key2217, -4), (key1996, -4), (key1980, -4), (key2261, -4), (key1980, 12)]

def rawRow15080 : Integer.Sparse Key := [(key2217, 4), (key1980, 4), (key2261, 4), (key1975, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2261, -4), (key1996, -4), (key1980, 12)]

def rawRow15081 : Integer.Sparse Key := [(key2217, 4), (key2261, 4), (key1980, 4), (key2217, -4), (key1975, -4), (key1980, -4), (key2261, -4), (key1980, -4), (key1996, -4), (key1980, 12)]

def rawRow15082 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key2217, 4), (key1980, -4), (key2217, -4), (key1975, -4), (key1996, -4), (key2261, -4), (key1980, -4), (key1980, 12)]

def rawRow15083 : Integer.Sparse Key := [(key2261, 4), (key2217, 4), (key1980, 4), (key2217, -4), (key1980, -4), (key1975, -4), (key2261, -4), (key1996, -4), (key1980, -4), (key1980, 12)]

def rawRow15084 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1996, 4), (key2217, -4), (key2261, -4), (key2261, -4), (key1975, -4), (key1980, -4), (key1980, -4), (key2217, 12)]

def rawRow15085 : Integer.Sparse Key := [(key1980, 4), (key1996, 4), (key1980, 4), (key2261, -4), (key2217, -4), (key2261, -4), (key1980, -4), (key1975, -4), (key1980, -4), (key2217, 12)]

def rawRow15086 : Integer.Sparse Key := [(key1996, 4), (key1980, 4), (key1980, 4), (key2261, -4), (key2261, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key1975, -4), (key2217, 12)]

def rawRow15087 : Integer.Sparse Key := [(key1980, 4), (key2217, 4), (key2261, 4), (key1980, -4), (key1996, -4), (key2261, -4), (key1975, -4), (key1980, -4), (key2217, -4), (key1980, 12)]

def rawRow15088 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key2217, 4), (key1996, -4), (key1980, -4), (key2261, -4), (key1980, -4), (key1975, -4), (key2217, -4), (key1980, 12)]

def rawRow15089 : Integer.Sparse Key := [(key2217, 4), (key1980, 4), (key2261, 4), (key1980, -4), (key2261, -4), (key1996, -4), (key1975, -4), (key2217, -4), (key1980, -4), (key1980, 12)]

def rawRow15090 : Integer.Sparse Key := [(key2217, 4), (key2261, 4), (key1980, 4), (key2261, -4), (key1980, -4), (key1996, -4), (key2217, -4), (key1975, -4), (key1980, -4), (key1980, 12)]

def rawRow15091 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key2217, 4), (key1996, -4), (key2261, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1975, -4), (key1980, 12)]

def rawRow15092 : Integer.Sparse Key := [(key2261, 4), (key2217, 4), (key1980, 4), (key2261, -4), (key1996, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1975, -4), (key1980, 12)]

def rawRow15093 : Integer.Sparse Key := [(key1996, 4), (key2261, 4), (key2261, 4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1975, 12)]

def rawRow15094 : Integer.Sparse Key := [(key2261, 4), (key1996, 4), (key2261, 4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1975, 12)]

def rawRow15095 : Integer.Sparse Key := [(key2261, 4), (key2261, 4), (key1996, 4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key1975, 12)]

def rawRow15096 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2409, 2), (key2440, 2), (key2440, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2522, 2), (key2522, 2), (key2482, -1), (key2482, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2538, 2), (key2554, 2), (key2554, 2), (key2543, -1), (key2543, -1), (key2554, -1), (key2554, -1), (key2563, -1), (key2563, -1)]

def rawRow15097 : Integer.Sparse Key := [(key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2440, 2), (key2409, 2), (key2440, 2), (key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2503, 2), (key2522, 2), (key2480, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2506, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2554, 2), (key2538, 2), (key2554, 2), (key2554, -1), (key2563, -1), (key2543, -1), (key2563, -1), (key2543, -1), (key2554, -1)]

def rawRow15098 : Integer.Sparse Key := [(key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2440, 2), (key2440, 2), (key2409, 2), (key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2522, 2), (key2503, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2482, -1), (key2554, 2), (key2554, 2), (key2538, 2), (key2563, -1), (key2554, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2543, -1)]

def rawRow15099 : Integer.Sparse Key := [(key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2472, 2), (key2482, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2506, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1), (key2543, 2), (key2543, 2), (key2563, 2), (key2538, -1), (key2543, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2554, -1)]

def rawRow15100 : Integer.Sparse Key := [(key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2482, 2), (key2472, 2), (key2506, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2543, 2), (key2563, 2), (key2543, 2), (key2543, -1), (key2538, -1), (key2554, -1), (key2538, -1), (key2554, -1), (key2543, -1)]

def rawRow15101 : Integer.Sparse Key := [(key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2506, 2), (key2506, 2), (key2482, 2), (key2482, 2), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1), (key2563, 2), (key2543, 2), (key2543, 2), (key2554, -1), (key2554, -1), (key2543, -1), (key2543, -1), (key2538, -1), (key2538, -1)]

def rawRow15102 : Integer.Sparse Key := [(key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2538, 2), (key2554, 2), (key2554, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2522, 2), (key2522, 2), (key2543, -1), (key2543, -1), (key2554, -1), (key2554, -1), (key2563, -1), (key2563, -1), (key2409, 2), (key2440, 2), (key2440, 2), (key2482, -1), (key2482, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1)]

def rawRow15103 : Integer.Sparse Key := [(key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2554, 2), (key2538, 2), (key2554, 2), (key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2503, 2), (key2522, 2), (key2480, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2554, -1), (key2563, -1), (key2543, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2440, 2), (key2409, 2), (key2440, 2), (key2506, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2482, -1), (key2506, -1)]

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

def rawRow15104 : Integer.Sparse Key := [(key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2554, 2), (key2554, 2), (key2538, 2), (key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2522, 2), (key2503, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2563, -1), (key2554, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2543, -1), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2482, -1)]

def rawRow15105 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2378, 2), (key2392, 2), (key2406, 2), (key2440, 2), (key2543, 2), (key2554, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1), (key2392, 2), (key2482, 2), (key2522, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2440, -1), (key2482, -1), (key2506, -1)]

def rawRow15106 : Integer.Sparse Key := [(key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2392, 2), (key2378, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2543, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1), (key2392, 2), (key2522, 2), (key2482, 2), (key2392, -1), (key2381, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2482, -1)]

def rawRow15107 : Integer.Sparse Key := [(key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2406, 2), (key2543, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2482, 2), (key2392, 2), (key2522, 2), (key2409, -1), (key2482, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2440, -1)]

def rawRow15108 : Integer.Sparse Key := [(key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2543, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2440, 2), (key2392, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1), (key2482, 2), (key2522, 2), (key2392, 2), (key2482, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2440, -1), (key2392, -1)]

def rawRow15109 : Integer.Sparse Key := [(key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2440, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2378, 2), (key2406, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1), (key2522, 2), (key2392, 2), (key2482, 2), (key2440, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2381, -1), (key2409, -1)]

def rawRow15110 : Integer.Sparse Key := [(key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2554, 2), (key2440, 2), (key2543, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2522, 2), (key2482, 2), (key2392, 2), (key2506, -1), (key2440, -1), (key2482, -1), (key2392, -1), (key2409, -1), (key2381, -1)]

def rawRow15111 : Integer.Sparse Key := [(key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2543, 2), (key2543, 2), (key2563, 2), (key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2472, 2), (key2482, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2506, 2), (key2538, -1), (key2543, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2554, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1)]

def rawRow15112 : Integer.Sparse Key := [(key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2543, 2), (key2563, 2), (key2543, 2), (key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2482, 2), (key2472, 2), (key2506, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2543, -1), (key2538, -1), (key2554, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1)]

def rawRow15113 : Integer.Sparse Key := [(key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2563, 2), (key2543, 2), (key2543, 2), (key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2506, 2), (key2506, 2), (key2482, 2), (key2482, 2), (key2472, 2), (key2472, 2), (key2554, -1), (key2554, -1), (key2543, -1), (key2543, -1), (key2538, -1), (key2538, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1)]

def rawRow15114 : Integer.Sparse Key := [(key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2392, 2), (key2482, 2), (key2522, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2378, 2), (key2392, 2), (key2406, 2), (key2440, 2), (key2543, 2), (key2554, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2440, -1), (key2482, -1), (key2506, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1)]

def rawRow15115 : Integer.Sparse Key := [(key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2392, 2), (key2522, 2), (key2482, 2), (key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2392, 2), (key2378, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2543, 2), (key2392, -1), (key2381, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2482, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1)]

def rawRow15116 : Integer.Sparse Key := [(key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2482, 2), (key2392, 2), (key2522, 2), (key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2406, 2), (key2543, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2409, -1), (key2482, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2440, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1)]

def rawRow15117 : Integer.Sparse Key := [(key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2482, 2), (key2522, 2), (key2392, 2), (key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2543, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2440, 2), (key2392, 2), (key2482, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2440, -1), (key2392, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1)]

def rawRow15118 : Integer.Sparse Key := [(key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2522, 2), (key2392, 2), (key2482, 2), (key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2440, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2378, 2), (key2406, 2), (key2440, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2381, -1), (key2409, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1)]

def rawRow15119 : Integer.Sparse Key := [(key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2522, 2), (key2482, 2), (key2392, 2), (key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2554, 2), (key2440, 2), (key2543, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2506, -1), (key2440, -1), (key2482, -1), (key2392, -1), (key2409, -1), (key2381, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1)]

def rawRow15120 : Integer.Sparse Key := [(key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2543, -1), (key2543, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2543, -1), (key2543, -1), (key2381, 2), (key2381, 2), (key2409, 2), (key2409, 2), (key2538, 2), (key2538, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1)]

def rawRow15121 : Integer.Sparse Key := [(key2482, -1), (key2543, -1), (key2392, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2482, -1), (key2543, -1), (key2392, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2409, 2), (key2538, 2), (key2381, 2), (key2538, 2), (key2381, 2), (key2409, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1)]

def rawRow15122 : Integer.Sparse Key := [(key2543, -1), (key2482, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2543, -1), (key2482, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2538, 2), (key2409, 2), (key2538, 2), (key2381, 2), (key2409, 2), (key2381, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1)]

def rawRow15123 : Integer.Sparse Key := [(key1277, -2), (key1277, -2), (key1283, -2), (key1283, 6), (key1700, -2), (key1700, -2), (key1706, -2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1855, 2), (key1855, 2), (key1706, -2), (key1855, -2), (key1855, -2), (key1756, 6), (key1756, -2), (key1886, -2), (key1886, -2)]

def rawRow15124 : Integer.Sparse Key := [(key1277, -2), (key1283, -2), (key1277, -2), (key1283, 6), (key1700, -2), (key1706, -2), (key1700, -2), (key1851, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1855, -2), (key1706, -2), (key1855, -2), (key1756, 6), (key1886, -2), (key1756, -2), (key1886, -2)]

def rawRow15125 : Integer.Sparse Key := [(key1283, -2), (key1277, -2), (key1277, -2), (key1283, 6), (key1706, -2), (key1700, -2), (key1700, -2), (key1855, 2), (key1851, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1700, 2), (key1855, -2), (key1855, -2), (key1706, -2), (key1756, 6), (key1886, -2), (key1886, -2), (key1756, -2)]

def rawRow15126 : Integer.Sparse Key := [(key1277, -2), (key1283, -2), (key1283, -2), (key1277, 6), (key1851, -2), (key1855, -2), (key1855, -2), (key1700, 2), (key1706, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1855, 2), (key1700, -2), (key1700, -2), (key1851, -2), (key1886, 6), (key1756, -2), (key1756, -2), (key1886, -2)]

def rawRow15127 : Integer.Sparse Key := [(key1283, -2), (key1277, -2), (key1283, -2), (key1277, 6), (key1855, -2), (key1851, -2), (key1855, -2), (key1706, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1700, -2), (key1851, -2), (key1700, -2), (key1886, 6), (key1756, -2), (key1886, -2), (key1756, -2)]

def rawRow15128 : Integer.Sparse Key := [(key1283, -2), (key1283, -2), (key1277, -2), (key1277, 6), (key1855, -2), (key1855, -2), (key1851, -2), (key1855, 2), (key1855, 2), (key1706, 2), (key1706, 2), (key1700, 2), (key1700, 2), (key1851, -2), (key1700, -2), (key1700, -2), (key1886, 6), (key1886, -2), (key1756, -2), (key1756, -2)]

def rawRow15129 : Integer.Sparse Key := [(key1700, -2), (key1700, -2), (key1706, -2), (key1756, 6), (key1277, -2), (key1277, -2), (key1283, -2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1855, 2), (key1855, 2), (key1756, -2), (key1886, -2), (key1886, -2), (key1283, 6), (key1706, -2), (key1855, -2), (key1855, -2)]

def rawRow15130 : Integer.Sparse Key := [(key1700, -2), (key1706, -2), (key1700, -2), (key1756, 6), (key1277, -2), (key1283, -2), (key1277, -2), (key1851, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1886, -2), (key1756, -2), (key1886, -2), (key1283, 6), (key1855, -2), (key1706, -2), (key1855, -2)]

def rawRow15131 : Integer.Sparse Key := [(key1706, -2), (key1700, -2), (key1700, -2), (key1756, 6), (key1283, -2), (key1277, -2), (key1277, -2), (key1855, 2), (key1851, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1700, 2), (key1886, -2), (key1886, -2), (key1756, -2), (key1283, 6), (key1855, -2), (key1855, -2), (key1706, -2)]

def rawRow15132 : Integer.Sparse Key := [(key1700, -2), (key1706, -2), (key1756, -2), (key1700, 6), (key1851, -2), (key1855, -2), (key1886, -2), (key1277, 2), (key1283, 2), (key1700, 2), (key1855, 2), (key1756, 2), (key1886, 2), (key1277, -2), (key1700, -2), (key1851, -2), (key1855, 6), (key1283, -2), (key1706, -2), (key1855, -2)]

def rawRow15133 : Integer.Sparse Key := [(key1706, -2), (key1700, -2), (key1756, -2), (key1700, 6), (key1855, -2), (key1851, -2), (key1886, -2), (key1283, 2), (key1277, 2), (key1855, 2), (key1700, 2), (key1886, 2), (key1756, 2), (key1277, -2), (key1851, -2), (key1700, -2), (key1855, 6), (key1283, -2), (key1855, -2), (key1706, -2)]

def rawRow15134 : Integer.Sparse Key := [(key1700, -2), (key1756, -2), (key1706, -2), (key1700, 6), (key1851, -2), (key1886, -2), (key1855, -2), (key1700, 2), (key1756, 2), (key1277, 2), (key1886, 2), (key1283, 2), (key1855, 2), (key1700, -2), (key1277, -2), (key1851, -2), (key1855, 6), (key1706, -2), (key1283, -2), (key1855, -2)]

def rawRow15135 : Integer.Sparse Key := [(key1756, -2), (key1700, -2), (key1706, -2), (key1700, 6), (key1886, -2), (key1851, -2), (key1855, -2), (key1756, 2), (key1700, 2), (key1886, 2), (key1277, 2), (key1855, 2), (key1283, 2), (key1700, -2), (key1851, -2), (key1277, -2), (key1855, 6), (key1706, -2), (key1855, -2), (key1283, -2)]

def rawRow15136 : Integer.Sparse Key := [(key1706, -2), (key1756, -2), (key1700, -2), (key1700, 6), (key1855, -2), (key1886, -2), (key1851, -2), (key1855, 2), (key1886, 2), (key1283, 2), (key1756, 2), (key1277, 2), (key1700, 2), (key1851, -2), (key1277, -2), (key1700, -2), (key1855, 6), (key1855, -2), (key1283, -2), (key1706, -2)]

def rawRow15137 : Integer.Sparse Key := [(key1756, -2), (key1706, -2), (key1700, -2), (key1700, 6), (key1886, -2), (key1855, -2), (key1851, -2), (key1886, 2), (key1855, 2), (key1756, 2), (key1283, 2), (key1700, 2), (key1277, 2), (key1851, -2), (key1700, -2), (key1277, -2), (key1855, 6), (key1855, -2), (key1706, -2), (key1283, -2)]

def rawRow15138 : Integer.Sparse Key := [(key1851, -2), (key1855, -2), (key1855, -2), (key1886, 6), (key1277, -2), (key1283, -2), (key1283, -2), (key1700, 2), (key1706, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1855, 2), (key1756, -2), (key1756, -2), (key1886, -2), (key1277, 6), (key1700, -2), (key1700, -2), (key1851, -2)]

def rawRow15139 : Integer.Sparse Key := [(key1855, -2), (key1851, -2), (key1855, -2), (key1886, 6), (key1283, -2), (key1277, -2), (key1283, -2), (key1706, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1756, -2), (key1886, -2), (key1756, -2), (key1277, 6), (key1700, -2), (key1851, -2), (key1700, -2)]

def rawRow15140 : Integer.Sparse Key := [(key1855, -2), (key1855, -2), (key1851, -2), (key1886, 6), (key1283, -2), (key1283, -2), (key1277, -2), (key1855, 2), (key1855, 2), (key1706, 2), (key1706, 2), (key1700, 2), (key1700, 2), (key1886, -2), (key1756, -2), (key1756, -2), (key1277, 6), (key1851, -2), (key1700, -2), (key1700, -2)]

def rawRow15141 : Integer.Sparse Key := [(key1851, -2), (key1855, -2), (key1886, -2), (key1855, 6), (key1700, -2), (key1706, -2), (key1756, -2), (key1277, 2), (key1283, 2), (key1700, 2), (key1855, 2), (key1756, 2), (key1886, 2), (key1283, -2), (key1706, -2), (key1855, -2), (key1700, 6), (key1277, -2), (key1700, -2), (key1851, -2)]

def rawRow15142 : Integer.Sparse Key := [(key1855, -2), (key1851, -2), (key1886, -2), (key1855, 6), (key1706, -2), (key1700, -2), (key1756, -2), (key1283, 2), (key1277, 2), (key1855, 2), (key1700, 2), (key1886, 2), (key1756, 2), (key1283, -2), (key1855, -2), (key1706, -2), (key1700, 6), (key1277, -2), (key1851, -2), (key1700, -2)]

def rawRow15143 : Integer.Sparse Key := [(key1851, -2), (key1886, -2), (key1855, -2), (key1855, 6), (key1700, -2), (key1756, -2), (key1706, -2), (key1700, 2), (key1756, 2), (key1277, 2), (key1886, 2), (key1283, 2), (key1855, 2), (key1706, -2), (key1283, -2), (key1855, -2), (key1700, 6), (key1700, -2), (key1277, -2), (key1851, -2)]

def rawRow15144 : Integer.Sparse Key := [(key1886, -2), (key1851, -2), (key1855, -2), (key1855, 6), (key1756, -2), (key1700, -2), (key1706, -2), (key1756, 2), (key1700, 2), (key1886, 2), (key1277, 2), (key1855, 2), (key1283, 2), (key1706, -2), (key1855, -2), (key1283, -2), (key1700, 6), (key1700, -2), (key1851, -2), (key1277, -2)]

def rawRow15145 : Integer.Sparse Key := [(key1855, -2), (key1886, -2), (key1851, -2), (key1855, 6), (key1706, -2), (key1756, -2), (key1700, -2), (key1855, 2), (key1886, 2), (key1283, 2), (key1756, 2), (key1277, 2), (key1700, 2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, 6), (key1851, -2), (key1277, -2), (key1700, -2)]

def rawRow15146 : Integer.Sparse Key := [(key1886, -2), (key1855, -2), (key1851, -2), (key1855, 6), (key1756, -2), (key1706, -2), (key1700, -2), (key1886, 2), (key1855, 2), (key1756, 2), (key1283, 2), (key1700, 2), (key1277, 2), (key1855, -2), (key1706, -2), (key1283, -2), (key1700, 6), (key1851, -2), (key1700, -2), (key1277, -2)]

def rawRow15147 : Integer.Sparse Key := [(key1855, -2), (key1855, -2), (key1886, -2), (key1851, 6), (key1855, -2), (key1855, -2), (key1886, -2), (key1283, 2), (key1283, 2), (key1706, 2), (key1706, 2), (key1756, 2), (key1756, 2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, 6), (key1277, -2), (key1700, -2), (key1700, -2)]

def rawRow15148 : Integer.Sparse Key := [(key1855, -2), (key1886, -2), (key1855, -2), (key1851, 6), (key1855, -2), (key1886, -2), (key1855, -2), (key1706, 2), (key1756, 2), (key1283, 2), (key1756, 2), (key1283, 2), (key1706, 2), (key1700, -2), (key1277, -2), (key1700, -2), (key1851, 6), (key1700, -2), (key1277, -2), (key1700, -2)]

def rawRow15149 : Integer.Sparse Key := [(key1886, -2), (key1855, -2), (key1855, -2), (key1851, 6), (key1886, -2), (key1855, -2), (key1855, -2), (key1756, 2), (key1706, 2), (key1756, 2), (key1283, 2), (key1706, 2), (key1283, 2), (key1700, -2), (key1700, -2), (key1277, -2), (key1851, 6), (key1700, -2), (key1700, -2), (key1277, -2)]

def rawRow15150 : Integer.Sparse Key := [(key2362, 2), (key2365, 2), (key2365, 2), (key2365, -2), (key2365, -2), (key2367, -2), (key2457, 2), (key2460, 2), (key2460, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow15151 : Integer.Sparse Key := [(key2365, 2), (key2362, 2), (key2365, 2), (key2365, -2), (key2367, -2), (key2365, -2), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow15152 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2362, 2), (key2367, -2), (key2365, -2), (key2365, -2), (key2460, 2), (key2460, 2), (key2457, 2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow15153 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2367, 2), (key2362, -2), (key2365, -2), (key2365, -2), (key2521, 2), (key2521, 2), (key2525, 2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, -1), (key2533, -1), (key2532, -1), (key2564, -1), (key2533, -1), (key2564, -1), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow15154 : Integer.Sparse Key := [(key2365, 2), (key2367, 2), (key2365, 2), (key2365, -2), (key2362, -2), (key2365, -2), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2533, -1), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow15155 : Integer.Sparse Key := [(key2367, 2), (key2365, 2), (key2365, 2), (key2365, -2), (key2365, -2), (key2362, -2), (key2525, 2), (key2521, 2), (key2521, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, -1), (key2564, -1), (key2533, -1), (key2533, -1), (key2532, -1), (key2532, -1), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow15156 : Integer.Sparse Key := [(key2457, 2), (key2460, 2), (key2460, 2), (key2521, -2), (key2521, -2), (key2525, -2), (key2362, 2), (key2365, 2), (key2365, 2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow15157 : Integer.Sparse Key := [(key2460, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2521, -2), (key2365, 2), (key2362, 2), (key2365, 2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow15158 : Integer.Sparse Key := [(key2460, 2), (key2460, 2), (key2457, 2), (key2525, -2), (key2521, -2), (key2521, -2), (key2365, 2), (key2365, 2), (key2362, 2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow15159 : Integer.Sparse Key := [(key2460, 2), (key2521, 2), (key2525, 2), (key2457, -2), (key2460, -2), (key2521, -2), (key2532, 2), (key2562, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, -1), (key2367, -1), (key2460, -1), (key2525, -1), (key2533, -1), (key2564, -1), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow15160 : Integer.Sparse Key := [(key2460, 2), (key2525, 2), (key2521, 2), (key2460, -2), (key2457, -2), (key2521, -2), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, -1), (key2365, -1), (key2525, -1), (key2460, -1), (key2564, -1), (key2533, -1), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow15161 : Integer.Sparse Key := [(key2521, 2), (key2460, 2), (key2525, 2), (key2457, -2), (key2521, -2), (key2460, -2), (key2562, 2), (key2532, 2), (key2564, 2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -1), (key2533, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow15162 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2460, 2), (key2521, -2), (key2457, -2), (key2460, -2), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2525, -1), (key2367, -1), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow15163 : Integer.Sparse Key := [(key2525, 2), (key2460, 2), (key2521, 2), (key2460, -2), (key2521, -2), (key2457, -2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2365, -1), (key2460, -1), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow15164 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2460, 2), (key2521, -2), (key2460, -2), (key2457, -2), (key2564, 2), (key2562, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, -1), (key2525, -1), (key2533, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow15165 : Integer.Sparse Key := [(key2532, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2), (key2564, -2), (key2365, 2), (key2365, 2), (key2367, 2), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2564, -1), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow15166 : Integer.Sparse Key := [(key2532, 2), (key2533, 2), (key2532, 2), (key2564, -2), (key2562, -2), (key2564, -2), (key2365, 2), (key2367, 2), (key2365, 2), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow15167 : Integer.Sparse Key := [(key2533, 2), (key2532, 2), (key2532, 2), (key2564, -2), (key2564, -2), (key2562, -2), (key2367, 2), (key2365, 2), (key2365, 2), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, -1), (key2521, -1), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow15168 : Integer.Sparse Key := [(key2532, 2), (key2562, 2), (key2564, 2), (key2532, -2), (key2533, -2), (key2564, -2), (key2460, 2), (key2521, 2), (key2525, 2), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, -1), (key2564, -1), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow15169 : Integer.Sparse Key := [(key2532, 2), (key2564, 2), (key2562, 2), (key2533, -2), (key2532, -2), (key2564, -2), (key2460, 2), (key2525, 2), (key2521, 2), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, -1), (key2525, -1), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow15170 : Integer.Sparse Key := [(key2562, 2), (key2532, 2), (key2564, 2), (key2532, -2), (key2564, -2), (key2533, -2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow15171 : Integer.Sparse Key := [(key2562, 2), (key2564, 2), (key2532, 2), (key2564, -2), (key2532, -2), (key2533, -2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, -1), (key2367, -1), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow15172 : Integer.Sparse Key := [(key2564, 2), (key2532, 2), (key2562, 2), (key2533, -2), (key2564, -2), (key2532, -2), (key2525, 2), (key2460, 2), (key2521, 2), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, -1), (key2460, -1), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow15173 : Integer.Sparse Key := [(key2564, 2), (key2562, 2), (key2532, 2), (key2564, -2), (key2533, -2), (key2532, -2), (key2525, 2), (key2521, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow15174 : Integer.Sparse Key := [(key2533, 2), (key2564, 2), (key2564, 2), (key2532, -2), (key2532, -2), (key2562, -2), (key2533, 2), (key2564, 2), (key2564, 2), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2532, -2), (key2532, -2), (key2562, -2), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2362, 4), (key2457, 4), (key2457, 4)]

def rawRow15175 : Integer.Sparse Key := [(key2564, 2), (key2533, 2), (key2564, 2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, 2), (key2533, 2), (key2564, 2), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2532, -2), (key2562, -2), (key2532, -2), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2457, 4), (key2362, 4), (key2457, 4)]

def rawRow15176 : Integer.Sparse Key := [(key2564, 2), (key2564, 2), (key2533, 2), (key2562, -2), (key2532, -2), (key2532, -2), (key2564, 2), (key2564, 2), (key2533, 2), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2365, -1), (key2562, -2), (key2532, -2), (key2532, -2), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2365, -1), (key2457, 4), (key2457, 4), (key2362, 4)]

def rawRow15177 : Integer.Sparse Key := [(key2843, 4), (key2843, 4), (key2880, 4), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15178 : Integer.Sparse Key := [(key2843, 4), (key2880, 4), (key2843, 4), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15179 : Integer.Sparse Key := [(key2880, 4), (key2843, 4), (key2843, 4), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15180 : Integer.Sparse Key := [(key2766, 4), (key2887, 4), (key2910, 4), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15181 : Integer.Sparse Key := [(key2766, 4), (key2910, 4), (key2887, 4), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2931, 4), (key2989, 4), (key2968, 4)]

def rawRow15182 : Integer.Sparse Key := [(key2887, 4), (key2766, 4), (key2910, 4), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15183 : Integer.Sparse Key := [(key2887, 4), (key2910, 4), (key2766, 4), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15184 : Integer.Sparse Key := [(key2910, 4), (key2766, 4), (key2887, 4), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15185 : Integer.Sparse Key := [(key2910, 4), (key2887, 4), (key2766, 4), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15186 : Integer.Sparse Key := [(key2843, 4), (key2843, 4), (key2880, 4), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15187 : Integer.Sparse Key := [(key2843, 4), (key2880, 4), (key2843, 4), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15188 : Integer.Sparse Key := [(key2880, 4), (key2843, 4), (key2843, 4), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15189 : Integer.Sparse Key := [(key2766, 4), (key2887, 4), (key2910, 4), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15190 : Integer.Sparse Key := [(key2766, 4), (key2910, 4), (key2887, 4), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, 4), (key2989, 4), (key2968, 4)]

def rawRow15191 : Integer.Sparse Key := [(key2887, 4), (key2766, 4), (key2910, 4), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15192 : Integer.Sparse Key := [(key2887, 4), (key2910, 4), (key2766, 4), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15193 : Integer.Sparse Key := [(key2910, 4), (key2766, 4), (key2887, 4), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15194 : Integer.Sparse Key := [(key2910, 4), (key2887, 4), (key2766, 4), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15195 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key1015, 6), (key1028, -2), (key1036, -2), (key1036, -2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1123, -2), (key1123, -2), (key1235, -2), (key1071, 6), (key1150, -2), (key1150, -2), (key1242, -2)]

def rawRow15196 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1015, 6), (key1036, -2), (key1028, -2), (key1036, -2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1123, -2), (key1235, -2), (key1123, -2), (key1071, 6), (key1150, -2), (key1242, -2), (key1150, -2)]

def rawRow15197 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, 6), (key1036, -2), (key1036, -2), (key1028, -2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, -2), (key1123, -2), (key1123, -2), (key1071, 6), (key1242, -2), (key1150, -2), (key1150, -2)]

def rawRow15198 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1015, -2), (key1001, 6), (key1106, -2), (key1114, -2), (key1123, -2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1036, -2), (key1114, -2), (key1232, -2), (key1150, 6), (key1071, -2), (key1150, -2), (key1242, -2)]

def rawRow15199 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1015, -2), (key1001, 6), (key1114, -2), (key1106, -2), (key1123, -2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1036, -2), (key1232, -2), (key1114, -2), (key1150, 6), (key1071, -2), (key1242, -2), (key1150, -2)]

def rawRow15200 : Integer.Sparse Key := [(key993, -2), (key1015, -2), (key1001, -2), (key1001, 6), (key1106, -2), (key1123, -2), (key1114, -2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1114, -2), (key1036, -2), (key1232, -2), (key1150, 6), (key1150, -2), (key1071, -2), (key1242, -2)]

def rawRow15201 : Integer.Sparse Key := [(key1015, -2), (key993, -2), (key1001, -2), (key1001, 6), (key1123, -2), (key1106, -2), (key1114, -2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1114, -2), (key1232, -2), (key1036, -2), (key1150, 6), (key1150, -2), (key1242, -2), (key1071, -2)]

def rawRow15202 : Integer.Sparse Key := [(key1001, -2), (key1015, -2), (key993, -2), (key1001, 6), (key1114, -2), (key1123, -2), (key1106, -2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1232, -2), (key1036, -2), (key1114, -2), (key1150, 6), (key1242, -2), (key1071, -2), (key1150, -2)]

def rawRow15203 : Integer.Sparse Key := [(key1015, -2), (key1001, -2), (key993, -2), (key1001, 6), (key1123, -2), (key1114, -2), (key1106, -2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1232, -2), (key1114, -2), (key1036, -2), (key1150, 6), (key1242, -2), (key1150, -2), (key1071, -2)]

def rawRow15204 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1071, 6), (key993, -2), (key1001, -2), (key1001, -2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1150, -2), (key1150, -2), (key1242, -2), (key1015, 6), (key1123, -2), (key1123, -2), (key1235, -2)]

def rawRow15205 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1071, 6), (key1001, -2), (key993, -2), (key1001, -2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1150, -2), (key1242, -2), (key1150, -2), (key1015, 6), (key1123, -2), (key1235, -2), (key1123, -2)]

def rawRow15206 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1071, 6), (key1001, -2), (key1001, -2), (key993, -2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, -2), (key1150, -2), (key1150, -2), (key1015, 6), (key1235, -2), (key1123, -2), (key1123, -2)]

def rawRow15207 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1123, -2), (key1150, 6), (key993, -2), (key1001, -2), (key1015, -2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1071, -2), (key1150, -2), (key1242, -2), (key1001, 6), (key1036, -2), (key1114, -2), (key1232, -2)]

def rawRow15208 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1123, -2), (key1150, 6), (key1001, -2), (key993, -2), (key1015, -2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1071, -2), (key1242, -2), (key1150, -2), (key1001, 6), (key1036, -2), (key1232, -2), (key1114, -2)]

def rawRow15209 : Integer.Sparse Key := [(key1106, -2), (key1123, -2), (key1114, -2), (key1150, 6), (key993, -2), (key1015, -2), (key1001, -2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1150, -2), (key1071, -2), (key1242, -2), (key1001, 6), (key1114, -2), (key1036, -2), (key1232, -2)]

def rawRow15210 : Integer.Sparse Key := [(key1123, -2), (key1106, -2), (key1114, -2), (key1150, 6), (key1015, -2), (key993, -2), (key1001, -2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1150, -2), (key1242, -2), (key1071, -2), (key1001, 6), (key1114, -2), (key1232, -2), (key1036, -2)]

def rawRow15211 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1106, -2), (key1150, 6), (key1001, -2), (key1015, -2), (key993, -2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1242, -2), (key1071, -2), (key1150, -2), (key1001, 6), (key1232, -2), (key1036, -2), (key1114, -2)]

def rawRow15212 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1106, -2), (key1150, 6), (key1015, -2), (key1001, -2), (key993, -2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, -2), (key1150, -2), (key1071, -2), (key1001, 6), (key1232, -2), (key1114, -2), (key1036, -2)]

def rawRow15213 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2388, 6), (key2762, -2), (key2768, -2), (key2768, -2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key2916, -2), (key2916, -2), (key2925, -2), (key3005, 6), (key3019, -2), (key3019, -2), (key3028, -2)]

def rawRow15214 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2388, 6), (key2768, -2), (key2762, -2), (key2768, -2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2916, -2), (key2925, -2), (key2916, -2), (key3005, 6), (key3019, -2), (key3028, -2), (key3019, -2)]

def rawRow15215 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, 6), (key2768, -2), (key2768, -2), (key2762, -2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key2925, -2), (key2916, -2), (key2916, -2), (key3005, 6), (key3028, -2), (key3019, -2), (key3019, -2)]

def rawRow15216 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2376, 6), (key2839, -2), (key2845, -2), (key2916, -2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key2768, -2), (key2845, -2), (key2876, -2), (key3019, 6), (key3005, -2), (key3019, -2), (key3028, -2)]

def rawRow15217 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2388, -2), (key2376, 6), (key2845, -2), (key2839, -2), (key2916, -2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2768, -2), (key2876, -2), (key2845, -2), (key3019, 6), (key3005, -2), (key3028, -2), (key3019, -2)]

def rawRow15218 : Integer.Sparse Key := [(key2370, -2), (key2388, -2), (key2376, -2), (key2376, 6), (key2839, -2), (key2916, -2), (key2845, -2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key2845, -2), (key2768, -2), (key2876, -2), (key3019, 6), (key3019, -2), (key3005, -2), (key3028, -2)]

def rawRow15219 : Integer.Sparse Key := [(key2388, -2), (key2370, -2), (key2376, -2), (key2376, 6), (key2916, -2), (key2839, -2), (key2845, -2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key2845, -2), (key2876, -2), (key2768, -2), (key3019, 6), (key3019, -2), (key3028, -2), (key3005, -2)]

def rawRow15220 : Integer.Sparse Key := [(key2376, -2), (key2388, -2), (key2370, -2), (key2376, 6), (key2845, -2), (key2916, -2), (key2839, -2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2876, -2), (key2768, -2), (key2845, -2), (key3019, 6), (key3028, -2), (key3005, -2), (key3019, -2)]

def rawRow15221 : Integer.Sparse Key := [(key2388, -2), (key2376, -2), (key2370, -2), (key2376, 6), (key2916, -2), (key2845, -2), (key2839, -2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key2876, -2), (key2845, -2), (key2768, -2), (key3019, 6), (key3028, -2), (key3019, -2), (key3005, -2)]

def rawRow15222 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2404, -2), (key2435, 6), (key2583, -2), (key2589, -2), (key2589, -2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key3019, -2), (key3019, -2), (key3028, -2), (key2604, 6), (key2916, -2), (key2916, -2), (key2925, -2)]

def rawRow15223 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2404, -2), (key2435, 6), (key2589, -2), (key2583, -2), (key2589, -2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key3019, -2), (key3028, -2), (key3019, -2), (key2604, 6), (key2916, -2), (key2925, -2), (key2916, -2)]

def rawRow15224 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2398, -2), (key2435, 6), (key2589, -2), (key2589, -2), (key2583, -2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key3028, -2), (key3019, -2), (key3019, -2), (key2604, 6), (key2925, -2), (key2916, -2), (key2916, -2)]

def rawRow15225 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2370, -2), (key2376, -2), (key2388, -2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2), (key2589, 6), (key2768, -2), (key2845, -2), (key2876, -2)]

def rawRow15226 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2478, -2), (key2501, 6), (key2376, -2), (key2370, -2), (key2388, -2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key3005, -2), (key3028, -2), (key3019, -2), (key2589, 6), (key2768, -2), (key2876, -2), (key2845, -2)]

def rawRow15227 : Integer.Sparse Key := [(key2464, -2), (key2478, -2), (key2470, -2), (key2501, 6), (key2370, -2), (key2388, -2), (key2376, -2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key3019, -2), (key3005, -2), (key3028, -2), (key2589, 6), (key2845, -2), (key2768, -2), (key2876, -2)]

def rawRow15228 : Integer.Sparse Key := [(key2478, -2), (key2464, -2), (key2470, -2), (key2501, 6), (key2388, -2), (key2370, -2), (key2376, -2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key3019, -2), (key3028, -2), (key3005, -2), (key2589, 6), (key2845, -2), (key2876, -2), (key2768, -2)]

def rawRow15229 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2464, -2), (key2501, 6), (key2376, -2), (key2388, -2), (key2370, -2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key3028, -2), (key3005, -2), (key3019, -2), (key2589, 6), (key2876, -2), (key2768, -2), (key2845, -2)]

def rawRow15230 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2464, -2), (key2501, 6), (key2388, -2), (key2376, -2), (key2370, -2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key3028, -2), (key3019, -2), (key3005, -2), (key2589, 6), (key2876, -2), (key2845, -2), (key2768, -2)]

def rawRow15231 : Integer.Sparse Key := [(key2610, 6), (key2626, -2), (key2626, -2), (key2635, -2), (key2665, 6), (key2700, -2), (key2700, -2), (key2721, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15232 : Integer.Sparse Key := [(key2610, 6), (key2626, -2), (key2635, -2), (key2626, -2), (key2665, 6), (key2700, -2), (key2721, -2), (key2700, -2), (key2780, -2), (key2789, -2), (key2780, -2), (key2803, -2), (key2824, -2), (key2803, -2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow15233 : Integer.Sparse Key := [(key2610, 6), (key2635, -2), (key2626, -2), (key2626, -2), (key2665, 6), (key2721, -2), (key2700, -2), (key2700, -2), (key2789, -2), (key2780, -2), (key2780, -2), (key2824, -2), (key2803, -2), (key2803, -2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow15234 : Integer.Sparse Key := [(key2626, 6), (key2610, -2), (key2626, -2), (key2635, -2), (key2700, 6), (key2665, -2), (key2700, -2), (key2721, -2), (key2803, -2), (key2853, -2), (key2855, -2), (key2780, -2), (key2853, -2), (key2865, -2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow15235 : Integer.Sparse Key := [(key2626, 6), (key2610, -2), (key2635, -2), (key2626, -2), (key2700, 6), (key2665, -2), (key2721, -2), (key2700, -2), (key2803, -2), (key2855, -2), (key2853, -2), (key2780, -2), (key2865, -2), (key2853, -2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow15236 : Integer.Sparse Key := [(key2626, 6), (key2626, -2), (key2610, -2), (key2635, -2), (key2700, 6), (key2700, -2), (key2665, -2), (key2721, -2), (key2853, -2), (key2803, -2), (key2855, -2), (key2853, -2), (key2780, -2), (key2865, -2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow15237 : Integer.Sparse Key := [(key2626, 6), (key2626, -2), (key2635, -2), (key2610, -2), (key2700, 6), (key2700, -2), (key2721, -2), (key2665, -2), (key2853, -2), (key2855, -2), (key2803, -2), (key2853, -2), (key2865, -2), (key2780, -2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow15238 : Integer.Sparse Key := [(key2626, 6), (key2635, -2), (key2610, -2), (key2626, -2), (key2700, 6), (key2721, -2), (key2665, -2), (key2700, -2), (key2855, -2), (key2803, -2), (key2853, -2), (key2865, -2), (key2780, -2), (key2853, -2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow15239 : Integer.Sparse Key := [(key2626, 6), (key2635, -2), (key2626, -2), (key2610, -2), (key2700, 6), (key2721, -2), (key2700, -2), (key2665, -2), (key2855, -2), (key2853, -2), (key2803, -2), (key2865, -2), (key2853, -2), (key2780, -2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow15240 : Integer.Sparse Key := [(key2665, 6), (key2780, -2), (key2780, -2), (key2789, -2), (key2610, 6), (key2803, -2), (key2803, -2), (key2824, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

def rawRow15241 : Integer.Sparse Key := [(key2665, 6), (key2780, -2), (key2789, -2), (key2780, -2), (key2610, 6), (key2803, -2), (key2824, -2), (key2803, -2), (key2626, -2), (key2635, -2), (key2626, -2), (key2700, -2), (key2721, -2), (key2700, -2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow15242 : Integer.Sparse Key := [(key2665, 6), (key2789, -2), (key2780, -2), (key2780, -2), (key2610, 6), (key2824, -2), (key2803, -2), (key2803, -2), (key2635, -2), (key2626, -2), (key2626, -2), (key2721, -2), (key2700, -2), (key2700, -2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow15243 : Integer.Sparse Key := [(key2700, 6), (key2803, -2), (key2853, -2), (key2855, -2), (key2626, 6), (key2780, -2), (key2853, -2), (key2865, -2), (key2610, -2), (key2626, -2), (key2635, -2), (key2665, -2), (key2700, -2), (key2721, -2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow15244 : Integer.Sparse Key := [(key2700, 6), (key2803, -2), (key2855, -2), (key2853, -2), (key2626, 6), (key2780, -2), (key2865, -2), (key2853, -2), (key2610, -2), (key2635, -2), (key2626, -2), (key2665, -2), (key2721, -2), (key2700, -2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow15245 : Integer.Sparse Key := [(key2700, 6), (key2853, -2), (key2803, -2), (key2855, -2), (key2626, 6), (key2853, -2), (key2780, -2), (key2865, -2), (key2626, -2), (key2610, -2), (key2635, -2), (key2700, -2), (key2665, -2), (key2721, -2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow15246 : Integer.Sparse Key := [(key2700, 6), (key2853, -2), (key2855, -2), (key2803, -2), (key2626, 6), (key2853, -2), (key2865, -2), (key2780, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow15247 : Integer.Sparse Key := [(key2700, 6), (key2855, -2), (key2803, -2), (key2853, -2), (key2626, 6), (key2865, -2), (key2780, -2), (key2853, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow15248 : Integer.Sparse Key := [(key2700, 6), (key2855, -2), (key2853, -2), (key2803, -2), (key2626, 6), (key2865, -2), (key2853, -2), (key2780, -2), (key2635, -2), (key2626, -2), (key2610, -2), (key2721, -2), (key2700, -2), (key2665, -2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow15249 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1000, -2), (key1014, 6), (key1029, -2), (key1035, -2), (key1035, -2), (key1107, 2), (key1113, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1231, 2), (key1122, -2), (key1122, -2), (key1234, -2), (key1070, 6), (key1149, -2), (key1149, -2), (key1241, -2)]

def rawRow15250 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1000, -2), (key1014, 6), (key1035, -2), (key1029, -2), (key1035, -2), (key1113, 2), (key1107, 2), (key1231, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1122, -2), (key1234, -2), (key1122, -2), (key1070, 6), (key1149, -2), (key1241, -2), (key1149, -2)]

def rawRow15251 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key994, -2), (key1014, 6), (key1035, -2), (key1035, -2), (key1029, -2), (key1231, 2), (key1231, 2), (key1113, 2), (key1113, 2), (key1107, 2), (key1107, 2), (key1234, -2), (key1122, -2), (key1122, -2), (key1070, 6), (key1241, -2), (key1149, -2), (key1149, -2)]

def rawRow15252 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1014, -2), (key1000, 6), (key1107, -2), (key1113, -2), (key1122, -2), (key1029, 2), (key1035, 2), (key1107, 2), (key1231, 2), (key1122, 2), (key1234, 2), (key1035, -2), (key1113, -2), (key1231, -2), (key1149, 6), (key1070, -2), (key1149, -2), (key1241, -2)]

def rawRow15253 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1014, -2), (key1000, 6), (key1113, -2), (key1107, -2), (key1122, -2), (key1035, 2), (key1029, 2), (key1231, 2), (key1107, 2), (key1234, 2), (key1122, 2), (key1035, -2), (key1231, -2), (key1113, -2), (key1149, 6), (key1070, -2), (key1241, -2), (key1149, -2)]

def rawRow15254 : Integer.Sparse Key := [(key994, -2), (key1014, -2), (key1000, -2), (key1000, 6), (key1107, -2), (key1122, -2), (key1113, -2), (key1107, 2), (key1122, 2), (key1029, 2), (key1234, 2), (key1035, 2), (key1231, 2), (key1113, -2), (key1035, -2), (key1231, -2), (key1149, 6), (key1149, -2), (key1070, -2), (key1241, -2)]

def rawRow15255 : Integer.Sparse Key := [(key1014, -2), (key994, -2), (key1000, -2), (key1000, 6), (key1122, -2), (key1107, -2), (key1113, -2), (key1122, 2), (key1107, 2), (key1234, 2), (key1029, 2), (key1231, 2), (key1035, 2), (key1113, -2), (key1231, -2), (key1035, -2), (key1149, 6), (key1149, -2), (key1241, -2), (key1070, -2)]

def rawRow15256 : Integer.Sparse Key := [(key1000, -2), (key1014, -2), (key994, -2), (key1000, 6), (key1113, -2), (key1122, -2), (key1107, -2), (key1231, 2), (key1234, 2), (key1035, 2), (key1122, 2), (key1029, 2), (key1107, 2), (key1231, -2), (key1035, -2), (key1113, -2), (key1149, 6), (key1241, -2), (key1070, -2), (key1149, -2)]

def rawRow15257 : Integer.Sparse Key := [(key1014, -2), (key1000, -2), (key994, -2), (key1000, 6), (key1122, -2), (key1113, -2), (key1107, -2), (key1234, 2), (key1231, 2), (key1122, 2), (key1035, 2), (key1107, 2), (key1029, 2), (key1231, -2), (key1113, -2), (key1035, -2), (key1149, 6), (key1241, -2), (key1149, -2), (key1070, -2)]

def rawRow15258 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1035, -2), (key1070, 6), (key994, -2), (key1000, -2), (key1000, -2), (key1107, 2), (key1113, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1231, 2), (key1149, -2), (key1149, -2), (key1241, -2), (key1014, 6), (key1122, -2), (key1122, -2), (key1234, -2)]

def rawRow15259 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1035, -2), (key1070, 6), (key1000, -2), (key994, -2), (key1000, -2), (key1113, 2), (key1107, 2), (key1231, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1149, -2), (key1241, -2), (key1149, -2), (key1014, 6), (key1122, -2), (key1234, -2), (key1122, -2)]

def rawRow15260 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1029, -2), (key1070, 6), (key1000, -2), (key1000, -2), (key994, -2), (key1231, 2), (key1231, 2), (key1113, 2), (key1113, 2), (key1107, 2), (key1107, 2), (key1241, -2), (key1149, -2), (key1149, -2), (key1014, 6), (key1234, -2), (key1122, -2), (key1122, -2)]

def rawRow15261 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1122, -2), (key1149, 6), (key994, -2), (key1000, -2), (key1014, -2), (key1029, 2), (key1035, 2), (key1107, 2), (key1231, 2), (key1122, 2), (key1234, 2), (key1070, -2), (key1149, -2), (key1241, -2), (key1000, 6), (key1035, -2), (key1113, -2), (key1231, -2)]

def rawRow15262 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1122, -2), (key1149, 6), (key1000, -2), (key994, -2), (key1014, -2), (key1035, 2), (key1029, 2), (key1231, 2), (key1107, 2), (key1234, 2), (key1122, 2), (key1070, -2), (key1241, -2), (key1149, -2), (key1000, 6), (key1035, -2), (key1231, -2), (key1113, -2)]

def rawRow15263 : Integer.Sparse Key := [(key1107, -2), (key1122, -2), (key1113, -2), (key1149, 6), (key994, -2), (key1014, -2), (key1000, -2), (key1107, 2), (key1122, 2), (key1029, 2), (key1234, 2), (key1035, 2), (key1231, 2), (key1149, -2), (key1070, -2), (key1241, -2), (key1000, 6), (key1113, -2), (key1035, -2), (key1231, -2)]

def rawRow15264 : Integer.Sparse Key := [(key1122, -2), (key1107, -2), (key1113, -2), (key1149, 6), (key1014, -2), (key994, -2), (key1000, -2), (key1122, 2), (key1107, 2), (key1234, 2), (key1029, 2), (key1231, 2), (key1035, 2), (key1149, -2), (key1241, -2), (key1070, -2), (key1000, 6), (key1113, -2), (key1231, -2), (key1035, -2)]

def rawRow15265 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1107, -2), (key1149, 6), (key1000, -2), (key1014, -2), (key994, -2), (key1231, 2), (key1234, 2), (key1035, 2), (key1122, 2), (key1029, 2), (key1107, 2), (key1241, -2), (key1070, -2), (key1149, -2), (key1000, 6), (key1231, -2), (key1035, -2), (key1113, -2)]

def rawRow15266 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1107, -2), (key1149, 6), (key1014, -2), (key1000, -2), (key994, -2), (key1234, 2), (key1231, 2), (key1122, 2), (key1035, 2), (key1107, 2), (key1029, 2), (key1241, -2), (key1149, -2), (key1070, -2), (key1000, 6), (key1231, -2), (key1113, -2), (key1035, -2)]

def rawRow15267 : Integer.Sparse Key := [(key1116, 4), (key1116, 4), (key1233, 4), (key1125, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1152, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1174, 4), (key1174, 4), (key1247, 4)]

def rawRow15268 : Integer.Sparse Key := [(key1116, 4), (key1233, 4), (key1116, 4), (key1130, -2), (key1125, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1174, 4), (key1247, 4), (key1174, 4)]

def rawRow15269 : Integer.Sparse Key := [(key1233, 4), (key1116, 4), (key1116, 4), (key1236, -2), (key1236, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1243, -2), (key1243, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1247, 4), (key1174, 4), (key1174, 4)]

def rawRow15270 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1236, 4), (key1038, -2), (key1044, -2), (key1116, -2), (key1233, -2), (key1130, -2), (key1236, -2), (key1073, -2), (key1080, -2), (key1152, -2), (key1243, -2), (key1174, -2), (key1247, -2), (key1080, 4), (key1159, 4), (key1243, 4)]

def rawRow15271 : Integer.Sparse Key := [(key1038, 4), (key1236, 4), (key1125, 4), (key1044, -2), (key1038, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1130, -2), (key1080, -2), (key1073, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1080, 4), (key1243, 4), (key1159, 4)]

def rawRow15272 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1236, 4), (key1116, -2), (key1130, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1152, -2), (key1174, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1159, 4), (key1080, 4), (key1243, 4)]

def rawRow15273 : Integer.Sparse Key := [(key1125, 4), (key1236, 4), (key1038, 4), (key1130, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1233, -2), (key1044, -2), (key1174, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1243, -2), (key1080, -2), (key1159, 4), (key1243, 4), (key1080, 4)]

def rawRow15274 : Integer.Sparse Key := [(key1236, 4), (key1038, 4), (key1125, 4), (key1233, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1038, -2), (key1116, -2), (key1243, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1073, -2), (key1152, -2), (key1243, 4), (key1080, 4), (key1159, 4)]

def rawRow15275 : Integer.Sparse Key := [(key1236, 4), (key1125, 4), (key1038, 4), (key1236, -2), (key1233, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1247, -2), (key1243, -2), (key1174, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1243, 4), (key1159, 4), (key1080, 4)]

def rawRow15276 : Integer.Sparse Key := [(key1116, 4), (key1116, 4), (key1233, 4), (key1152, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1125, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1174, 4), (key1174, 4), (key1247, 4)]

def rawRow15277 : Integer.Sparse Key := [(key1116, 4), (key1233, 4), (key1116, 4), (key1159, -2), (key1152, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1174, 4), (key1247, 4), (key1174, 4)]

def rawRow15278 : Integer.Sparse Key := [(key1233, 4), (key1116, 4), (key1116, 4), (key1243, -2), (key1243, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1236, -2), (key1236, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1247, 4), (key1174, 4), (key1174, 4)]

def rawRow15279 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1236, 4), (key1073, -2), (key1080, -2), (key1152, -2), (key1243, -2), (key1174, -2), (key1247, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1233, -2), (key1130, -2), (key1236, -2), (key1080, 4), (key1159, 4), (key1243, 4)]

def rawRow15280 : Integer.Sparse Key := [(key1038, 4), (key1236, 4), (key1125, 4), (key1080, -2), (key1073, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1044, -2), (key1038, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1130, -2), (key1080, 4), (key1243, 4), (key1159, 4)]

def rawRow15281 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1236, 4), (key1152, -2), (key1174, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1116, -2), (key1130, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1159, 4), (key1080, 4), (key1243, 4)]

def rawRow15282 : Integer.Sparse Key := [(key1125, 4), (key1236, 4), (key1038, 4), (key1174, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1243, -2), (key1080, -2), (key1130, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1233, -2), (key1044, -2), (key1159, 4), (key1243, 4), (key1080, 4)]

def rawRow15283 : Integer.Sparse Key := [(key1236, 4), (key1038, 4), (key1125, 4), (key1243, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1073, -2), (key1152, -2), (key1233, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1038, -2), (key1116, -2), (key1243, 4), (key1080, 4), (key1159, 4)]

def rawRow15284 : Integer.Sparse Key := [(key1236, 4), (key1125, 4), (key1038, 4), (key1247, -2), (key1243, -2), (key1174, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1236, -2), (key1233, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1243, 4), (key1159, 4), (key1080, 4)]

def rawRow15285 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key2922, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key3021, -1), (key3022, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key3025, -1)]

def rawRow15286 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key3022, -1), (key3021, -1), (key3025, -1), (key3021, -1), (key3025, -1), (key3022, -1)]

def rawRow15287 : Integer.Sparse Key := [(key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, -1), (key2918, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key3025, -1), (key3025, -1), (key3022, -1), (key3022, -1), (key3021, -1), (key3021, -1)]

def rawRow15288 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2669, 2), (key2704, 2), (key2724, 2), (key2778, -1), (key2784, -1), (key2851, -1), (key2868, -1), (key2918, -1), (key2922, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, -1), (key2868, -1), (key3007, 2), (key3021, 2), (key3025, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, -1)]

def rawRow15289 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2669, 2), (key2724, 2), (key2704, 2), (key2784, -1), (key2778, -1), (key2868, -1), (key2851, -1), (key2922, -1), (key2918, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2858, -1), (key3007, 2), (key3025, 2), (key3021, 2), (key3009, -1), (key3007, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3022, -1)]

def rawRow15290 : Integer.Sparse Key := [(key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2704, 2), (key2669, 2), (key2724, 2), (key2851, -1), (key2918, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2807, -1), (key2858, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2827, -1), (key3021, 2), (key3007, 2), (key3025, 2), (key3011, -1), (key3022, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3016, -1)]

def rawRow15291 : Integer.Sparse Key := [(key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2704, 2), (key2724, 2), (key2669, 2), (key2918, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2868, -1), (key2784, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key2858, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2827, -1), (key2792, -1), (key3021, 2), (key3025, 2), (key3007, 2), (key3022, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3016, -1), (key3009, -1)]

def rawRow15292 : Integer.Sparse Key := [(key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2724, 2), (key2669, 2), (key2704, 2), (key2868, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2778, -1), (key2851, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, -1), (key2807, -1), (key3025, 2), (key3007, 2), (key3021, 2), (key3016, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key3007, -1), (key3011, -1)]

def rawRow15293 : Integer.Sparse Key := [(key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2724, 2), (key2704, 2), (key2669, 2), (key2922, -1), (key2868, -1), (key2918, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, -1), (key2784, -1), (key3025, 2), (key3021, 2), (key3007, 2), (key3025, -1), (key3016, -1), (key3022, -1), (key3009, -1), (key3011, -1), (key3007, -1)]

def rawRow15294 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key3021, -1), (key3022, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key3025, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key2922, -1)]

def rawRow15295 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key3022, -1), (key3021, -1), (key3025, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, -1), (key2919, -1)]

def rawRow15296 : Integer.Sparse Key := [(key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key3025, -1), (key3025, -1), (key3022, -1), (key3022, -1), (key3021, -1), (key3021, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, -1), (key2918, -1)]

def rawRow15297 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2724, 2), (key2868, 2), (key3025, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, -1), (key2669, 2), (key2704, 2), (key2724, 2), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, -1), (key2868, -1)]

def rawRow15298 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2724, 2), (key3025, 2), (key2868, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key3009, -1), (key3007, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3022, -1), (key2669, 2), (key2724, 2), (key2704, 2), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2858, -1)]

def rawRow15299 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2868, 2), (key2724, 2), (key3025, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key3011, -1), (key3022, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3016, -1), (key2704, 2), (key2669, 2), (key2724, 2), (key2807, -1), (key2858, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2827, -1)]

def rawRow15300 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2868, 2), (key3025, 2), (key2724, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key3022, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3016, -1), (key3009, -1), (key2704, 2), (key2724, 2), (key2669, 2), (key2858, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2827, -1), (key2792, -1)]

def rawRow15301 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key3025, 2), (key2724, 2), (key2868, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key3016, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key3007, -1), (key3011, -1), (key2724, 2), (key2669, 2), (key2704, 2), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, -1), (key2807, -1)]

def rawRow15302 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 2), (key2868, 2), (key2724, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, -1), (key3016, -1), (key3022, -1), (key3009, -1), (key3011, -1), (key3007, -1), (key2724, 2), (key2704, 2), (key2669, 2), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, -1), (key2784, -1)]

def rawRow15303 : Integer.Sparse Key := [(key2681, 4), (key2681, 4), (key2688, 4), (key2712, -4), (key2714, -4), (key2714, -4), (key2815, -4), (key2817, -4), (key2817, -4), (key2863, 12)]

def rawRow15304 : Integer.Sparse Key := [(key2681, 4), (key2688, 4), (key2681, 4), (key2714, -4), (key2712, -4), (key2714, -4), (key2817, -4), (key2815, -4), (key2817, -4), (key2863, 12)]

def rawRow15305 : Integer.Sparse Key := [(key2688, 4), (key2681, 4), (key2681, 4), (key2714, -4), (key2714, -4), (key2712, -4), (key2817, -4), (key2817, -4), (key2815, -4), (key2863, 12)]

def rawRow15306 : Integer.Sparse Key := [(key2681, 4), (key2712, 4), (key2714, 4), (key2681, -4), (key2688, -4), (key2714, -4), (key2815, -4), (key2817, -4), (key2863, -4), (key2817, 12)]

def rawRow15307 : Integer.Sparse Key := [(key2681, 4), (key2714, 4), (key2712, 4), (key2688, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2815, -4), (key2863, -4), (key2817, 12)]

def rawRow15308 : Integer.Sparse Key := [(key2712, 4), (key2681, 4), (key2714, 4), (key2681, -4), (key2714, -4), (key2688, -4), (key2815, -4), (key2863, -4), (key2817, -4), (key2817, 12)]

def rawRow15309 : Integer.Sparse Key := [(key2712, 4), (key2714, 4), (key2681, 4), (key2714, -4), (key2681, -4), (key2688, -4), (key2863, -4), (key2815, -4), (key2817, -4), (key2817, 12)]

def rawRow15310 : Integer.Sparse Key := [(key2714, 4), (key2681, 4), (key2712, 4), (key2688, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2863, -4), (key2815, -4), (key2817, 12)]

def rawRow15311 : Integer.Sparse Key := [(key2714, 4), (key2712, 4), (key2681, 4), (key2714, -4), (key2688, -4), (key2681, -4), (key2863, -4), (key2817, -4), (key2815, -4), (key2817, 12)]

def rawRow15312 : Integer.Sparse Key := [(key2681, 4), (key2681, 4), (key2688, 4), (key2815, -4), (key2817, -4), (key2817, -4), (key2712, -4), (key2714, -4), (key2714, -4), (key2863, 12)]

def rawRow15313 : Integer.Sparse Key := [(key2681, 4), (key2688, 4), (key2681, 4), (key2817, -4), (key2815, -4), (key2817, -4), (key2714, -4), (key2712, -4), (key2714, -4), (key2863, 12)]

def rawRow15314 : Integer.Sparse Key := [(key2688, 4), (key2681, 4), (key2681, 4), (key2817, -4), (key2817, -4), (key2815, -4), (key2714, -4), (key2714, -4), (key2712, -4), (key2863, 12)]

def rawRow15315 : Integer.Sparse Key := [(key2681, 4), (key2815, 4), (key2817, 4), (key2681, -4), (key2688, -4), (key2817, -4), (key2712, -4), (key2714, -4), (key2863, -4), (key2714, 12)]

def rawRow15316 : Integer.Sparse Key := [(key2681, 4), (key2817, 4), (key2815, 4), (key2688, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2712, -4), (key2863, -4), (key2714, 12)]

def rawRow15317 : Integer.Sparse Key := [(key2815, 4), (key2681, 4), (key2817, 4), (key2681, -4), (key2817, -4), (key2688, -4), (key2712, -4), (key2863, -4), (key2714, -4), (key2714, 12)]

def rawRow15318 : Integer.Sparse Key := [(key2815, 4), (key2817, 4), (key2681, 4), (key2817, -4), (key2681, -4), (key2688, -4), (key2863, -4), (key2712, -4), (key2714, -4), (key2714, 12)]

def rawRow15319 : Integer.Sparse Key := [(key2817, 4), (key2681, 4), (key2815, 4), (key2688, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2863, -4), (key2712, -4), (key2714, 12)]

def rawRow15320 : Integer.Sparse Key := [(key2817, 4), (key2815, 4), (key2681, 4), (key2817, -4), (key2688, -4), (key2681, -4), (key2863, -4), (key2714, -4), (key2712, -4), (key2714, 12)]

def rawRow15321 : Integer.Sparse Key := [(key2681, 4), (key2712, 4), (key2714, 4), (key2815, -4), (key2817, -4), (key2863, -4), (key2681, -4), (key2688, -4), (key2714, -4), (key2817, 12)]

def rawRow15322 : Integer.Sparse Key := [(key2681, 4), (key2714, 4), (key2712, 4), (key2817, -4), (key2815, -4), (key2863, -4), (key2688, -4), (key2681, -4), (key2714, -4), (key2817, 12)]

def rawRow15323 : Integer.Sparse Key := [(key2712, 4), (key2681, 4), (key2714, 4), (key2815, -4), (key2863, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2688, -4), (key2817, 12)]

def rawRow15324 : Integer.Sparse Key := [(key2712, 4), (key2714, 4), (key2681, 4), (key2863, -4), (key2815, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2688, -4), (key2817, 12)]

def rawRow15325 : Integer.Sparse Key := [(key2714, 4), (key2681, 4), (key2712, 4), (key2817, -4), (key2863, -4), (key2815, -4), (key2688, -4), (key2714, -4), (key2681, -4), (key2817, 12)]

def rawRow15326 : Integer.Sparse Key := [(key2714, 4), (key2712, 4), (key2681, 4), (key2863, -4), (key2817, -4), (key2815, -4), (key2714, -4), (key2688, -4), (key2681, -4), (key2817, 12)]

def rawRow15327 : Integer.Sparse Key := [(key2681, 4), (key2815, 4), (key2817, 4), (key2712, -4), (key2714, -4), (key2863, -4), (key2681, -4), (key2688, -4), (key2817, -4), (key2714, 12)]

def rawRow15328 : Integer.Sparse Key := [(key2681, 4), (key2817, 4), (key2815, 4), (key2714, -4), (key2712, -4), (key2863, -4), (key2688, -4), (key2681, -4), (key2817, -4), (key2714, 12)]

def rawRow15329 : Integer.Sparse Key := [(key2815, 4), (key2681, 4), (key2817, 4), (key2712, -4), (key2863, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2688, -4), (key2714, 12)]

def rawRow15330 : Integer.Sparse Key := [(key2815, 4), (key2817, 4), (key2681, 4), (key2863, -4), (key2712, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2688, -4), (key2714, 12)]

def rawRow15331 : Integer.Sparse Key := [(key2817, 4), (key2681, 4), (key2815, 4), (key2714, -4), (key2863, -4), (key2712, -4), (key2688, -4), (key2817, -4), (key2681, -4), (key2714, 12)]

def rawRow15332 : Integer.Sparse Key := [(key2817, 4), (key2815, 4), (key2681, 4), (key2863, -4), (key2714, -4), (key2712, -4), (key2817, -4), (key2688, -4), (key2681, -4), (key2714, 12)]

def rawRow15333 : Integer.Sparse Key := [(key2712, 4), (key2815, 4), (key2863, 4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2688, 12)]

def rawRow15334 : Integer.Sparse Key := [(key2712, 4), (key2863, 4), (key2815, 4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2688, 12)]

def rawRow15335 : Integer.Sparse Key := [(key2815, 4), (key2712, 4), (key2863, 4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2688, 12)]

def rawRow15336 : Integer.Sparse Key := [(key2815, 4), (key2863, 4), (key2712, 4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2688, 12)]

def rawRow15337 : Integer.Sparse Key := [(key2863, 4), (key2712, 4), (key2815, 4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2688, 12)]

def rawRow15338 : Integer.Sparse Key := [(key2863, 4), (key2815, 4), (key2712, 4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2688, 12)]

def rawRow15339 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2599, 6), (key2763, -2), (key2767, -2), (key2767, -2), (key2840, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2888, -2), (key2888, -2), (key2909, -2), (key2930, 6), (key2967, -2), (key2967, -2), (key2988, -2)]

def rawRow15340 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2599, 6), (key2767, -2), (key2763, -2), (key2767, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2888, -2), (key2909, -2), (key2888, -2), (key2930, 6), (key2967, -2), (key2988, -2), (key2967, -2)]

def rawRow15341 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, 6), (key2767, -2), (key2767, -2), (key2763, -2), (key2875, 2), (key2875, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2909, -2), (key2888, -2), (key2888, -2), (key2930, 6), (key2988, -2), (key2967, -2), (key2967, -2)]

def rawRow15342 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2599, -2), (key2588, 6), (key2840, -2), (key2844, -2), (key2888, -2), (key2763, 2), (key2767, 2), (key2840, 2), (key2875, 2), (key2888, 2), (key2909, 2), (key2767, -2), (key2844, -2), (key2875, -2), (key2967, 6), (key2930, -2), (key2967, -2), (key2988, -2)]

def rawRow15343 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2599, -2), (key2588, 6), (key2844, -2), (key2840, -2), (key2888, -2), (key2767, 2), (key2763, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2767, -2), (key2875, -2), (key2844, -2), (key2967, 6), (key2930, -2), (key2988, -2), (key2967, -2)]

def rawRow15344 : Integer.Sparse Key := [(key2584, -2), (key2599, -2), (key2588, -2), (key2588, 6), (key2840, -2), (key2888, -2), (key2844, -2), (key2840, 2), (key2888, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2844, -2), (key2767, -2), (key2875, -2), (key2967, 6), (key2967, -2), (key2930, -2), (key2988, -2)]

def rawRow15345 : Integer.Sparse Key := [(key2599, -2), (key2584, -2), (key2588, -2), (key2588, 6), (key2888, -2), (key2840, -2), (key2844, -2), (key2888, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2875, 2), (key2767, 2), (key2844, -2), (key2875, -2), (key2767, -2), (key2967, 6), (key2967, -2), (key2988, -2), (key2930, -2)]

def rawRow15346 : Integer.Sparse Key := [(key2588, -2), (key2599, -2), (key2584, -2), (key2588, 6), (key2844, -2), (key2888, -2), (key2840, -2), (key2875, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2763, 2), (key2840, 2), (key2875, -2), (key2767, -2), (key2844, -2), (key2967, 6), (key2988, -2), (key2930, -2), (key2967, -2)]

def rawRow15347 : Integer.Sparse Key := [(key2599, -2), (key2588, -2), (key2584, -2), (key2588, 6), (key2888, -2), (key2844, -2), (key2840, -2), (key2909, 2), (key2875, 2), (key2888, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2875, -2), (key2844, -2), (key2767, -2), (key2967, 6), (key2988, -2), (key2967, -2), (key2930, -2)]

def rawRow15348 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2930, 6), (key2584, -2), (key2588, -2), (key2588, -2), (key2840, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2967, -2), (key2967, -2), (key2988, -2), (key2599, 6), (key2888, -2), (key2888, -2), (key2909, -2)]

def rawRow15349 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2930, 6), (key2588, -2), (key2584, -2), (key2588, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2967, -2), (key2988, -2), (key2967, -2), (key2599, 6), (key2888, -2), (key2909, -2), (key2888, -2)]

def rawRow15350 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2930, 6), (key2588, -2), (key2588, -2), (key2584, -2), (key2875, 2), (key2875, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, -2), (key2967, -2), (key2967, -2), (key2599, 6), (key2909, -2), (key2888, -2), (key2888, -2)]

def rawRow15351 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2930, -2), (key2767, 6), (key2840, -2), (key2844, -2), (key2967, -2), (key2584, 2), (key2588, 2), (key2840, 2), (key2875, 2), (key2967, 2), (key2988, 2), (key2588, -2), (key2844, -2), (key2875, -2), (key2888, 6), (key2599, -2), (key2888, -2), (key2909, -2)]

def rawRow15352 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2930, -2), (key2767, 6), (key2844, -2), (key2840, -2), (key2967, -2), (key2588, 2), (key2584, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2588, -2), (key2875, -2), (key2844, -2), (key2888, 6), (key2599, -2), (key2909, -2), (key2888, -2)]

def rawRow15353 : Integer.Sparse Key := [(key2763, -2), (key2930, -2), (key2767, -2), (key2767, 6), (key2840, -2), (key2967, -2), (key2844, -2), (key2840, 2), (key2967, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2844, -2), (key2588, -2), (key2875, -2), (key2888, 6), (key2888, -2), (key2599, -2), (key2909, -2)]

def rawRow15354 : Integer.Sparse Key := [(key2930, -2), (key2763, -2), (key2767, -2), (key2767, 6), (key2967, -2), (key2840, -2), (key2844, -2), (key2967, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2875, 2), (key2588, 2), (key2844, -2), (key2875, -2), (key2588, -2), (key2888, 6), (key2888, -2), (key2909, -2), (key2599, -2)]

def rawRow15355 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2763, -2), (key2767, 6), (key2844, -2), (key2967, -2), (key2840, -2), (key2875, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2584, 2), (key2840, 2), (key2875, -2), (key2588, -2), (key2844, -2), (key2888, 6), (key2909, -2), (key2599, -2), (key2888, -2)]

def rawRow15356 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2763, -2), (key2767, 6), (key2967, -2), (key2844, -2), (key2840, -2), (key2988, 2), (key2875, 2), (key2967, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2875, -2), (key2844, -2), (key2588, -2), (key2888, 6), (key2909, -2), (key2888, -2), (key2599, -2)]

def rawRow15357 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2888, -2), (key2967, 6), (key2584, -2), (key2588, -2), (key2599, -2), (key2763, 2), (key2767, 2), (key2840, 2), (key2875, 2), (key2888, 2), (key2909, 2), (key2930, -2), (key2967, -2), (key2988, -2), (key2588, 6), (key2767, -2), (key2844, -2), (key2875, -2)]

def rawRow15358 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2888, -2), (key2967, 6), (key2588, -2), (key2584, -2), (key2599, -2), (key2767, 2), (key2763, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2930, -2), (key2988, -2), (key2967, -2), (key2588, 6), (key2767, -2), (key2875, -2), (key2844, -2)]

def rawRow15359 : Integer.Sparse Key := [(key2840, -2), (key2888, -2), (key2844, -2), (key2967, 6), (key2584, -2), (key2599, -2), (key2588, -2), (key2840, 2), (key2888, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2967, -2), (key2930, -2), (key2988, -2), (key2588, 6), (key2844, -2), (key2767, -2), (key2875, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15360 : Integer.Sparse Key := [(key2888, -2), (key2840, -2), (key2844, -2), (key2967, 6), (key2599, -2), (key2584, -2), (key2588, -2), (key2888, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2875, 2), (key2767, 2), (key2967, -2), (key2988, -2), (key2930, -2), (key2588, 6), (key2844, -2), (key2875, -2), (key2767, -2)]

def rawRow15361 : Integer.Sparse Key := [(key2844, -2), (key2888, -2), (key2840, -2), (key2967, 6), (key2588, -2), (key2599, -2), (key2584, -2), (key2875, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2763, 2), (key2840, 2), (key2988, -2), (key2930, -2), (key2967, -2), (key2588, 6), (key2875, -2), (key2767, -2), (key2844, -2)]

def rawRow15362 : Integer.Sparse Key := [(key2888, -2), (key2844, -2), (key2840, -2), (key2967, 6), (key2599, -2), (key2588, -2), (key2584, -2), (key2909, 2), (key2875, 2), (key2888, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2988, -2), (key2967, -2), (key2930, -2), (key2588, 6), (key2875, -2), (key2844, -2), (key2767, -2)]

def rawRow15363 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2967, -2), (key2888, 6), (key2763, -2), (key2767, -2), (key2930, -2), (key2584, 2), (key2588, 2), (key2840, 2), (key2875, 2), (key2967, 2), (key2988, 2), (key2599, -2), (key2888, -2), (key2909, -2), (key2767, 6), (key2588, -2), (key2844, -2), (key2875, -2)]

def rawRow15364 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2967, -2), (key2888, 6), (key2767, -2), (key2763, -2), (key2930, -2), (key2588, 2), (key2584, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2599, -2), (key2909, -2), (key2888, -2), (key2767, 6), (key2588, -2), (key2875, -2), (key2844, -2)]

def rawRow15365 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2844, -2), (key2888, 6), (key2763, -2), (key2930, -2), (key2767, -2), (key2840, 2), (key2967, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2888, -2), (key2599, -2), (key2909, -2), (key2767, 6), (key2844, -2), (key2588, -2), (key2875, -2)]

def rawRow15366 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2844, -2), (key2888, 6), (key2930, -2), (key2763, -2), (key2767, -2), (key2967, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2875, 2), (key2588, 2), (key2888, -2), (key2909, -2), (key2599, -2), (key2767, 6), (key2844, -2), (key2875, -2), (key2588, -2)]

def rawRow15367 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2840, -2), (key2888, 6), (key2767, -2), (key2930, -2), (key2763, -2), (key2875, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2584, 2), (key2840, 2), (key2909, -2), (key2599, -2), (key2888, -2), (key2767, 6), (key2875, -2), (key2588, -2), (key2844, -2)]

def rawRow15368 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2840, -2), (key2888, 6), (key2930, -2), (key2767, -2), (key2763, -2), (key2988, 2), (key2875, 2), (key2967, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2909, -2), (key2888, -2), (key2599, -2), (key2767, 6), (key2875, -2), (key2844, -2), (key2588, -2)]

def rawRow15369 : Integer.Sparse Key := [(key2840, -2), (key2888, -2), (key2967, -2), (key2844, 6), (key2840, -2), (key2888, -2), (key2967, -2), (key2584, 2), (key2599, 2), (key2763, 2), (key2909, 2), (key2930, 2), (key2988, 2), (key2588, -2), (key2767, -2), (key2875, -2), (key2844, 6), (key2588, -2), (key2767, -2), (key2875, -2)]

def rawRow15370 : Integer.Sparse Key := [(key2888, -2), (key2840, -2), (key2967, -2), (key2844, 6), (key2888, -2), (key2840, -2), (key2967, -2), (key2599, 2), (key2584, 2), (key2909, 2), (key2763, 2), (key2988, 2), (key2930, 2), (key2588, -2), (key2875, -2), (key2767, -2), (key2844, 6), (key2588, -2), (key2875, -2), (key2767, -2)]

def rawRow15371 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2888, -2), (key2844, 6), (key2840, -2), (key2967, -2), (key2888, -2), (key2763, 2), (key2930, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2767, -2), (key2588, -2), (key2875, -2), (key2844, 6), (key2767, -2), (key2588, -2), (key2875, -2)]

def rawRow15372 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2888, -2), (key2844, 6), (key2967, -2), (key2840, -2), (key2888, -2), (key2930, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2909, 2), (key2599, 2), (key2767, -2), (key2875, -2), (key2588, -2), (key2844, 6), (key2767, -2), (key2875, -2), (key2588, -2)]

def rawRow15373 : Integer.Sparse Key := [(key2888, -2), (key2967, -2), (key2840, -2), (key2844, 6), (key2888, -2), (key2967, -2), (key2840, -2), (key2909, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2584, 2), (key2763, 2), (key2875, -2), (key2588, -2), (key2767, -2), (key2844, 6), (key2875, -2), (key2588, -2), (key2767, -2)]

def rawRow15374 : Integer.Sparse Key := [(key2967, -2), (key2888, -2), (key2840, -2), (key2844, 6), (key2967, -2), (key2888, -2), (key2840, -2), (key2988, 2), (key2909, 2), (key2930, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2875, -2), (key2767, -2), (key2588, -2), (key2844, 6), (key2875, -2), (key2767, -2), (key2588, -2)]

def rawRow15375 : Integer.Sparse Key := [(key2012, 4), (key2012, 4), (key2025, 4), (key2041, -4), (key2054, -4), (key2054, -4), (key2126, -4), (key2143, -4), (key2143, -4), (key2227, 12)]

def rawRow15376 : Integer.Sparse Key := [(key2012, 4), (key2025, 4), (key2012, 4), (key2054, -4), (key2041, -4), (key2054, -4), (key2143, -4), (key2126, -4), (key2143, -4), (key2227, 12)]

def rawRow15377 : Integer.Sparse Key := [(key2025, 4), (key2012, 4), (key2012, 4), (key2054, -4), (key2054, -4), (key2041, -4), (key2143, -4), (key2143, -4), (key2126, -4), (key2227, 12)]

def rawRow15378 : Integer.Sparse Key := [(key2012, 4), (key2041, 4), (key2054, 4), (key2012, -4), (key2025, -4), (key2054, -4), (key2126, -4), (key2143, -4), (key2227, -4), (key2143, 12)]

def rawRow15379 : Integer.Sparse Key := [(key2012, 4), (key2054, 4), (key2041, 4), (key2025, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2126, -4), (key2227, -4), (key2143, 12)]

def rawRow15380 : Integer.Sparse Key := [(key2041, 4), (key2012, 4), (key2054, 4), (key2012, -4), (key2054, -4), (key2025, -4), (key2126, -4), (key2227, -4), (key2143, -4), (key2143, 12)]

def rawRow15381 : Integer.Sparse Key := [(key2041, 4), (key2054, 4), (key2012, 4), (key2054, -4), (key2012, -4), (key2025, -4), (key2227, -4), (key2126, -4), (key2143, -4), (key2143, 12)]

def rawRow15382 : Integer.Sparse Key := [(key2054, 4), (key2012, 4), (key2041, 4), (key2025, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2227, -4), (key2126, -4), (key2143, 12)]

def rawRow15383 : Integer.Sparse Key := [(key2054, 4), (key2041, 4), (key2012, 4), (key2054, -4), (key2025, -4), (key2012, -4), (key2227, -4), (key2143, -4), (key2126, -4), (key2143, 12)]

def rawRow15384 : Integer.Sparse Key := [(key2012, 4), (key2012, 4), (key2025, 4), (key2126, -4), (key2143, -4), (key2143, -4), (key2041, -4), (key2054, -4), (key2054, -4), (key2227, 12)]

def rawRow15385 : Integer.Sparse Key := [(key2012, 4), (key2025, 4), (key2012, 4), (key2143, -4), (key2126, -4), (key2143, -4), (key2054, -4), (key2041, -4), (key2054, -4), (key2227, 12)]

def rawRow15386 : Integer.Sparse Key := [(key2025, 4), (key2012, 4), (key2012, 4), (key2143, -4), (key2143, -4), (key2126, -4), (key2054, -4), (key2054, -4), (key2041, -4), (key2227, 12)]

def rawRow15387 : Integer.Sparse Key := [(key2012, 4), (key2126, 4), (key2143, 4), (key2012, -4), (key2025, -4), (key2143, -4), (key2041, -4), (key2054, -4), (key2227, -4), (key2054, 12)]

def rawRow15388 : Integer.Sparse Key := [(key2012, 4), (key2143, 4), (key2126, 4), (key2025, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2041, -4), (key2227, -4), (key2054, 12)]

def rawRow15389 : Integer.Sparse Key := [(key2126, 4), (key2012, 4), (key2143, 4), (key2012, -4), (key2143, -4), (key2025, -4), (key2041, -4), (key2227, -4), (key2054, -4), (key2054, 12)]

def rawRow15390 : Integer.Sparse Key := [(key2126, 4), (key2143, 4), (key2012, 4), (key2143, -4), (key2012, -4), (key2025, -4), (key2227, -4), (key2041, -4), (key2054, -4), (key2054, 12)]

def rawRow15391 : Integer.Sparse Key := [(key2143, 4), (key2012, 4), (key2126, 4), (key2025, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2227, -4), (key2041, -4), (key2054, 12)]

def rawRow15392 : Integer.Sparse Key := [(key2143, 4), (key2126, 4), (key2012, 4), (key2143, -4), (key2025, -4), (key2012, -4), (key2227, -4), (key2054, -4), (key2041, -4), (key2054, 12)]

def rawRow15393 : Integer.Sparse Key := [(key2012, 4), (key2041, 4), (key2054, 4), (key2126, -4), (key2143, -4), (key2227, -4), (key2012, -4), (key2025, -4), (key2054, -4), (key2143, 12)]

def rawRow15394 : Integer.Sparse Key := [(key2012, 4), (key2054, 4), (key2041, 4), (key2143, -4), (key2126, -4), (key2227, -4), (key2025, -4), (key2012, -4), (key2054, -4), (key2143, 12)]

def rawRow15395 : Integer.Sparse Key := [(key2041, 4), (key2012, 4), (key2054, 4), (key2126, -4), (key2227, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2025, -4), (key2143, 12)]

def rawRow15396 : Integer.Sparse Key := [(key2041, 4), (key2054, 4), (key2012, 4), (key2227, -4), (key2126, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2025, -4), (key2143, 12)]

def rawRow15397 : Integer.Sparse Key := [(key2054, 4), (key2012, 4), (key2041, 4), (key2143, -4), (key2227, -4), (key2126, -4), (key2025, -4), (key2054, -4), (key2012, -4), (key2143, 12)]

def rawRow15398 : Integer.Sparse Key := [(key2054, 4), (key2041, 4), (key2012, 4), (key2227, -4), (key2143, -4), (key2126, -4), (key2054, -4), (key2025, -4), (key2012, -4), (key2143, 12)]

def rawRow15399 : Integer.Sparse Key := [(key2012, 4), (key2126, 4), (key2143, 4), (key2041, -4), (key2054, -4), (key2227, -4), (key2012, -4), (key2025, -4), (key2143, -4), (key2054, 12)]

def rawRow15400 : Integer.Sparse Key := [(key2012, 4), (key2143, 4), (key2126, 4), (key2054, -4), (key2041, -4), (key2227, -4), (key2025, -4), (key2012, -4), (key2143, -4), (key2054, 12)]

def rawRow15401 : Integer.Sparse Key := [(key2126, 4), (key2012, 4), (key2143, 4), (key2041, -4), (key2227, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2025, -4), (key2054, 12)]

def rawRow15402 : Integer.Sparse Key := [(key2126, 4), (key2143, 4), (key2012, 4), (key2227, -4), (key2041, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2025, -4), (key2054, 12)]

def rawRow15403 : Integer.Sparse Key := [(key2143, 4), (key2012, 4), (key2126, 4), (key2054, -4), (key2227, -4), (key2041, -4), (key2025, -4), (key2143, -4), (key2012, -4), (key2054, 12)]

def rawRow15404 : Integer.Sparse Key := [(key2143, 4), (key2126, 4), (key2012, 4), (key2227, -4), (key2054, -4), (key2041, -4), (key2143, -4), (key2025, -4), (key2012, -4), (key2054, 12)]

def rawRow15405 : Integer.Sparse Key := [(key2041, 4), (key2126, 4), (key2227, 4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2025, 12)]

def rawRow15406 : Integer.Sparse Key := [(key2041, 4), (key2227, 4), (key2126, 4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2025, 12)]

def rawRow15407 : Integer.Sparse Key := [(key2126, 4), (key2041, 4), (key2227, 4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2025, 12)]

def rawRow15408 : Integer.Sparse Key := [(key2126, 4), (key2227, 4), (key2041, 4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2025, 12)]

def rawRow15409 : Integer.Sparse Key := [(key2227, 4), (key2041, 4), (key2126, 4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2025, 12)]

def rawRow15410 : Integer.Sparse Key := [(key2227, 4), (key2126, 4), (key2041, 4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2025, 12)]

def rawRow15411 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2802, -1), (key2806, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2852, 2), (key2857, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2867, 2), (key2894, -1), (key2896, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2903, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2973, -1), (key2975, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2982, -1)]

def rawRow15412 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2723, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2806, -1), (key2802, -1), (key2826, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2857, 2), (key2852, 2), (key2867, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2896, -1), (key2894, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2975, -1), (key2973, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2975, -1)]

def rawRow15413 : Integer.Sparse Key := [(key2723, -1), (key2723, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2826, -1), (key2826, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2867, 2), (key2867, 2), (key2857, 2), (key2857, 2), (key2852, 2), (key2852, 2), (key2903, -1), (key2903, -1), (key2896, -1), (key2896, -1), (key2894, -1), (key2894, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2982, -1), (key2982, -1), (key2975, -1), (key2975, -1), (key2973, -1), (key2973, -1)]

def rawRow15414 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2699, -1), (key2723, -1), (key2736, -1), (key2746, -1), (key2668, 2), (key2703, 2), (key2723, 2), (key2779, -1), (key2783, -1), (key2852, -1), (key2867, -1), (key2894, -1), (key2903, -1), (key2779, 2), (key2791, 2), (key2802, 2), (key2826, 2), (key2896, 2), (key2903, 2), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2857, -1), (key2867, -1), (key2937, 2), (key2973, 2), (key2982, 2), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2975, -1), (key2982, -1)]

def rawRow15415 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2736, -1), (key2668, 2), (key2723, 2), (key2703, 2), (key2783, -1), (key2779, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2894, -1), (key2791, 2), (key2779, 2), (key2826, 2), (key2802, 2), (key2903, 2), (key2896, 2), (key2791, -1), (key2783, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2857, -1), (key2937, 2), (key2982, 2), (key2973, 2), (key2942, -1), (key2937, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2975, -1)]

def rawRow15416 : Integer.Sparse Key := [(key2699, -1), (key2736, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2703, 2), (key2668, 2), (key2723, 2), (key2852, -1), (key2894, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2802, 2), (key2896, 2), (key2779, 2), (key2903, 2), (key2791, 2), (key2826, 2), (key2806, -1), (key2857, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2826, -1), (key2973, 2), (key2937, 2), (key2982, 2), (key2949, -1), (key2975, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2959, -1)]

def rawRow15417 : Integer.Sparse Key := [(key2736, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2723, -1), (key2668, -1), (key2703, 2), (key2723, 2), (key2668, 2), (key2894, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2867, -1), (key2783, -1), (key2896, 2), (key2802, 2), (key2903, 2), (key2779, 2), (key2826, 2), (key2791, 2), (key2857, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2826, -1), (key2791, -1), (key2973, 2), (key2982, 2), (key2937, 2), (key2975, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2959, -1), (key2942, -1)]

def rawRow15418 : Integer.Sparse Key := [(key2723, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2664, -1), (key2699, -1), (key2723, 2), (key2668, 2), (key2703, 2), (key2867, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2826, 2), (key2903, 2), (key2791, 2), (key2896, 2), (key2779, 2), (key2802, 2), (key2826, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2783, -1), (key2806, -1), (key2982, 2), (key2937, 2), (key2973, 2), (key2959, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2937, -1), (key2949, -1)]

def rawRow15419 : Integer.Sparse Key := [(key2746, -1), (key2723, -1), (key2736, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2723, 2), (key2703, 2), (key2668, 2), (key2903, -1), (key2867, -1), (key2894, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2903, 2), (key2826, 2), (key2896, 2), (key2791, 2), (key2802, 2), (key2779, 2), (key2867, -1), (key2826, -1), (key2857, -1), (key2791, -1), (key2806, -1), (key2783, -1), (key2982, 2), (key2973, 2), (key2937, 2), (key2982, -1), (key2959, -1), (key2975, -1), (key2942, -1), (key2949, -1), (key2937, -1)]

def rawRow15420 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2699, -1), (key2703, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2852, 2), (key2857, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2867, 2), (key2973, -1), (key2975, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2982, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2894, -1), (key2896, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2903, -1)]

def rawRow15421 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2826, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2703, -1), (key2699, -1), (key2723, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2857, 2), (key2852, 2), (key2867, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2975, -1), (key2973, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2896, -1), (key2894, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2896, -1)]

def rawRow15422 : Integer.Sparse Key := [(key2826, -1), (key2826, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2723, -1), (key2723, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2867, 2), (key2867, 2), (key2857, 2), (key2857, 2), (key2852, 2), (key2852, 2), (key2982, -1), (key2982, -1), (key2975, -1), (key2975, -1), (key2973, -1), (key2973, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2903, -1), (key2896, -1), (key2896, -1), (key2894, -1), (key2894, -1)]

def rawRow15423 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2826, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2625, 2), (key2637, 2), (key2699, 2), (key2723, 2), (key2975, 2), (key2982, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2723, -1), (key2857, -1), (key2867, -1), (key2647, 2), (key2894, 2), (key2903, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2746, -1), (key2896, -1), (key2903, -1)]

def rawRow15424 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2613, 2), (key2826, 2), (key2806, 2), (key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2637, 2), (key2625, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2975, 2), (key2637, -1), (key2629, -1), (key2723, -1), (key2703, -1), (key2867, -1), (key2857, -1), (key2647, 2), (key2903, 2), (key2894, 2), (key2652, -1), (key2647, -1), (key2746, -1), (key2736, -1), (key2903, -1), (key2896, -1)]

def rawRow15425 : Integer.Sparse Key := [(key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2806, 2), (key2613, 2), (key2826, 2), (key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2699, 2), (key2975, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2703, -1), (key2857, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2894, 2), (key2647, 2), (key2903, 2), (key2736, -1), (key2896, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2746, -1)]

def rawRow15426 : Integer.Sparse Key := [(key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2806, 2), (key2826, 2), (key2613, 2), (key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2975, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2723, 2), (key2637, 2), (key2857, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2723, -1), (key2637, -1), (key2894, 2), (key2903, 2), (key2647, 2), (key2896, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2746, -1), (key2652, -1)]

def rawRow15427 : Integer.Sparse Key := [(key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2826, 2), (key2613, 2), (key2806, 2), (key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2723, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2625, 2), (key2699, 2), (key2723, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2629, -1), (key2703, -1), (key2903, 2), (key2647, 2), (key2894, 2), (key2746, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2647, -1), (key2736, -1)]

def rawRow15428 : Integer.Sparse Key := [(key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2826, 2), (key2806, 2), (key2613, 2), (key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2723, 2), (key2975, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2867, -1), (key2723, -1), (key2857, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2903, 2), (key2894, 2), (key2647, 2), (key2903, -1), (key2746, -1), (key2896, -1), (key2652, -1), (key2736, -1), (key2647, -1)]

def rawRow15429 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2852, -1), (key2867, -1), (key2894, -1), (key2903, -1), (key2937, 2), (key2973, 2), (key2982, 2), (key2664, -1), (key2668, -1), (key2699, -1), (key2723, -1), (key2736, -1), (key2746, -1), (key2779, 2), (key2791, 2), (key2802, 2), (key2826, 2), (key2896, 2), (key2903, 2), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2975, -1), (key2982, -1), (key2668, 2), (key2703, 2), (key2723, 2), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2857, -1), (key2867, -1)]

def rawRow15430 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2894, -1), (key2937, 2), (key2982, 2), (key2973, 2), (key2668, -1), (key2664, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2736, -1), (key2791, 2), (key2779, 2), (key2826, 2), (key2802, 2), (key2903, 2), (key2896, 2), (key2942, -1), (key2937, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2975, -1), (key2668, 2), (key2723, 2), (key2703, 2), (key2791, -1), (key2783, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2857, -1)]

def rawRow15431 : Integer.Sparse Key := [(key2852, -1), (key2894, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2973, 2), (key2937, 2), (key2982, 2), (key2699, -1), (key2736, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2802, 2), (key2896, 2), (key2779, 2), (key2903, 2), (key2791, 2), (key2826, 2), (key2949, -1), (key2975, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2959, -1), (key2703, 2), (key2668, 2), (key2723, 2), (key2806, -1), (key2857, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2826, -1)]

def rawRow15432 : Integer.Sparse Key := [(key2894, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2867, -1), (key2783, -1), (key2973, 2), (key2982, 2), (key2937, 2), (key2736, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2723, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2903, 2), (key2779, 2), (key2826, 2), (key2791, 2), (key2975, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2959, -1), (key2942, -1), (key2703, 2), (key2723, 2), (key2668, 2), (key2857, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2826, -1), (key2791, -1)]

def rawRow15433 : Integer.Sparse Key := [(key2867, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2982, 2), (key2937, 2), (key2973, 2), (key2723, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2664, -1), (key2699, -1), (key2826, 2), (key2903, 2), (key2791, 2), (key2896, 2), (key2779, 2), (key2802, 2), (key2959, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2937, -1), (key2949, -1), (key2723, 2), (key2668, 2), (key2703, 2), (key2826, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2783, -1), (key2806, -1)]

def rawRow15434 : Integer.Sparse Key := [(key2903, -1), (key2867, -1), (key2894, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 2), (key2973, 2), (key2937, 2), (key2746, -1), (key2723, -1), (key2736, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2903, 2), (key2826, 2), (key2896, 2), (key2791, 2), (key2802, 2), (key2779, 2), (key2982, -1), (key2959, -1), (key2975, -1), (key2942, -1), (key2949, -1), (key2937, -1), (key2723, 2), (key2703, 2), (key2668, 2), (key2867, -1), (key2826, -1), (key2857, -1), (key2791, -1), (key2806, -1), (key2783, -1)]

def rawRow15435 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2647, 2), (key2894, 2), (key2903, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2625, 2), (key2637, 2), (key2699, 2), (key2723, 2), (key2975, 2), (key2982, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2746, -1), (key2896, -1), (key2903, -1), (key2613, 2), (key2806, 2), (key2826, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2723, -1), (key2857, -1), (key2867, -1)]

def rawRow15436 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2647, 2), (key2903, 2), (key2894, 2), (key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2637, 2), (key2625, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2975, 2), (key2652, -1), (key2647, -1), (key2746, -1), (key2736, -1), (key2903, -1), (key2896, -1), (key2613, 2), (key2826, 2), (key2806, 2), (key2637, -1), (key2629, -1), (key2723, -1), (key2703, -1), (key2867, -1), (key2857, -1)]

def rawRow15437 : Integer.Sparse Key := [(key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2894, 2), (key2647, 2), (key2903, 2), (key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2699, 2), (key2975, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2736, -1), (key2896, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2806, 2), (key2613, 2), (key2826, 2), (key2703, -1), (key2857, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2723, -1)]

def rawRow15438 : Integer.Sparse Key := [(key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2894, 2), (key2903, 2), (key2647, 2), (key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2975, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2723, 2), (key2637, 2), (key2896, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2746, -1), (key2652, -1), (key2806, 2), (key2826, 2), (key2613, 2), (key2857, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2723, -1), (key2637, -1)]

def rawRow15439 : Integer.Sparse Key := [(key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2903, 2), (key2647, 2), (key2894, 2), (key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2723, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2625, 2), (key2699, 2), (key2746, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2647, -1), (key2736, -1), (key2826, 2), (key2613, 2), (key2806, 2), (key2723, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2629, -1), (key2703, -1)]

def rawRow15440 : Integer.Sparse Key := [(key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2903, 2), (key2894, 2), (key2647, 2), (key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2723, 2), (key2975, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2903, -1), (key2746, -1), (key2896, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2826, 2), (key2806, 2), (key2613, 2), (key2867, -1), (key2723, -1), (key2857, -1), (key2637, -1), (key2703, -1), (key2629, -1)]

def rawRow15441 : Integer.Sparse Key := [(key2625, -1), (key2647, -1), (key2779, -1), (key2903, -1), (key2937, -1), (key2982, -1), (key2629, 2), (key2783, 2), (key2867, 2), (key2625, -1), (key2647, -1), (key2779, -1), (key2903, -1), (key2937, -1), (key2982, -1), (key2609, 2), (key2652, 2), (key2664, 2), (key2746, 2), (key2942, 2), (key2959, 2), (key2613, -1), (key2637, -1), (key2668, -1), (key2723, -1), (key2791, -1), (key2826, -1), (key2629, 2), (key2783, 2), (key2867, 2), (key2613, -1), (key2637, -1), (key2668, -1), (key2723, -1), (key2791, -1), (key2826, -1)]

def rawRow15442 : Integer.Sparse Key := [(key2647, -1), (key2625, -1), (key2903, -1), (key2779, -1), (key2982, -1), (key2937, -1), (key2629, 2), (key2867, 2), (key2783, 2), (key2647, -1), (key2625, -1), (key2903, -1), (key2779, -1), (key2982, -1), (key2937, -1), (key2652, 2), (key2609, 2), (key2746, 2), (key2664, 2), (key2959, 2), (key2942, 2), (key2637, -1), (key2613, -1), (key2723, -1), (key2668, -1), (key2826, -1), (key2791, -1), (key2629, 2), (key2867, 2), (key2783, 2), (key2637, -1), (key2613, -1), (key2723, -1), (key2668, -1), (key2826, -1), (key2791, -1)]

def rawRow15443 : Integer.Sparse Key := [(key2779, -1), (key2937, -1), (key2625, -1), (key2982, -1), (key2647, -1), (key2903, -1), (key2783, 2), (key2629, 2), (key2867, 2), (key2779, -1), (key2937, -1), (key2625, -1), (key2982, -1), (key2647, -1), (key2903, -1), (key2664, 2), (key2942, 2), (key2609, 2), (key2959, 2), (key2652, 2), (key2746, 2), (key2668, -1), (key2791, -1), (key2613, -1), (key2826, -1), (key2637, -1), (key2723, -1), (key2783, 2), (key2629, 2), (key2867, 2), (key2668, -1), (key2791, -1), (key2613, -1), (key2826, -1), (key2637, -1), (key2723, -1)]

def rawRow15444 : Integer.Sparse Key := [(key2937, -1), (key2779, -1), (key2982, -1), (key2625, -1), (key2903, -1), (key2647, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2937, -1), (key2779, -1), (key2982, -1), (key2625, -1), (key2903, -1), (key2647, -1), (key2942, 2), (key2664, 2), (key2959, 2), (key2609, 2), (key2746, 2), (key2652, 2), (key2791, -1), (key2668, -1), (key2826, -1), (key2613, -1), (key2723, -1), (key2637, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2791, -1), (key2668, -1), (key2826, -1), (key2613, -1), (key2723, -1), (key2637, -1)]

def rawRow15445 : Integer.Sparse Key := [(key2903, -1), (key2982, -1), (key2647, -1), (key2937, -1), (key2625, -1), (key2779, -1), (key2867, 2), (key2629, 2), (key2783, 2), (key2903, -1), (key2982, -1), (key2647, -1), (key2937, -1), (key2625, -1), (key2779, -1), (key2746, 2), (key2959, 2), (key2652, 2), (key2942, 2), (key2609, 2), (key2664, 2), (key2723, -1), (key2826, -1), (key2637, -1), (key2791, -1), (key2613, -1), (key2668, -1), (key2867, 2), (key2629, 2), (key2783, 2), (key2723, -1), (key2826, -1), (key2637, -1), (key2791, -1), (key2613, -1), (key2668, -1)]

def rawRow15446 : Integer.Sparse Key := [(key2982, -1), (key2903, -1), (key2937, -1), (key2647, -1), (key2779, -1), (key2625, -1), (key2867, 2), (key2783, 2), (key2629, 2), (key2982, -1), (key2903, -1), (key2937, -1), (key2647, -1), (key2779, -1), (key2625, -1), (key2959, 2), (key2746, 2), (key2942, 2), (key2652, 2), (key2664, 2), (key2609, 2), (key2826, -1), (key2723, -1), (key2791, -1), (key2637, -1), (key2668, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2629, 2), (key2826, -1), (key2723, -1), (key2791, -1), (key2637, -1), (key2668, -1), (key2613, -1)]

def rawRow15447 : Integer.Sparse Key := [(key1358, -2), (key1364, -2), (key1364, -2), (key1374, 6), (key1484, -2), (key1490, -2), (key1490, -2), (key1710, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1723, -2), (key1723, -2), (key1940, -2), (key1513, 6), (key1741, -2), (key1741, -2), (key1949, -2)]

def rawRow15448 : Integer.Sparse Key := [(key1364, -2), (key1358, -2), (key1364, -2), (key1374, 6), (key1490, -2), (key1484, -2), (key1490, -2), (key1716, 2), (key1710, 2), (key1937, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1723, -2), (key1940, -2), (key1723, -2), (key1513, 6), (key1741, -2), (key1949, -2), (key1741, -2)]

def rawRow15449 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1358, -2), (key1374, 6), (key1490, -2), (key1490, -2), (key1484, -2), (key1937, 2), (key1937, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1940, -2), (key1723, -2), (key1723, -2), (key1513, 6), (key1949, -2), (key1741, -2), (key1741, -2)]

def rawRow15450 : Integer.Sparse Key := [(key1358, -2), (key1364, -2), (key1374, -2), (key1364, 6), (key1710, -2), (key1716, -2), (key1723, -2), (key1484, 2), (key1490, 2), (key1710, 2), (key1937, 2), (key1723, 2), (key1940, 2), (key1490, -2), (key1716, -2), (key1937, -2), (key1741, 6), (key1513, -2), (key1741, -2), (key1949, -2)]

def rawRow15451 : Integer.Sparse Key := [(key1364, -2), (key1358, -2), (key1374, -2), (key1364, 6), (key1716, -2), (key1710, -2), (key1723, -2), (key1490, 2), (key1484, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1490, -2), (key1937, -2), (key1716, -2), (key1741, 6), (key1513, -2), (key1949, -2), (key1741, -2)]

def rawRow15452 : Integer.Sparse Key := [(key1358, -2), (key1374, -2), (key1364, -2), (key1364, 6), (key1710, -2), (key1723, -2), (key1716, -2), (key1710, 2), (key1723, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1716, -2), (key1490, -2), (key1937, -2), (key1741, 6), (key1741, -2), (key1513, -2), (key1949, -2)]

def rawRow15453 : Integer.Sparse Key := [(key1374, -2), (key1358, -2), (key1364, -2), (key1364, 6), (key1723, -2), (key1710, -2), (key1716, -2), (key1723, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1937, 2), (key1490, 2), (key1716, -2), (key1937, -2), (key1490, -2), (key1741, 6), (key1741, -2), (key1949, -2), (key1513, -2)]

def rawRow15454 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1358, -2), (key1364, 6), (key1716, -2), (key1723, -2), (key1710, -2), (key1937, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1484, 2), (key1710, 2), (key1937, -2), (key1490, -2), (key1716, -2), (key1741, 6), (key1949, -2), (key1513, -2), (key1741, -2)]

def rawRow15455 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1358, -2), (key1364, 6), (key1723, -2), (key1716, -2), (key1710, -2), (key1940, 2), (key1937, 2), (key1723, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1937, -2), (key1716, -2), (key1490, -2), (key1741, 6), (key1949, -2), (key1741, -2), (key1513, -2)]

def rawRow15456 : Integer.Sparse Key := [(key1484, -2), (key1490, -2), (key1490, -2), (key1513, 6), (key1358, -2), (key1364, -2), (key1364, -2), (key1710, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1741, -2), (key1741, -2), (key1949, -2), (key1374, 6), (key1723, -2), (key1723, -2), (key1940, -2)]

def rawRow15457 : Integer.Sparse Key := [(key1490, -2), (key1484, -2), (key1490, -2), (key1513, 6), (key1364, -2), (key1358, -2), (key1364, -2), (key1716, 2), (key1710, 2), (key1937, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1741, -2), (key1949, -2), (key1741, -2), (key1374, 6), (key1723, -2), (key1940, -2), (key1723, -2)]

def rawRow15458 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1484, -2), (key1513, 6), (key1364, -2), (key1364, -2), (key1358, -2), (key1937, 2), (key1937, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1949, -2), (key1741, -2), (key1741, -2), (key1374, 6), (key1940, -2), (key1723, -2), (key1723, -2)]

def rawRow15459 : Integer.Sparse Key := [(key1484, -2), (key1490, -2), (key1513, -2), (key1490, 6), (key1710, -2), (key1716, -2), (key1741, -2), (key1358, 2), (key1364, 2), (key1710, 2), (key1937, 2), (key1741, 2), (key1949, 2), (key1364, -2), (key1716, -2), (key1937, -2), (key1723, 6), (key1374, -2), (key1723, -2), (key1940, -2)]

def rawRow15460 : Integer.Sparse Key := [(key1490, -2), (key1484, -2), (key1513, -2), (key1490, 6), (key1716, -2), (key1710, -2), (key1741, -2), (key1364, 2), (key1358, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1364, -2), (key1937, -2), (key1716, -2), (key1723, 6), (key1374, -2), (key1940, -2), (key1723, -2)]

def rawRow15461 : Integer.Sparse Key := [(key1484, -2), (key1513, -2), (key1490, -2), (key1490, 6), (key1710, -2), (key1741, -2), (key1716, -2), (key1710, 2), (key1741, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1716, -2), (key1364, -2), (key1937, -2), (key1723, 6), (key1723, -2), (key1374, -2), (key1940, -2)]

def rawRow15462 : Integer.Sparse Key := [(key1513, -2), (key1484, -2), (key1490, -2), (key1490, 6), (key1741, -2), (key1710, -2), (key1716, -2), (key1741, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1937, 2), (key1364, 2), (key1716, -2), (key1937, -2), (key1364, -2), (key1723, 6), (key1723, -2), (key1940, -2), (key1374, -2)]

def rawRow15463 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1484, -2), (key1490, 6), (key1716, -2), (key1741, -2), (key1710, -2), (key1937, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1358, 2), (key1710, 2), (key1937, -2), (key1364, -2), (key1716, -2), (key1723, 6), (key1940, -2), (key1374, -2), (key1723, -2)]

def rawRow15464 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1484, -2), (key1490, 6), (key1741, -2), (key1716, -2), (key1710, -2), (key1949, 2), (key1937, 2), (key1741, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1937, -2), (key1716, -2), (key1364, -2), (key1723, 6), (key1940, -2), (key1723, -2), (key1374, -2)]

def rawRow15465 : Integer.Sparse Key := [(key1710, -2), (key1716, -2), (key1723, -2), (key1741, 6), (key1358, -2), (key1364, -2), (key1374, -2), (key1484, 2), (key1490, 2), (key1710, 2), (key1937, 2), (key1723, 2), (key1940, 2), (key1513, -2), (key1741, -2), (key1949, -2), (key1364, 6), (key1490, -2), (key1716, -2), (key1937, -2)]

def rawRow15466 : Integer.Sparse Key := [(key1716, -2), (key1710, -2), (key1723, -2), (key1741, 6), (key1364, -2), (key1358, -2), (key1374, -2), (key1490, 2), (key1484, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1513, -2), (key1949, -2), (key1741, -2), (key1364, 6), (key1490, -2), (key1937, -2), (key1716, -2)]

def rawRow15467 : Integer.Sparse Key := [(key1710, -2), (key1723, -2), (key1716, -2), (key1741, 6), (key1358, -2), (key1374, -2), (key1364, -2), (key1710, 2), (key1723, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1741, -2), (key1513, -2), (key1949, -2), (key1364, 6), (key1716, -2), (key1490, -2), (key1937, -2)]

def rawRow15468 : Integer.Sparse Key := [(key1723, -2), (key1710, -2), (key1716, -2), (key1741, 6), (key1374, -2), (key1358, -2), (key1364, -2), (key1723, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1937, 2), (key1490, 2), (key1741, -2), (key1949, -2), (key1513, -2), (key1364, 6), (key1716, -2), (key1937, -2), (key1490, -2)]

def rawRow15469 : Integer.Sparse Key := [(key1716, -2), (key1723, -2), (key1710, -2), (key1741, 6), (key1364, -2), (key1374, -2), (key1358, -2), (key1937, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1484, 2), (key1710, 2), (key1949, -2), (key1513, -2), (key1741, -2), (key1364, 6), (key1937, -2), (key1490, -2), (key1716, -2)]

def rawRow15470 : Integer.Sparse Key := [(key1723, -2), (key1716, -2), (key1710, -2), (key1741, 6), (key1374, -2), (key1364, -2), (key1358, -2), (key1940, 2), (key1937, 2), (key1723, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1949, -2), (key1741, -2), (key1513, -2), (key1364, 6), (key1937, -2), (key1716, -2), (key1490, -2)]

def rawRow15471 : Integer.Sparse Key := [(key1710, -2), (key1716, -2), (key1741, -2), (key1723, 6), (key1484, -2), (key1490, -2), (key1513, -2), (key1358, 2), (key1364, 2), (key1710, 2), (key1937, 2), (key1741, 2), (key1949, 2), (key1374, -2), (key1723, -2), (key1940, -2), (key1490, 6), (key1364, -2), (key1716, -2), (key1937, -2)]

def rawRow15472 : Integer.Sparse Key := [(key1716, -2), (key1710, -2), (key1741, -2), (key1723, 6), (key1490, -2), (key1484, -2), (key1513, -2), (key1364, 2), (key1358, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1374, -2), (key1940, -2), (key1723, -2), (key1490, 6), (key1364, -2), (key1937, -2), (key1716, -2)]

def rawRow15473 : Integer.Sparse Key := [(key1710, -2), (key1741, -2), (key1716, -2), (key1723, 6), (key1484, -2), (key1513, -2), (key1490, -2), (key1710, 2), (key1741, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1723, -2), (key1374, -2), (key1940, -2), (key1490, 6), (key1716, -2), (key1364, -2), (key1937, -2)]

def rawRow15474 : Integer.Sparse Key := [(key1741, -2), (key1710, -2), (key1716, -2), (key1723, 6), (key1513, -2), (key1484, -2), (key1490, -2), (key1741, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1937, 2), (key1364, 2), (key1723, -2), (key1940, -2), (key1374, -2), (key1490, 6), (key1716, -2), (key1937, -2), (key1364, -2)]

def rawRow15475 : Integer.Sparse Key := [(key1716, -2), (key1741, -2), (key1710, -2), (key1723, 6), (key1490, -2), (key1513, -2), (key1484, -2), (key1937, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1358, 2), (key1710, 2), (key1940, -2), (key1374, -2), (key1723, -2), (key1490, 6), (key1937, -2), (key1364, -2), (key1716, -2)]

def rawRow15476 : Integer.Sparse Key := [(key1741, -2), (key1716, -2), (key1710, -2), (key1723, 6), (key1513, -2), (key1490, -2), (key1484, -2), (key1949, 2), (key1937, 2), (key1741, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1940, -2), (key1723, -2), (key1374, -2), (key1490, 6), (key1937, -2), (key1716, -2), (key1364, -2)]

def rawRow15477 : Integer.Sparse Key := [(key1710, -2), (key1723, -2), (key1741, -2), (key1716, 6), (key1710, -2), (key1723, -2), (key1741, -2), (key1358, 2), (key1374, 2), (key1484, 2), (key1940, 2), (key1513, 2), (key1949, 2), (key1364, -2), (key1490, -2), (key1937, -2), (key1716, 6), (key1364, -2), (key1490, -2), (key1937, -2)]

def rawRow15478 : Integer.Sparse Key := [(key1723, -2), (key1710, -2), (key1741, -2), (key1716, 6), (key1723, -2), (key1710, -2), (key1741, -2), (key1374, 2), (key1358, 2), (key1940, 2), (key1484, 2), (key1949, 2), (key1513, 2), (key1364, -2), (key1937, -2), (key1490, -2), (key1716, 6), (key1364, -2), (key1937, -2), (key1490, -2)]

def rawRow15479 : Integer.Sparse Key := [(key1710, -2), (key1741, -2), (key1723, -2), (key1716, 6), (key1710, -2), (key1741, -2), (key1723, -2), (key1484, 2), (key1513, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1490, -2), (key1364, -2), (key1937, -2), (key1716, 6), (key1490, -2), (key1364, -2), (key1937, -2)]

def rawRow15480 : Integer.Sparse Key := [(key1741, -2), (key1710, -2), (key1723, -2), (key1716, 6), (key1741, -2), (key1710, -2), (key1723, -2), (key1513, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1940, 2), (key1374, 2), (key1490, -2), (key1937, -2), (key1364, -2), (key1716, 6), (key1490, -2), (key1937, -2), (key1364, -2)]

def rawRow15481 : Integer.Sparse Key := [(key1723, -2), (key1741, -2), (key1710, -2), (key1716, 6), (key1723, -2), (key1741, -2), (key1710, -2), (key1940, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1358, 2), (key1484, 2), (key1937, -2), (key1364, -2), (key1490, -2), (key1716, 6), (key1937, -2), (key1364, -2), (key1490, -2)]

def rawRow15482 : Integer.Sparse Key := [(key1741, -2), (key1723, -2), (key1710, -2), (key1716, 6), (key1741, -2), (key1723, -2), (key1710, -2), (key1949, 2), (key1940, 2), (key1513, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1937, -2), (key1490, -2), (key1364, -2), (key1716, 6), (key1937, -2), (key1490, -2), (key1364, -2)]

def rawRow15483 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2394, -2), (key2766, 2), (key2766, 2), (key2772, 2), (key2887, -1), (key2889, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2910, -1), (key2929, -2), (key2931, -2), (key2931, -2), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2989, -1), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15484 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2378, 2), (key2394, -2), (key2390, -2), (key2394, -2), (key2766, 2), (key2772, 2), (key2766, 2), (key2889, -1), (key2887, -1), (key2910, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2931, -2), (key2929, -2), (key2931, -2), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15485 : Integer.Sparse Key := [(key2383, 2), (key2378, 2), (key2378, 2), (key2394, -2), (key2394, -2), (key2390, -2), (key2772, 2), (key2766, 2), (key2766, 2), (key2910, -1), (key2910, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key2931, -2), (key2931, -2), (key2929, -2), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, -1), (key2966, -1), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15486 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2378, -2), (key2383, -2), (key2394, -2), (key2843, 2), (key2887, 2), (key2889, 2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2966, -2), (key2968, -2), (key2995, -2), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, -1), (key3002, -1), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15487 : Integer.Sparse Key := [(key2378, 2), (key2394, 2), (key2390, 2), (key2383, -2), (key2378, -2), (key2394, -2), (key2843, 2), (key2889, 2), (key2887, 2), (key2772, -1), (key2766, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2889, -1), (key2968, -2), (key2966, -2), (key2995, -2), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2995, -1), (key2931, 4), (key2989, 4), (key2968, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15488 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2394, 2), (key2378, -2), (key2394, -2), (key2383, -2), (key2887, 2), (key2843, 2), (key2889, 2), (key2843, -1), (key2889, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2966, -2), (key2995, -2), (key2968, -2), (key2966, -1), (key2995, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15489 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2378, 2), (key2394, -2), (key2378, -2), (key2383, -2), (key2887, 2), (key2889, 2), (key2843, 2), (key2889, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2880, -1), (key2772, -1), (key2995, -2), (key2966, -2), (key2968, -2), (key2995, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2989, -1), (key2931, -1), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15490 : Integer.Sparse Key := [(key2394, 2), (key2378, 2), (key2390, 2), (key2383, -2), (key2394, -2), (key2378, -2), (key2889, 2), (key2843, 2), (key2887, 2), (key2880, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2766, -1), (key2843, -1), (key2968, -2), (key2995, -2), (key2966, -2), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, -1), (key2966, -1), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15491 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2378, 2), (key2394, -2), (key2383, -2), (key2378, -2), (key2889, 2), (key2887, 2), (key2843, 2), (key2910, -1), (key2880, -1), (key2889, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2995, -2), (key2968, -2), (key2966, -2), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15492 : Integer.Sparse Key := [(key2406, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2443, -2), (key2587, 2), (key2587, 2), (key2593, 2), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2989, -1), (key2598, -2), (key2600, -2), (key2600, -2), (key2887, -1), (key2889, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2910, -1), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15493 : Integer.Sparse Key := [(key2406, 2), (key2411, 2), (key2406, 2), (key2443, -2), (key2437, -2), (key2443, -2), (key2587, 2), (key2593, 2), (key2587, 2), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2600, -2), (key2598, -2), (key2600, -2), (key2889, -1), (key2887, -1), (key2910, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15494 : Integer.Sparse Key := [(key2411, 2), (key2406, 2), (key2406, 2), (key2443, -2), (key2443, -2), (key2437, -2), (key2593, 2), (key2587, 2), (key2587, 2), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, -1), (key2966, -1), (key2600, -2), (key2600, -2), (key2598, -2), (key2910, -1), (key2910, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15495 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2406, -2), (key2411, -2), (key2443, -2), (key2843, 2), (key2966, 2), (key2968, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow15496 : Integer.Sparse Key := [(key2406, 2), (key2443, 2), (key2437, 2), (key2411, -2), (key2406, -2), (key2443, -2), (key2843, 2), (key2968, 2), (key2966, 2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow15497 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2443, 2), (key2406, -2), (key2443, -2), (key2411, -2), (key2966, 2), (key2843, 2), (key2968, 2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow15498 : Integer.Sparse Key := [(key2437, 2), (key2443, 2), (key2406, 2), (key2443, -2), (key2406, -2), (key2411, -2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow15499 : Integer.Sparse Key := [(key2443, 2), (key2406, 2), (key2437, 2), (key2411, -2), (key2443, -2), (key2406, -2), (key2968, 2), (key2843, 2), (key2966, 2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow15500 : Integer.Sparse Key := [(key2443, 2), (key2437, 2), (key2406, 2), (key2443, -2), (key2411, -2), (key2406, -2), (key2968, 2), (key2966, 2), (key2843, 2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow15501 : Integer.Sparse Key := [(key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2378, 2), (key2390, 2), (key2394, 2), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, -1), (key3002, -1), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15502 : Integer.Sparse Key := [(key2472, 2), (key2484, 2), (key2480, 2), (key2509, -2), (key2503, -2), (key2524, -2), (key2378, 2), (key2394, 2), (key2390, 2), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2995, -1), (key2593, -2), (key2587, -2), (key2600, -2), (key2772, -1), (key2766, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2889, -1), (key2931, 4), (key2989, 4), (key2968, 4)]

def rawRow15503 : Integer.Sparse Key := [(key2480, 2), (key2472, 2), (key2484, 2), (key2503, -2), (key2524, -2), (key2509, -2), (key2390, 2), (key2378, 2), (key2394, 2), (key2966, -1), (key2995, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2587, -2), (key2600, -2), (key2593, -2), (key2843, -1), (key2889, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15504 : Integer.Sparse Key := [(key2480, 2), (key2484, 2), (key2472, 2), (key2524, -2), (key2503, -2), (key2509, -2), (key2390, 2), (key2394, 2), (key2378, 2), (key2995, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2989, -1), (key2931, -1), (key2600, -2), (key2587, -2), (key2593, -2), (key2889, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2880, -1), (key2772, -1), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15505 : Integer.Sparse Key := [(key2484, 2), (key2472, 2), (key2480, 2), (key2509, -2), (key2524, -2), (key2503, -2), (key2394, 2), (key2378, 2), (key2390, 2), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, -1), (key2966, -1), (key2593, -2), (key2600, -2), (key2587, -2), (key2880, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2766, -1), (key2843, -1), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15506 : Integer.Sparse Key := [(key2484, 2), (key2480, 2), (key2472, 2), (key2524, -2), (key2509, -2), (key2503, -2), (key2394, 2), (key2390, 2), (key2378, 2), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key2600, -2), (key2593, -2), (key2587, -2), (key2910, -1), (key2880, -1), (key2889, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15507 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2509, 2), (key2480, -2), (key2484, -2), (key2524, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow15508 : Integer.Sparse Key := [(key2472, 2), (key2509, 2), (key2503, 2), (key2484, -2), (key2480, -2), (key2524, -2), (key2406, 2), (key2443, 2), (key2437, 2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow15509 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2509, 2), (key2480, -2), (key2524, -2), (key2484, -2), (key2437, 2), (key2406, 2), (key2443, 2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow15510 : Integer.Sparse Key := [(key2503, 2), (key2509, 2), (key2472, 2), (key2524, -2), (key2480, -2), (key2484, -2), (key2437, 2), (key2443, 2), (key2406, 2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow15511 : Integer.Sparse Key := [(key2509, 2), (key2472, 2), (key2503, 2), (key2484, -2), (key2524, -2), (key2480, -2), (key2443, 2), (key2406, 2), (key2437, 2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow15512 : Integer.Sparse Key := [(key2509, 2), (key2503, 2), (key2472, 2), (key2524, -2), (key2484, -2), (key2480, -2), (key2443, 2), (key2437, 2), (key2406, 2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow15513 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2524, 2), (key2472, -2), (key2484, -2), (key2509, -2), (key2480, 2), (key2503, 2), (key2524, 2), (key2587, -1), (key2600, -1), (key2766, -1), (key2910, -1), (key2931, -1), (key2989, -1), (key2843, -2), (key2889, -2), (key2968, -2), (key2587, -1), (key2600, -1), (key2766, -1), (key2910, -1), (key2931, -1), (key2989, -1), (key2593, 4), (key2772, 4), (key2880, 4)]

def rawRow15514 : Integer.Sparse Key := [(key2480, 2), (key2524, 2), (key2503, 2), (key2484, -2), (key2472, -2), (key2509, -2), (key2480, 2), (key2524, 2), (key2503, 2), (key2600, -1), (key2587, -1), (key2910, -1), (key2766, -1), (key2989, -1), (key2931, -1), (key2889, -2), (key2843, -2), (key2968, -2), (key2600, -1), (key2587, -1), (key2910, -1), (key2766, -1), (key2989, -1), (key2931, -1), (key2593, 4), (key2880, 4), (key2772, 4)]

def rawRow15515 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2524, 2), (key2472, -2), (key2509, -2), (key2484, -2), (key2503, 2), (key2480, 2), (key2524, 2), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, -1), (key2910, -1), (key2843, -2), (key2968, -2), (key2889, -2), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, -1), (key2910, -1), (key2772, 4), (key2593, 4), (key2880, 4)]

def rawRow15516 : Integer.Sparse Key := [(key2503, 2), (key2524, 2), (key2480, 2), (key2509, -2), (key2472, -2), (key2484, -2), (key2503, 2), (key2524, 2), (key2480, 2), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, -1), (key2600, -1), (key2968, -2), (key2843, -2), (key2889, -2), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, -1), (key2600, -1), (key2772, 4), (key2880, 4), (key2593, 4)]

def rawRow15517 : Integer.Sparse Key := [(key2524, 2), (key2480, 2), (key2503, 2), (key2484, -2), (key2509, -2), (key2472, -2), (key2524, 2), (key2480, 2), (key2503, 2), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, -1), (key2766, -1), (key2889, -2), (key2968, -2), (key2843, -2), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, -1), (key2766, -1), (key2880, 4), (key2593, 4), (key2772, 4)]

def rawRow15518 : Integer.Sparse Key := [(key2524, 2), (key2503, 2), (key2480, 2), (key2509, -2), (key2484, -2), (key2472, -2), (key2524, 2), (key2503, 2), (key2480, 2), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, -1), (key2587, -1), (key2968, -2), (key2889, -2), (key2843, -2), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, -1), (key2587, -1), (key2880, 4), (key2772, 4), (key2593, 4)]

def rawRow15519 : Integer.Sparse Key := [(key2608, 2), (key2614, 2), (key2614, 2), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2778, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2)]

def rawRow15520 : Integer.Sparse Key := [(key2614, 2), (key2608, 2), (key2614, 2), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2)]

def rawRow15521 : Integer.Sparse Key := [(key2614, 2), (key2614, 2), (key2608, 2), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2792, -1), (key2792, -1), (key2784, -1), (key2784, -1), (key2778, -1), (key2778, -1), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2)]

def rawRow15522 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, -1), (key2784, -1), (key2851, -1), (key2868, -1), (key2918, -1), (key2922, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2)]

def rawRow15523 : Integer.Sparse Key := [(key2630, 2), (key2624, 2), (key2638, 2), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, -1), (key2778, -1), (key2868, -1), (key2851, -1), (key2922, -1), (key2918, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2)]

def rawRow15524 : Integer.Sparse Key := [(key2624, 2), (key2638, 2), (key2630, 2), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, -1), (key2918, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2)]

def rawRow15525 : Integer.Sparse Key := [(key2638, 2), (key2624, 2), (key2630, 2), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2868, -1), (key2784, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2)]

def rawRow15526 : Integer.Sparse Key := [(key2630, 2), (key2638, 2), (key2624, 2), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2778, -1), (key2851, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2)]

def rawRow15527 : Integer.Sparse Key := [(key2638, 2), (key2630, 2), (key2624, 2), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, -1), (key2868, -1), (key2918, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2)]

def rawRow15528 : Integer.Sparse Key := [(key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2752, -1), (key2704, -1), (key2752, -1), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2)]

def rawRow15529 : Integer.Sparse Key := [(key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2752, -1), (key2698, -1), (key2752, -1), (key2704, -1), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2)]

def rawRow15530 : Integer.Sparse Key := [(key2669, 2), (key2669, 2), (key2663, 2), (key2752, -1), (key2752, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2)]

def rawRow15531 : Integer.Sparse Key := [(key2698, 2), (key2704, 2), (key2724, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, -1), (key2630, -1), (key2851, -1), (key2868, -1), (key3021, -1), (key3025, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2)]

def rawRow15532 : Integer.Sparse Key := [(key2704, 2), (key2698, 2), (key2724, 2), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, -1), (key2624, -1), (key2868, -1), (key2851, -1), (key3025, -1), (key3021, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2)]

def rawRow15533 : Integer.Sparse Key := [(key2698, 2), (key2724, 2), (key2704, 2), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, -1), (key3021, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2)]

def rawRow15534 : Integer.Sparse Key := [(key2724, 2), (key2698, 2), (key2704, 2), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key2868, -1), (key2630, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2)]

def rawRow15535 : Integer.Sparse Key := [(key2704, 2), (key2724, 2), (key2698, 2), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2624, -1), (key2851, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2)]

def rawRow15536 : Integer.Sparse Key := [(key2724, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, -1), (key2868, -1), (key3021, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2)]

def rawRow15537 : Integer.Sparse Key := [(key2778, 2), (key2784, 2), (key2792, 2), (key2801, -1), (key2807, -1), (key2851, -1), (key2918, -1), (key2858, -1), (key2919, -1), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2)]

def rawRow15538 : Integer.Sparse Key := [(key2784, 2), (key2778, 2), (key2792, 2), (key2807, -1), (key2801, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2858, -1), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2)]

def rawRow15539 : Integer.Sparse Key := [(key2778, 2), (key2792, 2), (key2784, 2), (key2851, -1), (key2858, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2)]

def rawRow15540 : Integer.Sparse Key := [(key2792, 2), (key2778, 2), (key2784, 2), (key2858, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2918, -1), (key2807, -1), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2)]

def rawRow15541 : Integer.Sparse Key := [(key2784, 2), (key2792, 2), (key2778, 2), (key2918, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2)]

def rawRow15542 : Integer.Sparse Key := [(key2792, 2), (key2784, 2), (key2778, 2), (key2919, -1), (key2918, -1), (key2858, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2)]

def rawRow15543 : Integer.Sparse Key := [(key2801, 2), (key2807, 2), (key2827, 2), (key2778, -1), (key2784, -1), (key2851, -1), (key2918, -1), (key2868, -1), (key2922, -1), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2)]

def rawRow15544 : Integer.Sparse Key := [(key2807, 2), (key2801, 2), (key2827, 2), (key2784, -1), (key2778, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2868, -1), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2)]

def rawRow15545 : Integer.Sparse Key := [(key2801, 2), (key2827, 2), (key2807, 2), (key2851, -1), (key2868, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2)]

def rawRow15546 : Integer.Sparse Key := [(key2827, 2), (key2801, 2), (key2807, 2), (key2868, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2918, -1), (key2784, -1), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2)]

def rawRow15547 : Integer.Sparse Key := [(key2807, 2), (key2827, 2), (key2801, 2), (key2918, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2778, -1), (key2851, -1), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2)]

def rawRow15548 : Integer.Sparse Key := [(key2827, 2), (key2807, 2), (key2801, 2), (key2922, -1), (key2918, -1), (key2868, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2)]

def rawRow15549 : Integer.Sparse Key := [(key2851, 2), (key2858, 2), (key2868, 2), (key2778, -1), (key2792, -1), (key2801, -1), (key2919, -1), (key2827, -1), (key2922, -1), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2778, -1), (key2792, -1), (key2801, -1), (key2919, -1), (key2827, -1), (key2922, -1), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2)]

def rawRow15550 : Integer.Sparse Key := [(key2858, 2), (key2851, 2), (key2868, 2), (key2792, -1), (key2778, -1), (key2919, -1), (key2801, -1), (key2922, -1), (key2827, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2792, -1), (key2778, -1), (key2919, -1), (key2801, -1), (key2922, -1), (key2827, -1), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2)]

def rawRow15551 : Integer.Sparse Key := [(key2851, 2), (key2868, 2), (key2858, 2), (key2801, -1), (key2827, -1), (key2778, -1), (key2922, -1), (key2792, -1), (key2919, -1), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2801, -1), (key2827, -1), (key2778, -1), (key2922, -1), (key2792, -1), (key2919, -1), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2)]

def rawRow15552 : Integer.Sparse Key := [(key2868, 2), (key2851, 2), (key2858, 2), (key2827, -1), (key2801, -1), (key2922, -1), (key2778, -1), (key2919, -1), (key2792, -1), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2827, -1), (key2801, -1), (key2922, -1), (key2778, -1), (key2919, -1), (key2792, -1), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2)]

def rawRow15553 : Integer.Sparse Key := [(key2858, 2), (key2868, 2), (key2851, 2), (key2919, -1), (key2922, -1), (key2792, -1), (key2827, -1), (key2778, -1), (key2801, -1), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key2919, -1), (key2922, -1), (key2792, -1), (key2827, -1), (key2778, -1), (key2801, -1), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2)]

def rawRow15554 : Integer.Sparse Key := [(key2868, 2), (key2858, 2), (key2851, 2), (key2922, -1), (key2919, -1), (key2827, -1), (key2792, -1), (key2801, -1), (key2778, -1), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key2922, -1), (key2919, -1), (key2827, -1), (key2792, -1), (key2801, -1), (key2778, -1), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2)]

def rawRow15555 : Integer.Sparse Key := [(key2772, 4), (key2889, 4), (key2889, 4), (key2766, -2), (key2766, -2), (key2843, -2), (key2843, -2), (key2887, -2), (key2887, -2), (key2931, -2), (key2931, -2), (key2968, -2), (key2968, -2), (key2995, -2), (key2995, -2), (key2929, 4), (key2966, 4), (key2966, 4)]

def rawRow15556 : Integer.Sparse Key := [(key2889, 4), (key2772, 4), (key2889, 4), (key2843, -2), (key2887, -2), (key2766, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2966, 4), (key2929, 4), (key2966, 4)]

def rawRow15557 : Integer.Sparse Key := [(key2889, 4), (key2889, 4), (key2772, 4), (key2887, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2766, -2), (key2995, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2931, -2), (key2966, 4), (key2966, 4), (key2929, 4)]

def rawRow15558 : Integer.Sparse Key := [(key2411, 4), (key2484, 4), (key2484, 4), (key2443, -2), (key2443, -2), (key2509, -2), (key2509, -2), (key2524, -2), (key2524, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15559 : Integer.Sparse Key := [(key2484, 4), (key2411, 4), (key2484, 4), (key2509, -2), (key2524, -2), (key2443, -2), (key2524, -2), (key2443, -2), (key2509, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15560 : Integer.Sparse Key := [(key2484, 4), (key2484, 4), (key2411, 4), (key2524, -2), (key2509, -2), (key2524, -2), (key2443, -2), (key2509, -2), (key2443, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15561 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key1015, -2), (key993, 6), (key1232, -2), (key1232, -2), (key1235, -2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1242, 6), (key1071, -2), (key1150, -2), (key1150, -2)]

def rawRow15562 : Integer.Sparse Key := [(key1001, -2), (key1015, -2), (key1001, -2), (key993, 6), (key1232, -2), (key1235, -2), (key1232, -2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1242, 6), (key1150, -2), (key1071, -2), (key1150, -2)]

def rawRow15563 : Integer.Sparse Key := [(key1015, -2), (key1001, -2), (key1001, -2), (key993, 6), (key1235, -2), (key1232, -2), (key1232, -2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1242, 6), (key1150, -2), (key1150, -2), (key1071, -2)]

def rawRow15564 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1235, -2), (key1242, 6), (key1001, -2), (key1001, -2), (key1015, -2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1071, -2), (key1150, -2), (key1150, -2), (key993, 6), (key1028, -2), (key1106, -2), (key1106, -2)]

def rawRow15565 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1232, -2), (key1242, 6), (key1001, -2), (key1015, -2), (key1001, -2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, -2), (key1071, -2), (key1150, -2), (key993, 6), (key1106, -2), (key1028, -2), (key1106, -2)]

def rawRow15566 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1232, -2), (key1242, 6), (key1015, -2), (key1001, -2), (key1001, -2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1150, -2), (key1150, -2), (key1071, -2), (key993, 6), (key1106, -2), (key1106, -2), (key1028, -2)]

def rawRow15567 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2388, -2), (key2370, 6), (key2876, -2), (key2876, -2), (key2925, -2), (key2768, 2), (key2768, 2), (key2845, 2), (key2845, 2), (key2916, 2), (key2916, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key3028, 6), (key3005, -2), (key3019, -2), (key3019, -2)]

def rawRow15568 : Integer.Sparse Key := [(key2376, -2), (key2388, -2), (key2376, -2), (key2370, 6), (key2876, -2), (key2925, -2), (key2876, -2), (key2845, 2), (key2916, 2), (key2768, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key3028, 6), (key3019, -2), (key3005, -2), (key3019, -2)]

def rawRow15569 : Integer.Sparse Key := [(key2388, -2), (key2376, -2), (key2376, -2), (key2370, 6), (key2925, -2), (key2876, -2), (key2876, -2), (key2916, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2768, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key3028, 6), (key3019, -2), (key3019, -2), (key3005, -2)]

def rawRow15570 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2570, -2), (key2575, 6), (key2376, -2), (key2376, -2), (key2388, -2), (key2404, 2), (key2404, 2), (key2470, 2), (key2470, 2), (key2478, 2), (key2478, 2), (key2435, -2), (key2501, -2), (key2501, -2), (key2370, 6), (key2762, -2), (key2839, -2), (key2839, -2)]

def rawRow15571 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2568, -2), (key2575, 6), (key2376, -2), (key2388, -2), (key2376, -2), (key2470, 2), (key2478, 2), (key2404, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2501, -2), (key2435, -2), (key2501, -2), (key2370, 6), (key2839, -2), (key2762, -2), (key2839, -2)]

def rawRow15572 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2568, -2), (key2575, 6), (key2388, -2), (key2376, -2), (key2376, -2), (key2478, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2404, 2), (key2501, -2), (key2501, -2), (key2435, -2), (key2370, 6), (key2839, -2), (key2839, -2), (key2762, -2)]

def rawRow15573 : Integer.Sparse Key := [(key2635, 6), (key2610, -2), (key2626, -2), (key2626, -2), (key2721, 6), (key2665, -2), (key2700, -2), (key2700, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow15574 : Integer.Sparse Key := [(key2635, 6), (key2626, -2), (key2610, -2), (key2626, -2), (key2721, 6), (key2700, -2), (key2665, -2), (key2700, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow15575 : Integer.Sparse Key := [(key2635, 6), (key2626, -2), (key2626, -2), (key2610, -2), (key2721, 6), (key2700, -2), (key2700, -2), (key2665, -2), (key2865, -2), (key2865, -2), (key2824, -2), (key2855, -2), (key2855, -2), (key2789, -2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow15576 : Integer.Sparse Key := [(key2721, 6), (key2824, -2), (key2865, -2), (key2865, -2), (key2635, 6), (key2789, -2), (key2855, -2), (key2855, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow15577 : Integer.Sparse Key := [(key2721, 6), (key2865, -2), (key2824, -2), (key2865, -2), (key2635, 6), (key2855, -2), (key2789, -2), (key2855, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow15578 : Integer.Sparse Key := [(key2721, 6), (key2865, -2), (key2865, -2), (key2824, -2), (key2635, 6), (key2855, -2), (key2855, -2), (key2789, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow15579 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key1014, -2), (key994, 6), (key1231, -2), (key1231, -2), (key1234, -2), (key1035, 2), (key1035, 2), (key1113, 2), (key1113, 2), (key1122, 2), (key1122, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1241, 6), (key1070, -2), (key1149, -2), (key1149, -2)]

def rawRow15580 : Integer.Sparse Key := [(key1000, -2), (key1014, -2), (key1000, -2), (key994, 6), (key1231, -2), (key1234, -2), (key1231, -2), (key1113, 2), (key1122, 2), (key1035, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1241, 6), (key1149, -2), (key1070, -2), (key1149, -2)]

def rawRow15581 : Integer.Sparse Key := [(key1014, -2), (key1000, -2), (key1000, -2), (key994, 6), (key1234, -2), (key1231, -2), (key1231, -2), (key1122, 2), (key1113, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1035, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1241, 6), (key1149, -2), (key1149, -2), (key1070, -2)]

def rawRow15582 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1234, -2), (key1241, 6), (key1000, -2), (key1000, -2), (key1014, -2), (key1035, 2), (key1035, 2), (key1113, 2), (key1113, 2), (key1122, 2), (key1122, 2), (key1070, -2), (key1149, -2), (key1149, -2), (key994, 6), (key1029, -2), (key1107, -2), (key1107, -2)]

def rawRow15583 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1231, -2), (key1241, 6), (key1000, -2), (key1014, -2), (key1000, -2), (key1113, 2), (key1122, 2), (key1035, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1149, -2), (key1070, -2), (key1149, -2), (key994, 6), (key1107, -2), (key1029, -2), (key1107, -2)]

def rawRow15584 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1231, -2), (key1241, 6), (key1014, -2), (key1000, -2), (key1000, -2), (key1122, 2), (key1113, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1035, 2), (key1149, -2), (key1149, -2), (key1070, -2), (key994, 6), (key1107, -2), (key1107, -2), (key1029, -2)]

def rawRow15585 : Integer.Sparse Key := [(key1044, 4), (key1130, 4), (key1130, 4), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15586 : Integer.Sparse Key := [(key1130, 4), (key1044, 4), (key1130, 4), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15587 : Integer.Sparse Key := [(key1130, 4), (key1130, 4), (key1044, 4), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15588 : Integer.Sparse Key := [(key1044, 4), (key1130, 4), (key1130, 4), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15589 : Integer.Sparse Key := [(key1130, 4), (key1044, 4), (key1130, 4), (key1159, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15590 : Integer.Sparse Key := [(key1130, 4), (key1130, 4), (key1044, 4), (key1174, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15591 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2752, -1), (key2752, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2919, -1), (key2919, -1), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1), (key3009, 2), (key3022, 2), (key3022, 2), (key3007, -1), (key3007, -1), (key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1)]

def rawRow15592 : Integer.Sparse Key := [(key2704, -1), (key2752, -1), (key2669, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2858, -1), (key2919, -1), (key2792, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key3022, 2), (key3009, 2), (key3022, 2), (key3011, -1), (key3021, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key3011, -1)]

def rawRow15593 : Integer.Sparse Key := [(key2752, -1), (key2704, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2919, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2792, -1), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1), (key3022, 2), (key3022, 2), (key3009, 2), (key3021, -1), (key3011, -1), (key3021, -1), (key3007, -1), (key3011, -1), (key3007, -1)]

def rawRow15594 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1), (key2919, -1), (key2919, -1), (key2757, 2), (key2922, 2), (key2922, 2), (key2669, -1), (key2669, -1), (key2784, -1), (key2784, -1), (key2792, -1), (key2792, -1), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2), (key2724, -1), (key2724, -1), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1)]

def rawRow15595 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2752, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2922, 2), (key2757, 2), (key2922, 2), (key2784, -1), (key2792, -1), (key2669, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2827, -1), (key2868, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key2827, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1)]

def rawRow15596 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2752, -1), (key2922, 2), (key2922, 2), (key2757, 2), (key2792, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2669, -1), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2), (key2868, -1), (key2827, -1), (key2868, -1), (key2724, -1), (key2827, -1), (key2724, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1)]

def rawRow15597 : Integer.Sparse Key := [(key2688, 4), (key2714, 4), (key2714, 4), (key2681, -4), (key2681, -4), (key2712, -4), (key2817, -4), (key2817, -4), (key2863, -4), (key2815, 12)]

def rawRow15598 : Integer.Sparse Key := [(key2714, 4), (key2688, 4), (key2714, 4), (key2681, -4), (key2712, -4), (key2681, -4), (key2817, -4), (key2863, -4), (key2817, -4), (key2815, 12)]

def rawRow15599 : Integer.Sparse Key := [(key2714, 4), (key2714, 4), (key2688, 4), (key2712, -4), (key2681, -4), (key2681, -4), (key2863, -4), (key2817, -4), (key2817, -4), (key2815, 12)]

def rawRow15600 : Integer.Sparse Key := [(key2688, 4), (key2817, 4), (key2817, 4), (key2681, -4), (key2681, -4), (key2815, -4), (key2714, -4), (key2714, -4), (key2863, -4), (key2712, 12)]

def rawRow15601 : Integer.Sparse Key := [(key2817, 4), (key2688, 4), (key2817, 4), (key2681, -4), (key2815, -4), (key2681, -4), (key2714, -4), (key2863, -4), (key2714, -4), (key2712, 12)]

def rawRow15602 : Integer.Sparse Key := [(key2817, 4), (key2817, 4), (key2688, 4), (key2815, -4), (key2681, -4), (key2681, -4), (key2863, -4), (key2714, -4), (key2714, -4), (key2712, 12)]

def rawRow15603 : Integer.Sparse Key := [(key2688, 4), (key2714, 4), (key2714, 4), (key2817, -4), (key2817, -4), (key2863, -4), (key2681, -4), (key2681, -4), (key2712, -4), (key2815, 12)]

def rawRow15604 : Integer.Sparse Key := [(key2714, 4), (key2688, 4), (key2714, 4), (key2817, -4), (key2863, -4), (key2817, -4), (key2681, -4), (key2712, -4), (key2681, -4), (key2815, 12)]

def rawRow15605 : Integer.Sparse Key := [(key2714, 4), (key2714, 4), (key2688, 4), (key2863, -4), (key2817, -4), (key2817, -4), (key2712, -4), (key2681, -4), (key2681, -4), (key2815, 12)]

def rawRow15606 : Integer.Sparse Key := [(key2688, 4), (key2817, 4), (key2817, 4), (key2714, -4), (key2714, -4), (key2863, -4), (key2681, -4), (key2681, -4), (key2815, -4), (key2712, 12)]

def rawRow15607 : Integer.Sparse Key := [(key2817, 4), (key2688, 4), (key2817, 4), (key2714, -4), (key2863, -4), (key2714, -4), (key2681, -4), (key2815, -4), (key2681, -4), (key2712, 12)]

def rawRow15608 : Integer.Sparse Key := [(key2817, 4), (key2817, 4), (key2688, 4), (key2863, -4), (key2714, -4), (key2714, -4), (key2815, -4), (key2681, -4), (key2681, -4), (key2712, 12)]

def rawRow15609 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2599, -2), (key2584, 6), (key2875, -2), (key2875, -2), (key2909, -2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2888, 2), (key2888, 2), (key2763, -2), (key2840, -2), (key2840, -2), (key2988, 6), (key2930, -2), (key2967, -2), (key2967, -2)]

def rawRow15610 : Integer.Sparse Key := [(key2588, -2), (key2599, -2), (key2588, -2), (key2584, 6), (key2875, -2), (key2909, -2), (key2875, -2), (key2844, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2840, -2), (key2763, -2), (key2840, -2), (key2988, 6), (key2967, -2), (key2930, -2), (key2967, -2)]

def rawRow15611 : Integer.Sparse Key := [(key2599, -2), (key2588, -2), (key2588, -2), (key2584, 6), (key2909, -2), (key2875, -2), (key2875, -2), (key2888, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2840, -2), (key2840, -2), (key2763, -2), (key2988, 6), (key2967, -2), (key2967, -2), (key2930, -2)]

def rawRow15612 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2930, -2), (key2763, 6), (key2875, -2), (key2875, -2), (key2988, -2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2967, 2), (key2967, 2), (key2584, -2), (key2840, -2), (key2840, -2), (key2909, 6), (key2599, -2), (key2888, -2), (key2888, -2)]

def rawRow15613 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2767, -2), (key2763, 6), (key2875, -2), (key2988, -2), (key2875, -2), (key2844, 2), (key2967, 2), (key2588, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2840, -2), (key2584, -2), (key2840, -2), (key2909, 6), (key2888, -2), (key2599, -2), (key2888, -2)]

def rawRow15614 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2767, -2), (key2763, 6), (key2988, -2), (key2875, -2), (key2875, -2), (key2967, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, -2), (key2840, -2), (key2584, -2), (key2909, 6), (key2888, -2), (key2888, -2), (key2599, -2)]

def rawRow15615 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2909, -2), (key2988, 6), (key2588, -2), (key2588, -2), (key2599, -2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2888, 2), (key2888, 2), (key2930, -2), (key2967, -2), (key2967, -2), (key2584, 6), (key2763, -2), (key2840, -2), (key2840, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15616 : Integer.Sparse Key := [(key2875, -2), (key2909, -2), (key2875, -2), (key2988, 6), (key2588, -2), (key2599, -2), (key2588, -2), (key2844, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, -2), (key2930, -2), (key2967, -2), (key2584, 6), (key2840, -2), (key2763, -2), (key2840, -2)]

def rawRow15617 : Integer.Sparse Key := [(key2909, -2), (key2875, -2), (key2875, -2), (key2988, 6), (key2599, -2), (key2588, -2), (key2588, -2), (key2888, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2967, -2), (key2967, -2), (key2930, -2), (key2584, 6), (key2840, -2), (key2840, -2), (key2763, -2)]

def rawRow15618 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2988, -2), (key2909, 6), (key2767, -2), (key2767, -2), (key2930, -2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2967, 2), (key2967, 2), (key2599, -2), (key2888, -2), (key2888, -2), (key2763, 6), (key2584, -2), (key2840, -2), (key2840, -2)]

def rawRow15619 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2875, -2), (key2909, 6), (key2767, -2), (key2930, -2), (key2767, -2), (key2844, 2), (key2967, 2), (key2588, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2888, -2), (key2599, -2), (key2888, -2), (key2763, 6), (key2840, -2), (key2584, -2), (key2840, -2)]

def rawRow15620 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2875, -2), (key2909, 6), (key2930, -2), (key2767, -2), (key2767, -2), (key2967, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2888, -2), (key2888, -2), (key2599, -2), (key2763, 6), (key2840, -2), (key2840, -2), (key2584, -2)]

def rawRow15621 : Integer.Sparse Key := [(key2025, 4), (key2054, 4), (key2054, 4), (key2012, -4), (key2012, -4), (key2041, -4), (key2143, -4), (key2143, -4), (key2227, -4), (key2126, 12)]

def rawRow15622 : Integer.Sparse Key := [(key2054, 4), (key2025, 4), (key2054, 4), (key2012, -4), (key2041, -4), (key2012, -4), (key2143, -4), (key2227, -4), (key2143, -4), (key2126, 12)]

def rawRow15623 : Integer.Sparse Key := [(key2054, 4), (key2054, 4), (key2025, 4), (key2041, -4), (key2012, -4), (key2012, -4), (key2227, -4), (key2143, -4), (key2143, -4), (key2126, 12)]

def rawRow15624 : Integer.Sparse Key := [(key2025, 4), (key2143, 4), (key2143, 4), (key2012, -4), (key2012, -4), (key2126, -4), (key2054, -4), (key2054, -4), (key2227, -4), (key2041, 12)]

def rawRow15625 : Integer.Sparse Key := [(key2143, 4), (key2025, 4), (key2143, 4), (key2012, -4), (key2126, -4), (key2012, -4), (key2054, -4), (key2227, -4), (key2054, -4), (key2041, 12)]

def rawRow15626 : Integer.Sparse Key := [(key2143, 4), (key2143, 4), (key2025, 4), (key2126, -4), (key2012, -4), (key2012, -4), (key2227, -4), (key2054, -4), (key2054, -4), (key2041, 12)]

def rawRow15627 : Integer.Sparse Key := [(key2025, 4), (key2054, 4), (key2054, 4), (key2143, -4), (key2143, -4), (key2227, -4), (key2012, -4), (key2012, -4), (key2041, -4), (key2126, 12)]

def rawRow15628 : Integer.Sparse Key := [(key2054, 4), (key2025, 4), (key2054, 4), (key2143, -4), (key2227, -4), (key2143, -4), (key2012, -4), (key2041, -4), (key2012, -4), (key2126, 12)]

def rawRow15629 : Integer.Sparse Key := [(key2054, 4), (key2054, 4), (key2025, 4), (key2227, -4), (key2143, -4), (key2143, -4), (key2041, -4), (key2012, -4), (key2012, -4), (key2126, 12)]

def rawRow15630 : Integer.Sparse Key := [(key2025, 4), (key2143, 4), (key2143, 4), (key2054, -4), (key2054, -4), (key2227, -4), (key2012, -4), (key2012, -4), (key2126, -4), (key2041, 12)]

def rawRow15631 : Integer.Sparse Key := [(key2143, 4), (key2025, 4), (key2143, 4), (key2054, -4), (key2227, -4), (key2054, -4), (key2012, -4), (key2126, -4), (key2012, -4), (key2041, 12)]

def rawRow15632 : Integer.Sparse Key := [(key2143, 4), (key2143, 4), (key2025, 4), (key2227, -4), (key2054, -4), (key2054, -4), (key2126, -4), (key2012, -4), (key2012, -4), (key2041, 12)]

def rawRow15633 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2736, -1), (key2736, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2896, -1), (key2896, -1), (key2783, 2), (key2783, 2), (key2806, 2), (key2806, 2), (key2894, 2), (key2894, 2), (key2779, -1), (key2779, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2937, -1), (key2937, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1)]

def rawRow15634 : Integer.Sparse Key := [(key2703, -1), (key2736, -1), (key2668, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2857, -1), (key2896, -1), (key2791, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2806, 2), (key2894, 2), (key2783, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2802, -1), (key2852, -1), (key2779, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2949, -1), (key2973, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2949, -1)]

def rawRow15635 : Integer.Sparse Key := [(key2736, -1), (key2703, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2896, -1), (key2857, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2791, -1), (key2894, 2), (key2806, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2783, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2779, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2973, -1), (key2949, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2937, -1)]

def rawRow15636 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2629, 2), (key2629, 2), (key2703, 2), (key2703, 2), (key2973, 2), (key2973, 2), (key2625, -1), (key2625, -1), (key2699, -1), (key2699, -1), (key2852, -1), (key2852, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2647, -1), (key2647, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1)]

def rawRow15637 : Integer.Sparse Key := [(key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2699, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2736, -1), (key2894, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2736, -1)]

def rawRow15638 : Integer.Sparse Key := [(key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2973, 2), (key2703, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2629, 2), (key2852, -1), (key2699, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2625, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2894, -1), (key2736, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2647, -1)]

def rawRow15639 : Integer.Sparse Key := [(key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2896, -1), (key2896, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2736, -1), (key2736, -1), (key2783, 2), (key2783, 2), (key2806, 2), (key2806, 2), (key2894, 2), (key2894, 2), (key2937, -1), (key2937, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2779, -1), (key2779, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1)]

def rawRow15640 : Integer.Sparse Key := [(key2857, -1), (key2896, -1), (key2791, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2703, -1), (key2736, -1), (key2668, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2806, 2), (key2894, 2), (key2783, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2949, -1), (key2973, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2802, -1), (key2852, -1), (key2779, -1), (key2852, -1), (key2779, -1), (key2802, -1)]

def rawRow15641 : Integer.Sparse Key := [(key2896, -1), (key2857, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2791, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2736, -1), (key2703, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2894, 2), (key2806, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2783, 2), (key2973, -1), (key2949, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2937, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2779, -1)]

def rawRow15642 : Integer.Sparse Key := [(key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2629, 2), (key2629, 2), (key2703, 2), (key2703, 2), (key2973, 2), (key2973, 2), (key2647, -1), (key2647, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2625, -1), (key2625, -1), (key2699, -1), (key2699, -1), (key2852, -1), (key2852, -1)]

def rawRow15643 : Integer.Sparse Key := [(key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2736, -1), (key2894, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2699, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2699, -1)]

def rawRow15644 : Integer.Sparse Key := [(key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2973, 2), (key2703, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2629, 2), (key2894, -1), (key2736, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2647, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2852, -1), (key2699, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2625, -1)]

def rawRow15645 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1374, -2), (key1358, 6), (key1937, -2), (key1937, -2), (key1940, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1484, -2), (key1710, -2), (key1710, -2), (key1949, 6), (key1513, -2), (key1741, -2), (key1741, -2)]

def rawRow15646 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1364, -2), (key1358, 6), (key1937, -2), (key1940, -2), (key1937, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1710, -2), (key1484, -2), (key1710, -2), (key1949, 6), (key1741, -2), (key1513, -2), (key1741, -2)]

def rawRow15647 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1364, -2), (key1358, 6), (key1940, -2), (key1937, -2), (key1937, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1710, -2), (key1710, -2), (key1484, -2), (key1949, 6), (key1741, -2), (key1741, -2), (key1513, -2)]

def rawRow15648 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1513, -2), (key1484, 6), (key1937, -2), (key1937, -2), (key1949, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1358, -2), (key1710, -2), (key1710, -2), (key1940, 6), (key1374, -2), (key1723, -2), (key1723, -2)]

def rawRow15649 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1490, -2), (key1484, 6), (key1937, -2), (key1949, -2), (key1937, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1710, -2), (key1358, -2), (key1710, -2), (key1940, 6), (key1723, -2), (key1374, -2), (key1723, -2)]

def rawRow15650 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1490, -2), (key1484, 6), (key1949, -2), (key1937, -2), (key1937, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1710, -2), (key1710, -2), (key1358, -2), (key1940, 6), (key1723, -2), (key1723, -2), (key1374, -2)]

def rawRow15651 : Integer.Sparse Key := [(key1937, -2), (key1937, -2), (key1940, -2), (key1949, 6), (key1364, -2), (key1364, -2), (key1374, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1513, -2), (key1741, -2), (key1741, -2), (key1358, 6), (key1484, -2), (key1710, -2), (key1710, -2)]

def rawRow15652 : Integer.Sparse Key := [(key1937, -2), (key1940, -2), (key1937, -2), (key1949, 6), (key1364, -2), (key1374, -2), (key1364, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, -2), (key1513, -2), (key1741, -2), (key1358, 6), (key1710, -2), (key1484, -2), (key1710, -2)]

def rawRow15653 : Integer.Sparse Key := [(key1940, -2), (key1937, -2), (key1937, -2), (key1949, 6), (key1374, -2), (key1364, -2), (key1364, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1741, -2), (key1741, -2), (key1513, -2), (key1358, 6), (key1710, -2), (key1710, -2), (key1484, -2)]

def rawRow15654 : Integer.Sparse Key := [(key1937, -2), (key1937, -2), (key1949, -2), (key1940, 6), (key1490, -2), (key1490, -2), (key1513, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1374, -2), (key1723, -2), (key1723, -2), (key1484, 6), (key1358, -2), (key1710, -2), (key1710, -2)]

def rawRow15655 : Integer.Sparse Key := [(key1937, -2), (key1949, -2), (key1937, -2), (key1940, 6), (key1490, -2), (key1513, -2), (key1490, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, -2), (key1374, -2), (key1723, -2), (key1484, 6), (key1710, -2), (key1358, -2), (key1710, -2)]

def rawRow15656 : Integer.Sparse Key := [(key1949, -2), (key1937, -2), (key1937, -2), (key1940, 6), (key1513, -2), (key1490, -2), (key1490, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1723, -2), (key1723, -2), (key1374, -2), (key1484, 6), (key1710, -2), (key1710, -2), (key1358, -2)]

def rawRow15657 : Integer.Sparse Key := [(key2383, 2), (key2394, 2), (key2394, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2880, 2), (key2910, 2), (key2910, 2), (key2766, -1), (key2766, -1), (key2843, -1), (key2843, -1), (key2887, -1), (key2887, -1), (key2989, -2), (key2989, -2), (key3002, -2), (key2931, -1), (key2931, -1), (key2968, -1), (key2968, -1), (key2995, -1), (key2995, -1), (key2929, 4), (key2966, 4), (key2966, 4)]

def rawRow15658 : Integer.Sparse Key := [(key2394, 2), (key2383, 2), (key2394, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2910, 2), (key2880, 2), (key2910, 2), (key2843, -1), (key2887, -1), (key2766, -1), (key2887, -1), (key2766, -1), (key2843, -1), (key2989, -2), (key3002, -2), (key2989, -2), (key2968, -1), (key2995, -1), (key2931, -1), (key2995, -1), (key2931, -1), (key2968, -1), (key2966, 4), (key2929, 4), (key2966, 4)]

def rawRow15659 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2383, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2910, 2), (key2910, 2), (key2880, 2), (key2887, -1), (key2843, -1), (key2887, -1), (key2766, -1), (key2843, -1), (key2766, -1), (key3002, -2), (key2989, -2), (key2989, -2), (key2995, -1), (key2968, -1), (key2995, -1), (key2931, -1), (key2968, -1), (key2931, -1), (key2966, 4), (key2966, 4), (key2929, 4)]

def rawRow15660 : Integer.Sparse Key := [(key2411, 2), (key2443, 2), (key2443, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2880, 2), (key2989, 2), (key2989, 2), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2995, -1), (key2995, -1), (key2598, 4), (key2887, 4), (key2887, 4)]

def rawRow15661 : Integer.Sparse Key := [(key2443, 2), (key2411, 2), (key2443, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2989, 2), (key2880, 2), (key2989, 2), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, -1), (key2995, -1), (key2600, -1), (key2995, -1), (key2600, -1), (key2889, -1), (key2887, 4), (key2598, 4), (key2887, 4)]

def rawRow15662 : Integer.Sparse Key := [(key2443, 2), (key2443, 2), (key2411, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2989, 2), (key2989, 2), (key2880, 2), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, -1), (key2889, -1), (key2995, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2887, 4), (key2887, 4), (key2598, 4)]

def rawRow15663 : Integer.Sparse Key := [(key2569, 2), (key2571, 2), (key2571, 2), (key2576, -2), (key2576, -2), (key2580, -2), (key2383, 2), (key2394, 2), (key2394, 2), (key2443, -1), (key2443, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15664 : Integer.Sparse Key := [(key2571, 2), (key2569, 2), (key2571, 2), (key2576, -2), (key2580, -2), (key2576, -2), (key2394, 2), (key2383, 2), (key2394, 2), (key2509, -1), (key2524, -1), (key2443, -1), (key2524, -1), (key2443, -1), (key2509, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15665 : Integer.Sparse Key := [(key2571, 2), (key2571, 2), (key2569, 2), (key2580, -2), (key2576, -2), (key2576, -2), (key2394, 2), (key2394, 2), (key2383, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2443, -1), (key2509, -1), (key2443, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15666 : Integer.Sparse Key := [(key2569, 2), (key2576, 2), (key2576, 2), (key2571, -2), (key2571, -2), (key2580, -2), (key2411, 2), (key2443, 2), (key2443, 2), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, -1), (key2524, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow15667 : Integer.Sparse Key := [(key2576, 2), (key2569, 2), (key2576, 2), (key2571, -2), (key2580, -2), (key2571, -2), (key2443, 2), (key2411, 2), (key2443, 2), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow15668 : Integer.Sparse Key := [(key2576, 2), (key2576, 2), (key2569, 2), (key2580, -2), (key2571, -2), (key2571, -2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2394, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow15669 : Integer.Sparse Key := [(key2657, 2), (key2657, 2), (key2659, 2), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2752, -1), (key2752, -1), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2922, -1), (key2922, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2919, -1), (key2919, -1), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2)]

def rawRow15670 : Integer.Sparse Key := [(key2657, 2), (key2659, 2), (key2657, 2), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, -1), (key2752, -1), (key2669, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2)]

def rawRow15671 : Integer.Sparse Key := [(key2659, 2), (key2657, 2), (key2657, 2), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, -1), (key2704, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2922, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2827, -1), (key2919, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2792, -1), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2)]

def rawRow15672 : Integer.Sparse Key := [(key2752, 2), (key2752, 2), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, -1), (key2638, -1), (key2858, -1), (key2858, -1), (key3022, -1), (key3022, -1), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2)]

def rawRow15673 : Integer.Sparse Key := [(key2752, 2), (key2757, 2), (key2752, 2), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2)]

def rawRow15674 : Integer.Sparse Key := [(key2757, 2), (key2752, 2), (key2752, 2), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2)]

def rawRow15675 : Integer.Sparse Key := [(key3007, 2), (key3007, 2), (key3009, 2), (key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1), (key3022, -1), (key3022, -1), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1), (key2919, -1), (key2919, -1), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2669, -1), (key2669, -1), (key2784, -1), (key2784, -1), (key2792, -1), (key2792, -1), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2)]

def rawRow15676 : Integer.Sparse Key := [(key3007, 2), (key3009, 2), (key3007, 2), (key3021, -1), (key3022, -1), (key3011, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, -1), (key2919, -1), (key2752, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2)]

def rawRow15677 : Integer.Sparse Key := [(key3009, 2), (key3007, 2), (key3007, 2), (key3022, -1), (key3021, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3011, -1), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, -1), (key2918, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2752, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2669, -1), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2)]

def rawRow15678 : Integer.Sparse Key := [(key3011, 2), (key3011, 2), (key3016, 2), (key3007, -1), (key3007, -1), (key3021, -1), (key3021, -1), (key3025, -1), (key3025, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2)]

def rawRow15679 : Integer.Sparse Key := [(key3011, 2), (key3016, 2), (key3011, 2), (key3021, -1), (key3025, -1), (key3007, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2)]

def rawRow15680 : Integer.Sparse Key := [(key3016, 2), (key3011, 2), (key3011, 2), (key3025, -1), (key3021, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2)]

def rawRow15681 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2614, 2), (key2630, 2), (key2638, 2), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2669, -2), (key2704, -2), (key2724, -2), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1), (key3011, 2), (key3021, 2), (key3022, 2), (key3007, -2), (key3021, -2), (key3025, -2)]

def rawRow15682 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2669, -2), (key2724, -2), (key2704, -2), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, -2), (key3025, -2), (key3021, -2)]

def rawRow15683 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2630, 2), (key2614, 2), (key2638, 2), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2704, -2), (key2669, -2), (key2724, -2), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key3021, 2), (key3011, 2), (key3022, 2), (key3021, -2), (key3007, -2), (key3025, -2)]

def rawRow15684 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2630, 2), (key2638, 2), (key2614, 2), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2704, -2), (key2724, -2), (key2669, -2), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, -2), (key3025, -2), (key3007, -2)]

def rawRow15685 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2724, -2), (key2669, -2), (key2704, -2), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, -2), (key3007, -2), (key3021, -2)]

def rawRow15686 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2638, 2), (key2630, 2), (key2614, 2), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2724, -2), (key2704, -2), (key2669, -2), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key3022, 2), (key3021, 2), (key3011, 2), (key3025, -2), (key3021, -2), (key3007, -2)]

def rawRow15687 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2608, 2), (key2624, 2), (key2624, 2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2752, 1), (key2752, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2922, -1), (key2922, -1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2919, 1), (key2919, 1), (key3016, 2), (key3025, 2), (key3025, 2), (key3009, -2), (key3022, -2), (key3022, -2)]

def rawRow15688 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2624, 2), (key2608, 2), (key2624, 2), (key2704, 1), (key2752, 1), (key2669, 1), (key2752, 1), (key2669, 1), (key2704, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2868, -1), (key2922, -1), (key2827, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2858, 1), (key2919, 1), (key2792, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key3025, 2), (key3016, 2), (key3025, 2), (key3022, -2), (key3009, -2), (key3022, -2)]

def rawRow15689 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2624, 2), (key2624, 2), (key2608, 2), (key2752, 1), (key2704, 1), (key2752, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2922, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2827, -1), (key2919, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2792, 1), (key3025, 2), (key3025, 2), (key3016, 2), (key3022, -2), (key3022, -2), (key3009, -2)]

def rawRow15690 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2669, 2), (key2704, 2), (key2752, 2), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2614, -2), (key2807, -2), (key2827, -2), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2752, 2), (key2918, 2), (key2919, 2), (key2657, -2), (key2918, -2), (key2922, -2)]

def rawRow15691 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2669, 2), (key2752, 2), (key2704, 2), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2614, -2), (key2827, -2), (key2807, -2), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, -2), (key2922, -2), (key2918, -2)]

def rawRow15692 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2704, 2), (key2669, 2), (key2752, 2), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2807, -2), (key2614, -2), (key2827, -2), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2918, 2), (key2752, 2), (key2919, 2), (key2918, -2), (key2657, -2), (key2922, -2)]

def rawRow15693 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2704, 2), (key2752, 2), (key2669, 2), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2807, -2), (key2827, -2), (key2614, -2), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, -2), (key2922, -2), (key2657, -2)]

def rawRow15694 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key2752, 2), (key2669, 2), (key2704, 2), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2827, -2), (key2614, -2), (key2807, -2), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, -2), (key2657, -2), (key2918, -2)]

def rawRow15695 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2752, 2), (key2704, 2), (key2669, 2), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2827, -2), (key2807, -2), (key2614, -2), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key2919, 2), (key2918, 2), (key2752, 2), (key2922, -2), (key2918, -2), (key2657, -2)]

def rawRow15696 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2608, -2), (key2801, -2), (key2801, -2), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2757, 2), (key2922, 2), (key2922, 2), (key2659, -2), (key2919, -2), (key2919, -2)]

def rawRow15697 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2801, -2), (key2608, -2), (key2801, -2), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2922, 2), (key2757, 2), (key2922, 2), (key2919, -2), (key2659, -2), (key2919, -2)]

def rawRow15698 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2801, -2), (key2801, -2), (key2608, -2), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2922, 2), (key2922, 2), (key2757, 2), (key2919, -2), (key2919, -2), (key2659, -2)]

def rawRow15699 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2851, -1), (key2918, -1), (key2858, -1), (key2919, -1), (key2827, 2), (key2868, 2), (key2922, 2), (key2698, 1), (key2704, 1), (key2851, 1), (key3021, 1), (key2858, 1), (key3022, 1), (key2724, -2), (key2868, -2), (key3025, -2), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2614, 2), (key2630, 2), (key2638, 2), (key2669, -2), (key2704, -2), (key2724, -2)]

def rawRow15700 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2858, -1), (key2827, 2), (key2922, 2), (key2868, 2), (key2704, 1), (key2698, 1), (key3021, 1), (key2851, 1), (key3022, 1), (key2858, 1), (key2724, -2), (key3025, -2), (key2868, -2), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, -2), (key2724, -2), (key2704, -2)]

def rawRow15701 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2868, 2), (key2827, 2), (key2922, 2), (key2851, 1), (key2858, 1), (key2698, 1), (key3022, 1), (key2704, 1), (key3021, 1), (key2868, -2), (key2724, -2), (key3025, -2), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2630, 2), (key2614, 2), (key2638, 2), (key2704, -2), (key2669, -2), (key2724, -2)]

def rawRow15702 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2918, -1), (key2807, -1), (key2868, 2), (key2922, 2), (key2827, 2), (key2858, 1), (key2851, 1), (key3022, 1), (key2698, 1), (key3021, 1), (key2704, 1), (key2868, -2), (key3025, -2), (key2724, -2), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2630, 2), (key2638, 2), (key2614, 2), (key2704, -2), (key2724, -2), (key2669, -2)]

def rawRow15703 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2922, 2), (key2827, 2), (key2868, 2), (key3021, 1), (key3022, 1), (key2704, 1), (key2858, 1), (key2698, 1), (key2851, 1), (key3025, -2), (key2724, -2), (key2868, -2), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, -2), (key2669, -2), (key2704, -2)]

def rawRow15704 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2858, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 2), (key2868, 2), (key2827, 2), (key3022, 1), (key3021, 1), (key2858, 1), (key2704, 1), (key2851, 1), (key2698, 1), (key3025, -2), (key2868, -2), (key2724, -2), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2638, 2), (key2630, 2), (key2614, 2), (key2724, -2), (key2704, -2), (key2669, -2)]

def rawRow15705 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2851, -1), (key2918, -1), (key2868, -1), (key2922, -1), (key2792, 2), (key2858, 2), (key2919, 2), (key2624, 1), (key2630, 1), (key2851, 1), (key3021, 1), (key2868, 1), (key3025, 1), (key2638, -2), (key2858, -2), (key3022, -2), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2669, 2), (key2784, 2), (key2792, 2), (key2614, -2), (key2807, -2), (key2827, -2)]

def rawRow15706 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2868, -1), (key2792, 2), (key2919, 2), (key2858, 2), (key2630, 1), (key2624, 1), (key3021, 1), (key2851, 1), (key3025, 1), (key2868, 1), (key2638, -2), (key3022, -2), (key2858, -2), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2669, 2), (key2792, 2), (key2784, 2), (key2614, -2), (key2827, -2), (key2807, -2)]

def rawRow15707 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2858, 2), (key2792, 2), (key2919, 2), (key2851, 1), (key2868, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2858, -2), (key2638, -2), (key3022, -2), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2784, 2), (key2669, 2), (key2792, 2), (key2807, -2), (key2614, -2), (key2827, -2)]

def rawRow15708 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2918, -1), (key2784, -1), (key2858, 2), (key2919, 2), (key2792, 2), (key2868, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key3021, 1), (key2630, 1), (key2858, -2), (key3022, -2), (key2638, -2), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2784, 2), (key2792, 2), (key2669, 2), (key2807, -2), (key2827, -2), (key2614, -2)]

def rawRow15709 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2778, -1), (key2851, -1), (key2919, 2), (key2792, 2), (key2858, 2), (key3021, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2624, 1), (key2851, 1), (key3022, -2), (key2638, -2), (key2858, -2), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2792, 2), (key2669, 2), (key2784, 2), (key2827, -2), (key2614, -2), (key2807, -2)]

def rawRow15710 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2868, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2919, 2), (key2858, 2), (key2792, 2), (key3025, 1), (key3021, 1), (key2868, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key3022, -2), (key2858, -2), (key2638, -2), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2792, 2), (key2784, 2), (key2669, 2), (key2827, -2), (key2807, -2), (key2614, -2)]

def rawRow15711 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1), (key3022, -1), (key3022, -1), (key3016, 2), (key3025, 2), (key3025, 2), (key2752, 1), (key2752, 1), (key2918, 1), (key2918, 1), (key2919, 1), (key2919, 1), (key2757, -2), (key2922, -2), (key2922, -2), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, -2), (key2698, -2), (key2698, -2)]

def rawRow15712 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3011, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3025, 2), (key3016, 2), (key3025, 2), (key2918, 1), (key2919, 1), (key2752, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2922, -2), (key2757, -2), (key2922, -2), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, -2), (key2663, -2), (key2698, -2)]

def rawRow15713 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3011, -1), (key3025, 2), (key3025, 2), (key3016, 2), (key2919, 1), (key2918, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2752, 1), (key2922, -2), (key2922, -2), (key2757, -2), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, -2), (key2698, -2), (key2663, -2)]

def rawRow15714 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3021, -1), (key3021, -1), (key3025, -1), (key3025, -1), (key3009, 2), (key3022, 2), (key3022, 2), (key2657, 1), (key2657, 1), (key2918, 1), (key2918, 1), (key2922, 1), (key2922, 1), (key2659, -2), (key2919, -2), (key2919, -2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, -2), (key2801, -2), (key2801, -2)]

def rawRow15715 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3007, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3022, 2), (key3009, 2), (key3022, 2), (key2918, 1), (key2922, 1), (key2657, 1), (key2922, 1), (key2657, 1), (key2918, 1), (key2919, -2), (key2659, -2), (key2919, -2), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -2), (key2608, -2), (key2801, -2)]

def rawRow15716 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key3022, 2), (key3022, 2), (key3009, 2), (key2922, 1), (key2918, 1), (key2922, 1), (key2657, 1), (key2918, 1), (key2657, 1), (key2919, -2), (key2919, -2), (key2659, -2), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, -2), (key2801, -2), (key2608, -2)]

def rawRow15717 : Integer.Sparse Key := [(key2406, 4), (key2480, 4), (key2543, 4), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2437, -2), (key2440, -2), (key2503, -2), (key2554, -2), (key2522, -2), (key2563, -2), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15718 : Integer.Sparse Key := [(key2406, 4), (key2543, 4), (key2480, 4), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, -2), (key2437, -2), (key2554, -2), (key2503, -2), (key2563, -2), (key2522, -2), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15719 : Integer.Sparse Key := [(key2480, 4), (key2406, 4), (key2543, 4), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2503, -2), (key2522, -2), (key2437, -2), (key2563, -2), (key2440, -2), (key2554, -2), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15720 : Integer.Sparse Key := [(key2480, 4), (key2543, 4), (key2406, 4), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2522, -2), (key2503, -2), (key2563, -2), (key2437, -2), (key2554, -2), (key2440, -2), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15721 : Integer.Sparse Key := [(key2543, 4), (key2406, 4), (key2480, 4), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, -2), (key2563, -2), (key2440, -2), (key2522, -2), (key2437, -2), (key2503, -2), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15722 : Integer.Sparse Key := [(key2543, 4), (key2480, 4), (key2406, 4), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2563, -2), (key2554, -2), (key2522, -2), (key2440, -2), (key2503, -2), (key2437, -2), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15723 : Integer.Sparse Key := [(key2409, 4), (key2482, 4), (key2482, 4), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2440, -2), (key2440, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15724 : Integer.Sparse Key := [(key2482, 4), (key2409, 4), (key2482, 4), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15725 : Integer.Sparse Key := [(key2482, 4), (key2482, 4), (key2409, 4), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2522, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2440, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15726 : Integer.Sparse Key := [(key2406, 4), (key2480, 4), (key2543, 4), (key2437, -2), (key2440, -2), (key2503, -2), (key2554, -2), (key2522, -2), (key2563, -2), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15727 : Integer.Sparse Key := [(key2406, 4), (key2543, 4), (key2480, 4), (key2440, -2), (key2437, -2), (key2554, -2), (key2503, -2), (key2563, -2), (key2522, -2), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15728 : Integer.Sparse Key := [(key2480, 4), (key2406, 4), (key2543, 4), (key2503, -2), (key2522, -2), (key2437, -2), (key2563, -2), (key2440, -2), (key2554, -2), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15729 : Integer.Sparse Key := [(key2480, 4), (key2543, 4), (key2406, 4), (key2522, -2), (key2503, -2), (key2563, -2), (key2437, -2), (key2554, -2), (key2440, -2), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15730 : Integer.Sparse Key := [(key2543, 4), (key2406, 4), (key2480, 4), (key2554, -2), (key2563, -2), (key2440, -2), (key2522, -2), (key2437, -2), (key2503, -2), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15731 : Integer.Sparse Key := [(key2543, 4), (key2480, 4), (key2406, 4), (key2563, -2), (key2554, -2), (key2522, -2), (key2440, -2), (key2503, -2), (key2437, -2), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15732 : Integer.Sparse Key := [(key2409, 4), (key2482, 4), (key2482, 4), (key2440, -2), (key2440, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15733 : Integer.Sparse Key := [(key2482, 4), (key2409, 4), (key2482, 4), (key2506, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15734 : Integer.Sparse Key := [(key2482, 4), (key2482, 4), (key2409, 4), (key2522, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2440, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15735 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key1013, -2), (key999, 6), (key1107, -2), (key1112, -2), (key1121, -2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1034, -2), (key1112, -2), (key1191, -2), (key1148, 6), (key1069, -2), (key1148, -2), (key1210, -2)]

def rawRow15736 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key1013, -2), (key999, 6), (key1112, -2), (key1107, -2), (key1121, -2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1034, -2), (key1191, -2), (key1112, -2), (key1148, 6), (key1069, -2), (key1210, -2), (key1148, -2)]

def rawRow15737 : Integer.Sparse Key := [(key994, -2), (key1013, -2), (key999, -2), (key999, 6), (key1107, -2), (key1121, -2), (key1112, -2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1112, -2), (key1034, -2), (key1191, -2), (key1148, 6), (key1148, -2), (key1069, -2), (key1210, -2)]

def rawRow15738 : Integer.Sparse Key := [(key1013, -2), (key994, -2), (key999, -2), (key999, 6), (key1121, -2), (key1107, -2), (key1112, -2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1112, -2), (key1191, -2), (key1034, -2), (key1148, 6), (key1148, -2), (key1210, -2), (key1069, -2)]

def rawRow15739 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key994, -2), (key999, 6), (key1112, -2), (key1121, -2), (key1107, -2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1191, -2), (key1034, -2), (key1112, -2), (key1148, 6), (key1210, -2), (key1069, -2), (key1148, -2)]

def rawRow15740 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key994, -2), (key999, 6), (key1121, -2), (key1112, -2), (key1107, -2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1191, -2), (key1112, -2), (key1034, -2), (key1148, 6), (key1210, -2), (key1148, -2), (key1069, -2)]

def rawRow15741 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key1013, -2), (key994, 6), (key1191, -2), (key1191, -2), (key1197, -2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1210, 6), (key1069, -2), (key1148, -2), (key1148, -2)]

def rawRow15742 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key999, -2), (key994, 6), (key1191, -2), (key1197, -2), (key1191, -2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1210, 6), (key1148, -2), (key1069, -2), (key1148, -2)]

def rawRow15743 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key999, -2), (key994, 6), (key1197, -2), (key1191, -2), (key1191, -2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1210, 6), (key1148, -2), (key1148, -2), (key1069, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15744 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1121, -2), (key1148, 6), (key994, -2), (key999, -2), (key1013, -2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1069, -2), (key1148, -2), (key1210, -2), (key999, 6), (key1034, -2), (key1112, -2), (key1191, -2)]

def rawRow15745 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1121, -2), (key1148, 6), (key999, -2), (key994, -2), (key1013, -2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1069, -2), (key1210, -2), (key1148, -2), (key999, 6), (key1034, -2), (key1191, -2), (key1112, -2)]

def rawRow15746 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1112, -2), (key1148, 6), (key994, -2), (key1013, -2), (key999, -2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1148, -2), (key1069, -2), (key1210, -2), (key999, 6), (key1112, -2), (key1034, -2), (key1191, -2)]

def rawRow15747 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1112, -2), (key1148, 6), (key1013, -2), (key994, -2), (key999, -2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1148, -2), (key1210, -2), (key1069, -2), (key999, 6), (key1112, -2), (key1191, -2), (key1034, -2)]

def rawRow15748 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1107, -2), (key1148, 6), (key999, -2), (key1013, -2), (key994, -2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1210, -2), (key1069, -2), (key1148, -2), (key999, 6), (key1191, -2), (key1034, -2), (key1112, -2)]

def rawRow15749 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1107, -2), (key1148, 6), (key1013, -2), (key999, -2), (key994, -2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1210, -2), (key1148, -2), (key1069, -2), (key999, 6), (key1191, -2), (key1112, -2), (key1034, -2)]

def rawRow15750 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1197, -2), (key1210, 6), (key999, -2), (key999, -2), (key1013, -2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1069, -2), (key1148, -2), (key1148, -2), (key994, 6), (key1029, -2), (key1107, -2), (key1107, -2)]

def rawRow15751 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1191, -2), (key1210, 6), (key999, -2), (key1013, -2), (key999, -2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1148, -2), (key1069, -2), (key1148, -2), (key994, 6), (key1107, -2), (key1029, -2), (key1107, -2)]

def rawRow15752 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1191, -2), (key1210, 6), (key1013, -2), (key999, -2), (key999, -2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1148, -2), (key1148, -2), (key1069, -2), (key994, 6), (key1107, -2), (key1107, -2), (key1029, -2)]

def rawRow15753 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2387, -2), (key2375, 6), (key2465, -2), (key2469, -2), (key2477, -2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2403, -2), (key2469, -2), (key2536, -2), (key2500, 6), (key2434, -2), (key2500, -2), (key2552, -2)]

def rawRow15754 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2387, -2), (key2375, 6), (key2469, -2), (key2465, -2), (key2477, -2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2403, -2), (key2536, -2), (key2469, -2), (key2500, 6), (key2434, -2), (key2552, -2), (key2500, -2)]

def rawRow15755 : Integer.Sparse Key := [(key2371, -2), (key2387, -2), (key2375, -2), (key2375, 6), (key2465, -2), (key2477, -2), (key2469, -2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2469, -2), (key2403, -2), (key2536, -2), (key2500, 6), (key2500, -2), (key2434, -2), (key2552, -2)]

def rawRow15756 : Integer.Sparse Key := [(key2387, -2), (key2371, -2), (key2375, -2), (key2375, 6), (key2477, -2), (key2465, -2), (key2469, -2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2469, -2), (key2536, -2), (key2403, -2), (key2500, 6), (key2500, -2), (key2552, -2), (key2434, -2)]

def rawRow15757 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2371, -2), (key2375, 6), (key2469, -2), (key2477, -2), (key2465, -2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2536, -2), (key2403, -2), (key2469, -2), (key2500, 6), (key2552, -2), (key2434, -2), (key2500, -2)]

def rawRow15758 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2371, -2), (key2375, 6), (key2477, -2), (key2469, -2), (key2465, -2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2536, -2), (key2469, -2), (key2403, -2), (key2500, 6), (key2552, -2), (key2500, -2), (key2434, -2)]

def rawRow15759 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2387, -2), (key2371, 6), (key2536, -2), (key2536, -2), (key2541, -2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2399, -2), (key2465, -2), (key2465, -2), (key2552, 6), (key2434, -2), (key2500, -2), (key2500, -2)]

def rawRow15760 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2375, -2), (key2371, 6), (key2536, -2), (key2541, -2), (key2536, -2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2465, -2), (key2399, -2), (key2465, -2), (key2552, 6), (key2500, -2), (key2434, -2), (key2500, -2)]

def rawRow15761 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2375, -2), (key2371, 6), (key2541, -2), (key2536, -2), (key2536, -2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2465, -2), (key2465, -2), (key2399, -2), (key2552, 6), (key2500, -2), (key2500, -2), (key2434, -2)]

def rawRow15762 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2477, -2), (key2500, 6), (key2371, -2), (key2375, -2), (key2387, -2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2434, -2), (key2500, -2), (key2552, -2), (key2375, 6), (key2403, -2), (key2469, -2), (key2536, -2)]

def rawRow15763 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2477, -2), (key2500, 6), (key2375, -2), (key2371, -2), (key2387, -2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2434, -2), (key2552, -2), (key2500, -2), (key2375, 6), (key2403, -2), (key2536, -2), (key2469, -2)]

def rawRow15764 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2469, -2), (key2500, 6), (key2371, -2), (key2387, -2), (key2375, -2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2500, -2), (key2434, -2), (key2552, -2), (key2375, 6), (key2469, -2), (key2403, -2), (key2536, -2)]

def rawRow15765 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2469, -2), (key2500, 6), (key2387, -2), (key2371, -2), (key2375, -2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2500, -2), (key2552, -2), (key2434, -2), (key2375, 6), (key2469, -2), (key2536, -2), (key2403, -2)]

def rawRow15766 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2465, -2), (key2500, 6), (key2375, -2), (key2387, -2), (key2371, -2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2552, -2), (key2434, -2), (key2500, -2), (key2375, 6), (key2536, -2), (key2403, -2), (key2469, -2)]

def rawRow15767 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2465, -2), (key2500, 6), (key2387, -2), (key2375, -2), (key2371, -2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2552, -2), (key2500, -2), (key2434, -2), (key2375, 6), (key2536, -2), (key2469, -2), (key2403, -2)]

def rawRow15768 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2541, -2), (key2552, 6), (key2375, -2), (key2375, -2), (key2387, -2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2434, -2), (key2500, -2), (key2500, -2), (key2371, 6), (key2399, -2), (key2465, -2), (key2465, -2)]

def rawRow15769 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2536, -2), (key2552, 6), (key2375, -2), (key2387, -2), (key2375, -2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2500, -2), (key2434, -2), (key2500, -2), (key2371, 6), (key2465, -2), (key2399, -2), (key2465, -2)]

def rawRow15770 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2536, -2), (key2552, 6), (key2387, -2), (key2375, -2), (key2375, -2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2500, -2), (key2500, -2), (key2434, -2), (key2371, 6), (key2465, -2), (key2465, -2), (key2399, -2)]

def rawRow15771 : Integer.Sparse Key := [(key2623, 6), (key2607, -2), (key2623, -2), (key2634, -2), (key2697, 6), (key2662, -2), (key2697, -2), (key2720, -2), (key2800, -2), (key2850, -2), (key2854, -2), (key2777, -2), (key2850, -2), (key2864, -2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

def rawRow15772 : Integer.Sparse Key := [(key2623, 6), (key2607, -2), (key2634, -2), (key2623, -2), (key2697, 6), (key2662, -2), (key2720, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, -2), (key2864, -2), (key2850, -2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

def rawRow15773 : Integer.Sparse Key := [(key2623, 6), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, 6), (key2697, -2), (key2662, -2), (key2720, -2), (key2850, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, -2), (key2864, -2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

def rawRow15774 : Integer.Sparse Key := [(key2623, 6), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, 6), (key2697, -2), (key2720, -2), (key2662, -2), (key2850, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, -2), (key2777, -2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

def rawRow15775 : Integer.Sparse Key := [(key2623, 6), (key2634, -2), (key2607, -2), (key2623, -2), (key2697, 6), (key2720, -2), (key2662, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, -2), (key2777, -2), (key2850, -2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

def rawRow15776 : Integer.Sparse Key := [(key2623, 6), (key2634, -2), (key2623, -2), (key2607, -2), (key2697, 6), (key2720, -2), (key2697, -2), (key2662, -2), (key2854, -2), (key2850, -2), (key2800, -2), (key2864, -2), (key2850, -2), (key2777, -2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

def rawRow15777 : Integer.Sparse Key := [(key2634, 6), (key2607, -2), (key2623, -2), (key2623, -2), (key2720, 6), (key2662, -2), (key2697, -2), (key2697, -2), (key2823, -2), (key2864, -2), (key2864, -2), (key2788, -2), (key2854, -2), (key2854, -2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

def rawRow15778 : Integer.Sparse Key := [(key2634, 6), (key2623, -2), (key2607, -2), (key2623, -2), (key2720, 6), (key2697, -2), (key2662, -2), (key2697, -2), (key2864, -2), (key2823, -2), (key2864, -2), (key2854, -2), (key2788, -2), (key2854, -2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

def rawRow15779 : Integer.Sparse Key := [(key2634, 6), (key2623, -2), (key2623, -2), (key2607, -2), (key2720, 6), (key2697, -2), (key2697, -2), (key2662, -2), (key2864, -2), (key2864, -2), (key2823, -2), (key2854, -2), (key2854, -2), (key2788, -2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

def rawRow15780 : Integer.Sparse Key := [(key2697, 6), (key2800, -2), (key2850, -2), (key2854, -2), (key2623, 6), (key2777, -2), (key2850, -2), (key2864, -2), (key2607, -2), (key2623, -2), (key2634, -2), (key2662, -2), (key2697, -2), (key2720, -2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

def rawRow15781 : Integer.Sparse Key := [(key2697, 6), (key2800, -2), (key2854, -2), (key2850, -2), (key2623, 6), (key2777, -2), (key2864, -2), (key2850, -2), (key2607, -2), (key2634, -2), (key2623, -2), (key2662, -2), (key2720, -2), (key2697, -2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

def rawRow15782 : Integer.Sparse Key := [(key2697, 6), (key2850, -2), (key2800, -2), (key2854, -2), (key2623, 6), (key2850, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, -2), (key2662, -2), (key2720, -2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

def rawRow15783 : Integer.Sparse Key := [(key2697, 6), (key2850, -2), (key2854, -2), (key2800, -2), (key2623, 6), (key2850, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, -2), (key2720, -2), (key2662, -2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

def rawRow15784 : Integer.Sparse Key := [(key2697, 6), (key2854, -2), (key2800, -2), (key2850, -2), (key2623, 6), (key2864, -2), (key2777, -2), (key2850, -2), (key2634, -2), (key2607, -2), (key2623, -2), (key2720, -2), (key2662, -2), (key2697, -2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

def rawRow15785 : Integer.Sparse Key := [(key2697, 6), (key2854, -2), (key2850, -2), (key2800, -2), (key2623, 6), (key2864, -2), (key2850, -2), (key2777, -2), (key2634, -2), (key2623, -2), (key2607, -2), (key2720, -2), (key2697, -2), (key2662, -2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

def rawRow15786 : Integer.Sparse Key := [(key2720, 6), (key2823, -2), (key2864, -2), (key2864, -2), (key2634, 6), (key2788, -2), (key2854, -2), (key2854, -2), (key2607, -2), (key2623, -2), (key2623, -2), (key2662, -2), (key2697, -2), (key2697, -2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

def rawRow15787 : Integer.Sparse Key := [(key2720, 6), (key2864, -2), (key2823, -2), (key2864, -2), (key2634, 6), (key2854, -2), (key2788, -2), (key2854, -2), (key2623, -2), (key2607, -2), (key2623, -2), (key2697, -2), (key2662, -2), (key2697, -2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

def rawRow15788 : Integer.Sparse Key := [(key2720, 6), (key2864, -2), (key2864, -2), (key2823, -2), (key2634, 6), (key2854, -2), (key2854, -2), (key2788, -2), (key2623, -2), (key2623, -2), (key2607, -2), (key2697, -2), (key2697, -2), (key2662, -2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

def rawRow15789 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key1012, -2), (key997, 6), (key1106, -2), (key1110, -2), (key1120, -2), (key1028, 2), (key1032, 2), (key1106, 2), (key1189, 2), (key1120, 2), (key1196, 2), (key1032, -2), (key1110, -2), (key1189, -2), (key1147, 6), (key1068, -2), (key1147, -2), (key1209, -2)]

def rawRow15790 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key1012, -2), (key997, 6), (key1110, -2), (key1106, -2), (key1120, -2), (key1032, 2), (key1028, 2), (key1189, 2), (key1106, 2), (key1196, 2), (key1120, 2), (key1032, -2), (key1189, -2), (key1110, -2), (key1147, 6), (key1068, -2), (key1209, -2), (key1147, -2)]

def rawRow15791 : Integer.Sparse Key := [(key993, -2), (key1012, -2), (key997, -2), (key997, 6), (key1106, -2), (key1120, -2), (key1110, -2), (key1106, 2), (key1120, 2), (key1028, 2), (key1196, 2), (key1032, 2), (key1189, 2), (key1110, -2), (key1032, -2), (key1189, -2), (key1147, 6), (key1147, -2), (key1068, -2), (key1209, -2)]

def rawRow15792 : Integer.Sparse Key := [(key1012, -2), (key993, -2), (key997, -2), (key997, 6), (key1120, -2), (key1106, -2), (key1110, -2), (key1120, 2), (key1106, 2), (key1196, 2), (key1028, 2), (key1189, 2), (key1032, 2), (key1110, -2), (key1189, -2), (key1032, -2), (key1147, 6), (key1147, -2), (key1209, -2), (key1068, -2)]

def rawRow15793 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key993, -2), (key997, 6), (key1110, -2), (key1120, -2), (key1106, -2), (key1189, 2), (key1196, 2), (key1032, 2), (key1120, 2), (key1028, 2), (key1106, 2), (key1189, -2), (key1032, -2), (key1110, -2), (key1147, 6), (key1209, -2), (key1068, -2), (key1147, -2)]

def rawRow15794 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key993, -2), (key997, 6), (key1120, -2), (key1110, -2), (key1106, -2), (key1196, 2), (key1189, 2), (key1120, 2), (key1032, 2), (key1106, 2), (key1028, 2), (key1189, -2), (key1110, -2), (key1032, -2), (key1147, 6), (key1209, -2), (key1147, -2), (key1068, -2)]

def rawRow15795 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key1012, -2), (key993, 6), (key1189, -2), (key1189, -2), (key1196, -2), (key1032, 2), (key1032, 2), (key1110, 2), (key1110, 2), (key1120, 2), (key1120, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1209, 6), (key1068, -2), (key1147, -2), (key1147, -2)]

def rawRow15796 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key997, -2), (key993, 6), (key1189, -2), (key1196, -2), (key1189, -2), (key1110, 2), (key1120, 2), (key1032, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1209, 6), (key1147, -2), (key1068, -2), (key1147, -2)]

def rawRow15797 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key997, -2), (key993, 6), (key1196, -2), (key1189, -2), (key1189, -2), (key1120, 2), (key1110, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1032, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1209, 6), (key1147, -2), (key1147, -2), (key1068, -2)]

def rawRow15798 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1120, -2), (key1147, 6), (key993, -2), (key997, -2), (key1012, -2), (key1028, 2), (key1032, 2), (key1106, 2), (key1189, 2), (key1120, 2), (key1196, 2), (key1068, -2), (key1147, -2), (key1209, -2), (key997, 6), (key1032, -2), (key1110, -2), (key1189, -2)]

def rawRow15799 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1120, -2), (key1147, 6), (key997, -2), (key993, -2), (key1012, -2), (key1032, 2), (key1028, 2), (key1189, 2), (key1106, 2), (key1196, 2), (key1120, 2), (key1068, -2), (key1209, -2), (key1147, -2), (key997, 6), (key1032, -2), (key1189, -2), (key1110, -2)]

def rawRow15800 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1110, -2), (key1147, 6), (key993, -2), (key1012, -2), (key997, -2), (key1106, 2), (key1120, 2), (key1028, 2), (key1196, 2), (key1032, 2), (key1189, 2), (key1147, -2), (key1068, -2), (key1209, -2), (key997, 6), (key1110, -2), (key1032, -2), (key1189, -2)]

def rawRow15801 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1110, -2), (key1147, 6), (key1012, -2), (key993, -2), (key997, -2), (key1120, 2), (key1106, 2), (key1196, 2), (key1028, 2), (key1189, 2), (key1032, 2), (key1147, -2), (key1209, -2), (key1068, -2), (key997, 6), (key1110, -2), (key1189, -2), (key1032, -2)]

def rawRow15802 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1106, -2), (key1147, 6), (key997, -2), (key1012, -2), (key993, -2), (key1189, 2), (key1196, 2), (key1032, 2), (key1120, 2), (key1028, 2), (key1106, 2), (key1209, -2), (key1068, -2), (key1147, -2), (key997, 6), (key1189, -2), (key1032, -2), (key1110, -2)]

def rawRow15803 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1106, -2), (key1147, 6), (key1012, -2), (key997, -2), (key993, -2), (key1196, 2), (key1189, 2), (key1120, 2), (key1032, 2), (key1106, 2), (key1028, 2), (key1209, -2), (key1147, -2), (key1068, -2), (key997, 6), (key1189, -2), (key1110, -2), (key1032, -2)]

def rawRow15804 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1196, -2), (key1209, 6), (key997, -2), (key997, -2), (key1012, -2), (key1032, 2), (key1032, 2), (key1110, 2), (key1110, 2), (key1120, 2), (key1120, 2), (key1068, -2), (key1147, -2), (key1147, -2), (key993, 6), (key1028, -2), (key1106, -2), (key1106, -2)]

def rawRow15805 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1189, -2), (key1209, 6), (key997, -2), (key1012, -2), (key997, -2), (key1110, 2), (key1120, 2), (key1032, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1147, -2), (key1068, -2), (key1147, -2), (key993, 6), (key1106, -2), (key1028, -2), (key1106, -2)]

def rawRow15806 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1189, -2), (key1209, 6), (key1012, -2), (key997, -2), (key997, -2), (key1120, 2), (key1110, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1032, 2), (key1147, -2), (key1147, -2), (key1068, -2), (key993, 6), (key1106, -2), (key1106, -2), (key1028, -2)]

def rawRow15807 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1200, 4), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1073, -2), (key1077, -2), (key1152, -2), (key1213, -2), (key1172, -2), (key1223, -2), (key1077, 4), (key1156, 4), (key1213, 4)]

def rawRow15808 : Integer.Sparse Key := [(key1038, 4), (key1200, 4), (key1125, 4), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, -2), (key1073, -2), (key1213, -2), (key1152, -2), (key1223, -2), (key1172, -2), (key1077, 4), (key1213, 4), (key1156, 4)]

def rawRow15809 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1200, 4), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1152, -2), (key1172, -2), (key1073, -2), (key1223, -2), (key1077, -2), (key1213, -2), (key1156, 4), (key1077, 4), (key1213, 4)]

def rawRow15810 : Integer.Sparse Key := [(key1125, 4), (key1200, 4), (key1038, 4), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1172, -2), (key1152, -2), (key1223, -2), (key1073, -2), (key1213, -2), (key1077, -2), (key1156, 4), (key1213, 4), (key1077, 4)]

def rawRow15811 : Integer.Sparse Key := [(key1200, 4), (key1038, 4), (key1125, 4), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, -2), (key1223, -2), (key1077, -2), (key1172, -2), (key1073, -2), (key1152, -2), (key1213, 4), (key1077, 4), (key1156, 4)]

def rawRow15812 : Integer.Sparse Key := [(key1200, 4), (key1125, 4), (key1038, 4), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1223, -2), (key1213, -2), (key1172, -2), (key1077, -2), (key1152, -2), (key1073, -2), (key1213, 4), (key1156, 4), (key1077, 4)]

def rawRow15813 : Integer.Sparse Key := [(key1042, 4), (key1128, 4), (key1128, 4), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1077, -2), (key1077, -2), (key1156, -2), (key1156, -2), (key1172, -2), (key1172, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15814 : Integer.Sparse Key := [(key1128, 4), (key1042, 4), (key1128, 4), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15815 : Integer.Sparse Key := [(key1128, 4), (key1128, 4), (key1042, 4), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1172, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1077, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15816 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1200, 4), (key1073, -2), (key1077, -2), (key1152, -2), (key1213, -2), (key1172, -2), (key1223, -2), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1077, 4), (key1156, 4), (key1213, 4)]

def rawRow15817 : Integer.Sparse Key := [(key1038, 4), (key1200, 4), (key1125, 4), (key1077, -2), (key1073, -2), (key1213, -2), (key1152, -2), (key1223, -2), (key1172, -2), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, 4), (key1213, 4), (key1156, 4)]

def rawRow15818 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1200, 4), (key1152, -2), (key1172, -2), (key1073, -2), (key1223, -2), (key1077, -2), (key1213, -2), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1156, 4), (key1077, 4), (key1213, 4)]

def rawRow15819 : Integer.Sparse Key := [(key1125, 4), (key1200, 4), (key1038, 4), (key1172, -2), (key1152, -2), (key1223, -2), (key1073, -2), (key1213, -2), (key1077, -2), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1156, 4), (key1213, 4), (key1077, 4)]

def rawRow15820 : Integer.Sparse Key := [(key1200, 4), (key1038, 4), (key1125, 4), (key1213, -2), (key1223, -2), (key1077, -2), (key1172, -2), (key1073, -2), (key1152, -2), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, 4), (key1077, 4), (key1156, 4)]

def rawRow15821 : Integer.Sparse Key := [(key1200, 4), (key1125, 4), (key1038, 4), (key1223, -2), (key1213, -2), (key1172, -2), (key1077, -2), (key1152, -2), (key1073, -2), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1213, 4), (key1156, 4), (key1077, 4)]

def rawRow15822 : Integer.Sparse Key := [(key1042, 4), (key1128, 4), (key1128, 4), (key1077, -2), (key1077, -2), (key1156, -2), (key1156, -2), (key1172, -2), (key1172, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15823 : Integer.Sparse Key := [(key1128, 4), (key1042, 4), (key1128, 4), (key1156, -2), (key1172, -2), (key1077, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15824 : Integer.Sparse Key := [(key1128, 4), (key1128, 4), (key1042, 4), (key1172, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1077, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15825 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2668, 2), (key2783, 2), (key2937, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2), (key2703, -1), (key2736, -1), (key2806, -1), (key2949, -1), (key2894, -1), (key2973, -1), (key2723, 2), (key2867, 2), (key2982, 2), (key2723, -1), (key2746, -1), (key2826, -1), (key2959, -1), (key2903, -1), (key2982, -1)]

def rawRow15826 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2668, 2), (key2937, 2), (key2783, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2), (key2736, -1), (key2703, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2894, -1), (key2723, 2), (key2982, 2), (key2867, 2), (key2746, -1), (key2723, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2903, -1)]

def rawRow15827 : Integer.Sparse Key := [(key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2783, 2), (key2668, 2), (key2937, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2), (key2806, -1), (key2894, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2949, -1), (key2867, 2), (key2723, 2), (key2982, 2), (key2826, -1), (key2903, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2959, -1)]

def rawRow15828 : Integer.Sparse Key := [(key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2783, 2), (key2937, 2), (key2668, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2), (key2894, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2949, -1), (key2736, -1), (key2867, 2), (key2982, 2), (key2723, 2), (key2903, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2959, -1), (key2746, -1)]

def rawRow15829 : Integer.Sparse Key := [(key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2937, 2), (key2668, 2), (key2783, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2), (key2949, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2703, -1), (key2806, -1), (key2982, 2), (key2723, 2), (key2867, 2), (key2959, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2723, -1), (key2826, -1)]

def rawRow15830 : Integer.Sparse Key := [(key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2937, 2), (key2783, 2), (key2668, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2), (key2973, -1), (key2949, -1), (key2894, -1), (key2736, -1), (key2806, -1), (key2703, -1), (key2982, 2), (key2867, 2), (key2723, 2), (key2982, -1), (key2959, -1), (key2903, -1), (key2746, -1), (key2826, -1), (key2723, -1)]

def rawRow15831 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1)]

def rawRow15832 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1)]

def rawRow15833 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1)]

def rawRow15834 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2723, 2), (key2867, 2), (key2982, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2), (key2723, -1), (key2746, -1), (key2826, -1), (key2959, -1), (key2903, -1), (key2982, -1), (key2668, 2), (key2783, 2), (key2937, 2), (key2703, -1), (key2736, -1), (key2806, -1), (key2949, -1), (key2894, -1), (key2973, -1)]

def rawRow15835 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2723, 2), (key2982, 2), (key2867, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2), (key2746, -1), (key2723, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2903, -1), (key2668, 2), (key2937, 2), (key2783, 2), (key2736, -1), (key2703, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2894, -1)]

def rawRow15836 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2867, 2), (key2723, 2), (key2982, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2), (key2826, -1), (key2903, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2959, -1), (key2783, 2), (key2668, 2), (key2937, 2), (key2806, -1), (key2894, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2949, -1)]

def rawRow15837 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2867, 2), (key2982, 2), (key2723, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2), (key2903, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2959, -1), (key2746, -1), (key2783, 2), (key2937, 2), (key2668, 2), (key2894, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2949, -1), (key2736, -1)]

def rawRow15838 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2982, 2), (key2723, 2), (key2867, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2), (key2959, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2723, -1), (key2826, -1), (key2937, 2), (key2668, 2), (key2783, 2), (key2949, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2703, -1), (key2806, -1)]

def rawRow15839 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2982, 2), (key2867, 2), (key2723, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2), (key2982, -1), (key2959, -1), (key2903, -1), (key2746, -1), (key2826, -1), (key2723, -1), (key2937, 2), (key2783, 2), (key2668, 2), (key2973, -1), (key2949, -1), (key2894, -1), (key2736, -1), (key2806, -1), (key2703, -1)]

def rawRow15840 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1)]

def rawRow15841 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1)]

def rawRow15842 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1)]

def rawRow15843 : Integer.Sparse Key := [(key2678, 4), (key2709, 4), (key2713, 4), (key2678, -4), (key2687, -4), (key2713, -4), (key2812, -4), (key2816, -4), (key2862, -4), (key2816, 12)]

def rawRow15844 : Integer.Sparse Key := [(key2678, 4), (key2713, 4), (key2709, 4), (key2687, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2812, -4), (key2862, -4), (key2816, 12)]

def rawRow15845 : Integer.Sparse Key := [(key2709, 4), (key2678, 4), (key2713, 4), (key2678, -4), (key2713, -4), (key2687, -4), (key2812, -4), (key2862, -4), (key2816, -4), (key2816, 12)]

def rawRow15846 : Integer.Sparse Key := [(key2709, 4), (key2713, 4), (key2678, 4), (key2713, -4), (key2678, -4), (key2687, -4), (key2862, -4), (key2812, -4), (key2816, -4), (key2816, 12)]

def rawRow15847 : Integer.Sparse Key := [(key2713, 4), (key2678, 4), (key2709, 4), (key2687, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2862, -4), (key2812, -4), (key2816, 12)]

def rawRow15848 : Integer.Sparse Key := [(key2713, 4), (key2709, 4), (key2678, 4), (key2713, -4), (key2687, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2812, -4), (key2816, 12)]

def rawRow15849 : Integer.Sparse Key := [(key2687, 4), (key2713, 4), (key2713, 4), (key2678, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2816, -4), (key2862, -4), (key2812, 12)]

def rawRow15850 : Integer.Sparse Key := [(key2713, 4), (key2687, 4), (key2713, 4), (key2678, -4), (key2709, -4), (key2678, -4), (key2816, -4), (key2862, -4), (key2816, -4), (key2812, 12)]

def rawRow15851 : Integer.Sparse Key := [(key2713, 4), (key2713, 4), (key2687, 4), (key2709, -4), (key2678, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2816, -4), (key2812, 12)]

def rawRow15852 : Integer.Sparse Key := [(key2678, 4), (key2709, 4), (key2713, 4), (key2812, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2687, -4), (key2713, -4), (key2816, 12)]

def rawRow15853 : Integer.Sparse Key := [(key2678, 4), (key2713, 4), (key2709, 4), (key2816, -4), (key2812, -4), (key2862, -4), (key2687, -4), (key2678, -4), (key2713, -4), (key2816, 12)]

def rawRow15854 : Integer.Sparse Key := [(key2709, 4), (key2678, 4), (key2713, 4), (key2812, -4), (key2862, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2687, -4), (key2816, 12)]

def rawRow15855 : Integer.Sparse Key := [(key2709, 4), (key2713, 4), (key2678, 4), (key2862, -4), (key2812, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2687, -4), (key2816, 12)]

def rawRow15856 : Integer.Sparse Key := [(key2713, 4), (key2678, 4), (key2709, 4), (key2816, -4), (key2862, -4), (key2812, -4), (key2687, -4), (key2713, -4), (key2678, -4), (key2816, 12)]

def rawRow15857 : Integer.Sparse Key := [(key2713, 4), (key2709, 4), (key2678, 4), (key2862, -4), (key2816, -4), (key2812, -4), (key2713, -4), (key2687, -4), (key2678, -4), (key2816, 12)]

def rawRow15858 : Integer.Sparse Key := [(key2687, 4), (key2713, 4), (key2713, 4), (key2816, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2678, -4), (key2709, -4), (key2812, 12)]

def rawRow15859 : Integer.Sparse Key := [(key2713, 4), (key2687, 4), (key2713, 4), (key2816, -4), (key2862, -4), (key2816, -4), (key2678, -4), (key2709, -4), (key2678, -4), (key2812, 12)]

def rawRow15860 : Integer.Sparse Key := [(key2713, 4), (key2713, 4), (key2687, 4), (key2862, -4), (key2816, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2678, -4), (key2812, 12)]

def rawRow15861 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2373, 6), (key2839, -2), (key2842, -2), (key2886, -2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2765, -2), (key2842, -2), (key2874, -2), (key2965, 6), (key2928, -2), (key2965, -2), (key2987, -2)]

def rawRow15862 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2386, -2), (key2373, 6), (key2842, -2), (key2839, -2), (key2886, -2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2765, -2), (key2874, -2), (key2842, -2), (key2965, 6), (key2928, -2), (key2987, -2), (key2965, -2)]

def rawRow15863 : Integer.Sparse Key := [(key2370, -2), (key2386, -2), (key2373, -2), (key2373, 6), (key2839, -2), (key2886, -2), (key2842, -2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2842, -2), (key2765, -2), (key2874, -2), (key2965, 6), (key2965, -2), (key2928, -2), (key2987, -2)]

def rawRow15864 : Integer.Sparse Key := [(key2386, -2), (key2370, -2), (key2373, -2), (key2373, 6), (key2886, -2), (key2839, -2), (key2842, -2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2842, -2), (key2874, -2), (key2765, -2), (key2965, 6), (key2965, -2), (key2987, -2), (key2928, -2)]

def rawRow15865 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2370, -2), (key2373, 6), (key2842, -2), (key2886, -2), (key2839, -2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2874, -2), (key2765, -2), (key2842, -2), (key2965, 6), (key2987, -2), (key2928, -2), (key2965, -2)]

def rawRow15866 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2370, -2), (key2373, 6), (key2886, -2), (key2842, -2), (key2839, -2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2874, -2), (key2842, -2), (key2765, -2), (key2965, 6), (key2987, -2), (key2965, -2), (key2928, -2)]

def rawRow15867 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2386, -2), (key2370, 6), (key2874, -2), (key2874, -2), (key2908, -2), (key2765, 2), (key2765, 2), (key2842, 2), (key2842, 2), (key2886, 2), (key2886, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key2987, 6), (key2928, -2), (key2965, -2), (key2965, -2)]

def rawRow15868 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2373, -2), (key2370, 6), (key2874, -2), (key2908, -2), (key2874, -2), (key2842, 2), (key2886, 2), (key2765, 2), (key2886, 2), (key2765, 2), (key2842, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key2987, 6), (key2965, -2), (key2928, -2), (key2965, -2)]

def rawRow15869 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2373, -2), (key2370, 6), (key2908, -2), (key2874, -2), (key2874, -2), (key2886, 2), (key2842, 2), (key2886, 2), (key2765, 2), (key2842, 2), (key2765, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key2987, 6), (key2965, -2), (key2965, -2), (key2928, -2)]

def rawRow15870 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2370, -2), (key2373, -2), (key2386, -2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2), (key2586, 6), (key2765, -2), (key2842, -2), (key2874, -2)]

def rawRow15871 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2476, -2), (key2499, 6), (key2373, -2), (key2370, -2), (key2386, -2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2928, -2), (key2987, -2), (key2965, -2), (key2586, 6), (key2765, -2), (key2874, -2), (key2842, -2)]

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

def rawRow15872 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2467, -2), (key2499, 6), (key2370, -2), (key2386, -2), (key2373, -2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2965, -2), (key2928, -2), (key2987, -2), (key2586, 6), (key2842, -2), (key2765, -2), (key2874, -2)]

def rawRow15873 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2467, -2), (key2499, 6), (key2386, -2), (key2370, -2), (key2373, -2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2965, -2), (key2987, -2), (key2928, -2), (key2586, 6), (key2842, -2), (key2874, -2), (key2765, -2)]

def rawRow15874 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2464, -2), (key2499, 6), (key2373, -2), (key2386, -2), (key2370, -2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2987, -2), (key2928, -2), (key2965, -2), (key2586, 6), (key2874, -2), (key2765, -2), (key2842, -2)]

def rawRow15875 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2464, -2), (key2499, 6), (key2386, -2), (key2373, -2), (key2370, -2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2987, -2), (key2965, -2), (key2928, -2), (key2586, 6), (key2874, -2), (key2842, -2), (key2765, -2)]

def rawRow15876 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2540, -2), (key2551, 6), (key2373, -2), (key2373, -2), (key2386, -2), (key2401, 2), (key2401, 2), (key2467, 2), (key2467, 2), (key2476, 2), (key2476, 2), (key2433, -2), (key2499, -2), (key2499, -2), (key2370, 6), (key2762, -2), (key2839, -2), (key2839, -2)]

def rawRow15877 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2534, -2), (key2551, 6), (key2373, -2), (key2386, -2), (key2373, -2), (key2467, 2), (key2476, 2), (key2401, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2499, -2), (key2433, -2), (key2499, -2), (key2370, 6), (key2839, -2), (key2762, -2), (key2839, -2)]

def rawRow15878 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2534, -2), (key2551, 6), (key2386, -2), (key2373, -2), (key2373, -2), (key2476, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2401, 2), (key2499, -2), (key2499, -2), (key2433, -2), (key2370, 6), (key2839, -2), (key2839, -2), (key2762, -2)]

def rawRow15879 : Integer.Sparse Key := [(key2011, 4), (key2040, 4), (key2048, 4), (key2011, -4), (key2020, -4), (key2048, -4), (key2125, -4), (key2135, -4), (key2220, -4), (key2135, 12)]

def rawRow15880 : Integer.Sparse Key := [(key2011, 4), (key2048, 4), (key2040, 4), (key2020, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2125, -4), (key2220, -4), (key2135, 12)]

def rawRow15881 : Integer.Sparse Key := [(key2040, 4), (key2011, 4), (key2048, 4), (key2011, -4), (key2048, -4), (key2020, -4), (key2125, -4), (key2220, -4), (key2135, -4), (key2135, 12)]

def rawRow15882 : Integer.Sparse Key := [(key2040, 4), (key2048, 4), (key2011, 4), (key2048, -4), (key2011, -4), (key2020, -4), (key2220, -4), (key2125, -4), (key2135, -4), (key2135, 12)]

def rawRow15883 : Integer.Sparse Key := [(key2048, 4), (key2011, 4), (key2040, 4), (key2020, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2220, -4), (key2125, -4), (key2135, 12)]

def rawRow15884 : Integer.Sparse Key := [(key2048, 4), (key2040, 4), (key2011, 4), (key2048, -4), (key2020, -4), (key2011, -4), (key2220, -4), (key2135, -4), (key2125, -4), (key2135, 12)]

def rawRow15885 : Integer.Sparse Key := [(key2020, 4), (key2048, 4), (key2048, 4), (key2011, -4), (key2011, -4), (key2040, -4), (key2135, -4), (key2135, -4), (key2220, -4), (key2125, 12)]

def rawRow15886 : Integer.Sparse Key := [(key2048, 4), (key2020, 4), (key2048, 4), (key2011, -4), (key2040, -4), (key2011, -4), (key2135, -4), (key2220, -4), (key2135, -4), (key2125, 12)]

def rawRow15887 : Integer.Sparse Key := [(key2048, 4), (key2048, 4), (key2020, 4), (key2040, -4), (key2011, -4), (key2011, -4), (key2220, -4), (key2135, -4), (key2135, -4), (key2125, 12)]

def rawRow15888 : Integer.Sparse Key := [(key2011, 4), (key2040, 4), (key2048, 4), (key2125, -4), (key2135, -4), (key2220, -4), (key2011, -4), (key2020, -4), (key2048, -4), (key2135, 12)]

def rawRow15889 : Integer.Sparse Key := [(key2011, 4), (key2048, 4), (key2040, 4), (key2135, -4), (key2125, -4), (key2220, -4), (key2020, -4), (key2011, -4), (key2048, -4), (key2135, 12)]

def rawRow15890 : Integer.Sparse Key := [(key2040, 4), (key2011, 4), (key2048, 4), (key2125, -4), (key2220, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2020, -4), (key2135, 12)]

def rawRow15891 : Integer.Sparse Key := [(key2040, 4), (key2048, 4), (key2011, 4), (key2220, -4), (key2125, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2020, -4), (key2135, 12)]

def rawRow15892 : Integer.Sparse Key := [(key2048, 4), (key2011, 4), (key2040, 4), (key2135, -4), (key2220, -4), (key2125, -4), (key2020, -4), (key2048, -4), (key2011, -4), (key2135, 12)]

def rawRow15893 : Integer.Sparse Key := [(key2048, 4), (key2040, 4), (key2011, 4), (key2220, -4), (key2135, -4), (key2125, -4), (key2048, -4), (key2020, -4), (key2011, -4), (key2135, 12)]

def rawRow15894 : Integer.Sparse Key := [(key2020, 4), (key2048, 4), (key2048, 4), (key2135, -4), (key2135, -4), (key2220, -4), (key2011, -4), (key2011, -4), (key2040, -4), (key2125, 12)]

def rawRow15895 : Integer.Sparse Key := [(key2048, 4), (key2020, 4), (key2048, 4), (key2135, -4), (key2220, -4), (key2135, -4), (key2011, -4), (key2040, -4), (key2011, -4), (key2125, 12)]

def rawRow15896 : Integer.Sparse Key := [(key2048, 4), (key2048, 4), (key2020, 4), (key2220, -4), (key2135, -4), (key2135, -4), (key2040, -4), (key2011, -4), (key2011, -4), (key2125, 12)]

def rawRow15897 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2666, 2), (key2701, 2), (key2722, 2), (key2778, -1), (key2781, -1), (key2851, -1), (key2866, -1), (key2892, -1), (key2902, -1), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, 2), (key2895, 2), (key2902, 2), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2856, -1), (key2866, -1), (key2935, 2), (key2971, 2), (key2981, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, -1)]

def rawRow15898 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2666, 2), (key2722, 2), (key2701, 2), (key2781, -1), (key2778, -1), (key2866, -1), (key2851, -1), (key2902, -1), (key2892, -1), (key2790, 2), (key2778, 2), (key2825, 2), (key2801, 2), (key2902, 2), (key2895, 2), (key2790, -1), (key2781, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2856, -1), (key2935, 2), (key2981, 2), (key2971, 2), (key2941, -1), (key2935, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2974, -1)]

def rawRow15899 : Integer.Sparse Key := [(key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2701, 2), (key2666, 2), (key2722, 2), (key2851, -1), (key2892, -1), (key2778, -1), (key2902, -1), (key2781, -1), (key2866, -1), (key2801, 2), (key2895, 2), (key2778, 2), (key2902, 2), (key2790, 2), (key2825, 2), (key2804, -1), (key2856, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2825, -1), (key2971, 2), (key2935, 2), (key2981, 2), (key2947, -1), (key2974, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2958, -1)]

def rawRow15900 : Integer.Sparse Key := [(key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2701, 2), (key2722, 2), (key2666, 2), (key2892, -1), (key2851, -1), (key2902, -1), (key2778, -1), (key2866, -1), (key2781, -1), (key2895, 2), (key2801, 2), (key2902, 2), (key2778, 2), (key2825, 2), (key2790, 2), (key2856, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2825, -1), (key2790, -1), (key2971, 2), (key2981, 2), (key2935, 2), (key2974, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2958, -1), (key2941, -1)]

def rawRow15901 : Integer.Sparse Key := [(key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2722, 2), (key2666, 2), (key2701, 2), (key2866, -1), (key2902, -1), (key2781, -1), (key2892, -1), (key2778, -1), (key2851, -1), (key2825, 2), (key2902, 2), (key2790, 2), (key2895, 2), (key2778, 2), (key2801, 2), (key2825, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2781, -1), (key2804, -1), (key2981, 2), (key2935, 2), (key2971, 2), (key2958, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2935, -1), (key2947, -1)]

def rawRow15902 : Integer.Sparse Key := [(key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2722, 2), (key2701, 2), (key2666, 2), (key2902, -1), (key2866, -1), (key2892, -1), (key2781, -1), (key2851, -1), (key2778, -1), (key2902, 2), (key2825, 2), (key2895, 2), (key2790, 2), (key2801, 2), (key2778, 2), (key2866, -1), (key2825, -1), (key2856, -1), (key2790, -1), (key2804, -1), (key2781, -1), (key2981, 2), (key2971, 2), (key2935, 2), (key2981, -1), (key2958, -1), (key2974, -1), (key2941, -1), (key2947, -1), (key2935, -1)]

def rawRow15903 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2734, -1), (key2734, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2895, -1), (key2895, -1), (key2781, 2), (key2781, 2), (key2804, 2), (key2804, 2), (key2892, 2), (key2892, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1), (key2941, 2), (key2974, 2), (key2974, 2), (key2935, -1), (key2935, -1), (key2947, -1), (key2947, -1), (key2971, -1), (key2971, -1)]

def rawRow15904 : Integer.Sparse Key := [(key2701, -1), (key2734, -1), (key2666, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2856, -1), (key2895, -1), (key2790, -1), (key2895, -1), (key2790, -1), (key2856, -1), (key2804, 2), (key2892, 2), (key2781, 2), (key2892, 2), (key2781, 2), (key2804, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2974, 2), (key2941, 2), (key2974, 2), (key2947, -1), (key2971, -1), (key2935, -1), (key2971, -1), (key2935, -1), (key2947, -1)]

def rawRow15905 : Integer.Sparse Key := [(key2734, -1), (key2701, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2895, -1), (key2856, -1), (key2895, -1), (key2790, -1), (key2856, -1), (key2790, -1), (key2892, 2), (key2804, 2), (key2892, 2), (key2781, 2), (key2804, 2), (key2781, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1), (key2974, 2), (key2974, 2), (key2941, 2), (key2971, -1), (key2947, -1), (key2971, -1), (key2935, -1), (key2947, -1), (key2935, -1)]

def rawRow15906 : Integer.Sparse Key := [(key2698, -1), (key2701, -1), (key2851, -1), (key2971, -1), (key2856, -1), (key2974, -1), (key2722, 2), (key2866, 2), (key2981, 2), (key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, 2), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, -1), (key2666, 2), (key2701, 2), (key2722, 2), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2856, -1), (key2866, -1)]

def rawRow15907 : Integer.Sparse Key := [(key2701, -1), (key2698, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2856, -1), (key2722, 2), (key2981, 2), (key2866, 2), (key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2790, 2), (key2778, 2), (key2825, 2), (key2801, 2), (key2902, 2), (key2895, 2), (key2941, -1), (key2935, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2974, -1), (key2666, 2), (key2722, 2), (key2701, 2), (key2790, -1), (key2781, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2856, -1)]

def rawRow15908 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2866, 2), (key2722, 2), (key2981, 2), (key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2801, 2), (key2895, 2), (key2778, 2), (key2902, 2), (key2790, 2), (key2825, 2), (key2947, -1), (key2974, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2958, -1), (key2701, 2), (key2666, 2), (key2722, 2), (key2804, -1), (key2856, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2825, -1)]

def rawRow15909 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2971, -1), (key2701, -1), (key2866, 2), (key2981, 2), (key2722, 2), (key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2895, 2), (key2801, 2), (key2902, 2), (key2778, 2), (key2825, 2), (key2790, 2), (key2974, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2958, -1), (key2941, -1), (key2701, 2), (key2722, 2), (key2666, 2), (key2856, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2825, -1), (key2790, -1)]

def rawRow15910 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2981, 2), (key2722, 2), (key2866, 2), (key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2825, 2), (key2902, 2), (key2790, 2), (key2895, 2), (key2778, 2), (key2801, 2), (key2958, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2935, -1), (key2947, -1), (key2722, 2), (key2666, 2), (key2701, 2), (key2825, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2781, -1), (key2804, -1)]

def rawRow15911 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2856, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 2), (key2866, 2), (key2722, 2), (key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2902, 2), (key2825, 2), (key2895, 2), (key2790, 2), (key2801, 2), (key2778, 2), (key2981, -1), (key2958, -1), (key2974, -1), (key2941, -1), (key2947, -1), (key2935, -1), (key2722, 2), (key2701, 2), (key2666, 2), (key2866, -1), (key2825, -1), (key2856, -1), (key2790, -1), (key2804, -1), (key2781, -1)]

def rawRow15912 : Integer.Sparse Key := [(key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1), (key2895, -1), (key2895, -1), (key2745, 2), (key2902, 2), (key2902, 2), (key2666, -1), (key2666, -1), (key2781, -1), (key2781, -1), (key2790, -1), (key2790, -1), (key2701, 2), (key2701, 2), (key2804, 2), (key2804, 2), (key2856, 2), (key2856, 2), (key2722, -1), (key2722, -1), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, -1), (key2851, -1)]

def rawRow15913 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2734, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2902, 2), (key2745, 2), (key2902, 2), (key2781, -1), (key2790, -1), (key2666, -1), (key2790, -1), (key2666, -1), (key2781, -1), (key2804, 2), (key2856, 2), (key2701, 2), (key2856, 2), (key2701, 2), (key2804, 2), (key2825, -1), (key2866, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2825, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, -1), (key2801, -1)]

def rawRow15914 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2734, -1), (key2902, 2), (key2902, 2), (key2745, 2), (key2790, -1), (key2781, -1), (key2790, -1), (key2666, -1), (key2781, -1), (key2666, -1), (key2856, 2), (key2804, 2), (key2856, 2), (key2701, 2), (key2804, 2), (key2701, 2), (key2866, -1), (key2825, -1), (key2866, -1), (key2722, -1), (key2825, -1), (key2722, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, -1), (key2778, -1)]

def rawRow15915 : Integer.Sparse Key := [(key1359, -2), (key1364, -2), (key1374, -2), (key1364, 6), (key1711, -2), (key1716, -2), (key1723, -2), (key1485, 2), (key1490, 2), (key1711, 2), (key1861, 2), (key1723, 2), (key1867, 2), (key1490, -2), (key1716, -2), (key1861, -2), (key1741, 6), (key1513, -2), (key1741, -2), (key1877, -2)]

def rawRow15916 : Integer.Sparse Key := [(key1364, -2), (key1359, -2), (key1374, -2), (key1364, 6), (key1716, -2), (key1711, -2), (key1723, -2), (key1490, 2), (key1485, 2), (key1861, 2), (key1711, 2), (key1867, 2), (key1723, 2), (key1490, -2), (key1861, -2), (key1716, -2), (key1741, 6), (key1513, -2), (key1877, -2), (key1741, -2)]

def rawRow15917 : Integer.Sparse Key := [(key1359, -2), (key1374, -2), (key1364, -2), (key1364, 6), (key1711, -2), (key1723, -2), (key1716, -2), (key1711, 2), (key1723, 2), (key1485, 2), (key1867, 2), (key1490, 2), (key1861, 2), (key1716, -2), (key1490, -2), (key1861, -2), (key1741, 6), (key1741, -2), (key1513, -2), (key1877, -2)]

def rawRow15918 : Integer.Sparse Key := [(key1374, -2), (key1359, -2), (key1364, -2), (key1364, 6), (key1723, -2), (key1711, -2), (key1716, -2), (key1723, 2), (key1711, 2), (key1867, 2), (key1485, 2), (key1861, 2), (key1490, 2), (key1716, -2), (key1861, -2), (key1490, -2), (key1741, 6), (key1741, -2), (key1877, -2), (key1513, -2)]

def rawRow15919 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1359, -2), (key1364, 6), (key1716, -2), (key1723, -2), (key1711, -2), (key1861, 2), (key1867, 2), (key1490, 2), (key1723, 2), (key1485, 2), (key1711, 2), (key1861, -2), (key1490, -2), (key1716, -2), (key1741, 6), (key1877, -2), (key1513, -2), (key1741, -2)]

def rawRow15920 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1359, -2), (key1364, 6), (key1723, -2), (key1716, -2), (key1711, -2), (key1867, 2), (key1861, 2), (key1723, 2), (key1490, 2), (key1711, 2), (key1485, 2), (key1861, -2), (key1716, -2), (key1490, -2), (key1741, 6), (key1877, -2), (key1741, -2), (key1513, -2)]

def rawRow15921 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1374, -2), (key1359, 6), (key1861, -2), (key1861, -2), (key1867, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1485, -2), (key1711, -2), (key1711, -2), (key1877, 6), (key1513, -2), (key1741, -2), (key1741, -2)]

def rawRow15922 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1364, -2), (key1359, 6), (key1861, -2), (key1867, -2), (key1861, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1711, -2), (key1485, -2), (key1711, -2), (key1877, 6), (key1741, -2), (key1513, -2), (key1741, -2)]

def rawRow15923 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1364, -2), (key1359, 6), (key1867, -2), (key1861, -2), (key1861, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1711, -2), (key1711, -2), (key1485, -2), (key1877, 6), (key1741, -2), (key1741, -2), (key1513, -2)]

def rawRow15924 : Integer.Sparse Key := [(key1485, -2), (key1490, -2), (key1513, -2), (key1490, 6), (key1711, -2), (key1716, -2), (key1741, -2), (key1359, 2), (key1364, 2), (key1711, 2), (key1861, 2), (key1741, 2), (key1877, 2), (key1364, -2), (key1716, -2), (key1861, -2), (key1723, 6), (key1374, -2), (key1723, -2), (key1867, -2)]

def rawRow15925 : Integer.Sparse Key := [(key1490, -2), (key1485, -2), (key1513, -2), (key1490, 6), (key1716, -2), (key1711, -2), (key1741, -2), (key1364, 2), (key1359, 2), (key1861, 2), (key1711, 2), (key1877, 2), (key1741, 2), (key1364, -2), (key1861, -2), (key1716, -2), (key1723, 6), (key1374, -2), (key1867, -2), (key1723, -2)]

def rawRow15926 : Integer.Sparse Key := [(key1485, -2), (key1513, -2), (key1490, -2), (key1490, 6), (key1711, -2), (key1741, -2), (key1716, -2), (key1711, 2), (key1741, 2), (key1359, 2), (key1877, 2), (key1364, 2), (key1861, 2), (key1716, -2), (key1364, -2), (key1861, -2), (key1723, 6), (key1723, -2), (key1374, -2), (key1867, -2)]

def rawRow15927 : Integer.Sparse Key := [(key1513, -2), (key1485, -2), (key1490, -2), (key1490, 6), (key1741, -2), (key1711, -2), (key1716, -2), (key1741, 2), (key1711, 2), (key1877, 2), (key1359, 2), (key1861, 2), (key1364, 2), (key1716, -2), (key1861, -2), (key1364, -2), (key1723, 6), (key1723, -2), (key1867, -2), (key1374, -2)]

def rawRow15928 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1485, -2), (key1490, 6), (key1716, -2), (key1741, -2), (key1711, -2), (key1861, 2), (key1877, 2), (key1364, 2), (key1741, 2), (key1359, 2), (key1711, 2), (key1861, -2), (key1364, -2), (key1716, -2), (key1723, 6), (key1867, -2), (key1374, -2), (key1723, -2)]

def rawRow15929 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1485, -2), (key1490, 6), (key1741, -2), (key1716, -2), (key1711, -2), (key1877, 2), (key1861, 2), (key1741, 2), (key1364, 2), (key1711, 2), (key1359, 2), (key1861, -2), (key1716, -2), (key1364, -2), (key1723, 6), (key1867, -2), (key1723, -2), (key1374, -2)]

def rawRow15930 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1513, -2), (key1485, 6), (key1861, -2), (key1861, -2), (key1877, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1359, -2), (key1711, -2), (key1711, -2), (key1867, 6), (key1374, -2), (key1723, -2), (key1723, -2)]

def rawRow15931 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1490, -2), (key1485, 6), (key1861, -2), (key1877, -2), (key1861, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1711, -2), (key1359, -2), (key1711, -2), (key1867, 6), (key1723, -2), (key1374, -2), (key1723, -2)]

def rawRow15932 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1490, -2), (key1485, 6), (key1877, -2), (key1861, -2), (key1861, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1711, -2), (key1711, -2), (key1359, -2), (key1867, 6), (key1723, -2), (key1723, -2), (key1374, -2)]

def rawRow15933 : Integer.Sparse Key := [(key1711, -2), (key1716, -2), (key1723, -2), (key1741, 6), (key1359, -2), (key1364, -2), (key1374, -2), (key1485, 2), (key1490, 2), (key1711, 2), (key1861, 2), (key1723, 2), (key1867, 2), (key1513, -2), (key1741, -2), (key1877, -2), (key1364, 6), (key1490, -2), (key1716, -2), (key1861, -2)]

def rawRow15934 : Integer.Sparse Key := [(key1716, -2), (key1711, -2), (key1723, -2), (key1741, 6), (key1364, -2), (key1359, -2), (key1374, -2), (key1490, 2), (key1485, 2), (key1861, 2), (key1711, 2), (key1867, 2), (key1723, 2), (key1513, -2), (key1877, -2), (key1741, -2), (key1364, 6), (key1490, -2), (key1861, -2), (key1716, -2)]

def rawRow15935 : Integer.Sparse Key := [(key1711, -2), (key1723, -2), (key1716, -2), (key1741, 6), (key1359, -2), (key1374, -2), (key1364, -2), (key1711, 2), (key1723, 2), (key1485, 2), (key1867, 2), (key1490, 2), (key1861, 2), (key1741, -2), (key1513, -2), (key1877, -2), (key1364, 6), (key1716, -2), (key1490, -2), (key1861, -2)]

def rawRow15936 : Integer.Sparse Key := [(key1723, -2), (key1711, -2), (key1716, -2), (key1741, 6), (key1374, -2), (key1359, -2), (key1364, -2), (key1723, 2), (key1711, 2), (key1867, 2), (key1485, 2), (key1861, 2), (key1490, 2), (key1741, -2), (key1877, -2), (key1513, -2), (key1364, 6), (key1716, -2), (key1861, -2), (key1490, -2)]

def rawRow15937 : Integer.Sparse Key := [(key1716, -2), (key1723, -2), (key1711, -2), (key1741, 6), (key1364, -2), (key1374, -2), (key1359, -2), (key1861, 2), (key1867, 2), (key1490, 2), (key1723, 2), (key1485, 2), (key1711, 2), (key1877, -2), (key1513, -2), (key1741, -2), (key1364, 6), (key1861, -2), (key1490, -2), (key1716, -2)]

def rawRow15938 : Integer.Sparse Key := [(key1723, -2), (key1716, -2), (key1711, -2), (key1741, 6), (key1374, -2), (key1364, -2), (key1359, -2), (key1867, 2), (key1861, 2), (key1723, 2), (key1490, 2), (key1711, 2), (key1485, 2), (key1877, -2), (key1741, -2), (key1513, -2), (key1364, 6), (key1861, -2), (key1716, -2), (key1490, -2)]

def rawRow15939 : Integer.Sparse Key := [(key1711, -2), (key1716, -2), (key1741, -2), (key1723, 6), (key1485, -2), (key1490, -2), (key1513, -2), (key1359, 2), (key1364, 2), (key1711, 2), (key1861, 2), (key1741, 2), (key1877, 2), (key1374, -2), (key1723, -2), (key1867, -2), (key1490, 6), (key1364, -2), (key1716, -2), (key1861, -2)]

def rawRow15940 : Integer.Sparse Key := [(key1716, -2), (key1711, -2), (key1741, -2), (key1723, 6), (key1490, -2), (key1485, -2), (key1513, -2), (key1364, 2), (key1359, 2), (key1861, 2), (key1711, 2), (key1877, 2), (key1741, 2), (key1374, -2), (key1867, -2), (key1723, -2), (key1490, 6), (key1364, -2), (key1861, -2), (key1716, -2)]

def rawRow15941 : Integer.Sparse Key := [(key1711, -2), (key1741, -2), (key1716, -2), (key1723, 6), (key1485, -2), (key1513, -2), (key1490, -2), (key1711, 2), (key1741, 2), (key1359, 2), (key1877, 2), (key1364, 2), (key1861, 2), (key1723, -2), (key1374, -2), (key1867, -2), (key1490, 6), (key1716, -2), (key1364, -2), (key1861, -2)]

def rawRow15942 : Integer.Sparse Key := [(key1741, -2), (key1711, -2), (key1716, -2), (key1723, 6), (key1513, -2), (key1485, -2), (key1490, -2), (key1741, 2), (key1711, 2), (key1877, 2), (key1359, 2), (key1861, 2), (key1364, 2), (key1723, -2), (key1867, -2), (key1374, -2), (key1490, 6), (key1716, -2), (key1861, -2), (key1364, -2)]

def rawRow15943 : Integer.Sparse Key := [(key1716, -2), (key1741, -2), (key1711, -2), (key1723, 6), (key1490, -2), (key1513, -2), (key1485, -2), (key1861, 2), (key1877, 2), (key1364, 2), (key1741, 2), (key1359, 2), (key1711, 2), (key1867, -2), (key1374, -2), (key1723, -2), (key1490, 6), (key1861, -2), (key1364, -2), (key1716, -2)]

def rawRow15944 : Integer.Sparse Key := [(key1741, -2), (key1716, -2), (key1711, -2), (key1723, 6), (key1513, -2), (key1490, -2), (key1485, -2), (key1877, 2), (key1861, 2), (key1741, 2), (key1364, 2), (key1711, 2), (key1359, 2), (key1867, -2), (key1723, -2), (key1374, -2), (key1490, 6), (key1861, -2), (key1716, -2), (key1364, -2)]

def rawRow15945 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1867, -2), (key1877, 6), (key1364, -2), (key1364, -2), (key1374, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1513, -2), (key1741, -2), (key1741, -2), (key1359, 6), (key1485, -2), (key1711, -2), (key1711, -2)]

def rawRow15946 : Integer.Sparse Key := [(key1861, -2), (key1867, -2), (key1861, -2), (key1877, 6), (key1364, -2), (key1374, -2), (key1364, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, -2), (key1513, -2), (key1741, -2), (key1359, 6), (key1711, -2), (key1485, -2), (key1711, -2)]

def rawRow15947 : Integer.Sparse Key := [(key1867, -2), (key1861, -2), (key1861, -2), (key1877, 6), (key1374, -2), (key1364, -2), (key1364, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1741, -2), (key1741, -2), (key1513, -2), (key1359, 6), (key1711, -2), (key1711, -2), (key1485, -2)]

def rawRow15948 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1877, -2), (key1867, 6), (key1490, -2), (key1490, -2), (key1513, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1374, -2), (key1723, -2), (key1723, -2), (key1485, 6), (key1359, -2), (key1711, -2), (key1711, -2)]

def rawRow15949 : Integer.Sparse Key := [(key1861, -2), (key1877, -2), (key1861, -2), (key1867, 6), (key1490, -2), (key1513, -2), (key1490, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, -2), (key1374, -2), (key1723, -2), (key1485, 6), (key1711, -2), (key1359, -2), (key1711, -2)]

def rawRow15950 : Integer.Sparse Key := [(key1877, -2), (key1861, -2), (key1861, -2), (key1867, 6), (key1513, -2), (key1490, -2), (key1490, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1723, -2), (key1723, -2), (key1374, -2), (key1485, 6), (key1711, -2), (key1711, -2), (key1359, -2)]

def rawRow15951 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2392, 2), (key2378, -2), (key2381, -2), (key2392, -2), (key2472, 2), (key2480, 2), (key2482, 2), (key2406, -1), (key2409, -1), (key2472, -1), (key2538, -1), (key2482, -1), (key2543, -1), (key2503, -2), (key2506, -2), (key2522, -2), (key2437, -1), (key2440, -1), (key2503, -1), (key2554, -1), (key2522, -1), (key2563, -1), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15952 : Integer.Sparse Key := [(key2378, 2), (key2392, 2), (key2390, 2), (key2381, -2), (key2378, -2), (key2392, -2), (key2472, 2), (key2482, 2), (key2480, 2), (key2409, -1), (key2406, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2482, -1), (key2506, -2), (key2503, -2), (key2522, -2), (key2440, -1), (key2437, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2522, -1), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15953 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2392, 2), (key2378, -2), (key2392, -2), (key2381, -2), (key2480, 2), (key2472, 2), (key2482, 2), (key2472, -1), (key2482, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2503, -2), (key2522, -2), (key2506, -2), (key2503, -1), (key2522, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15954 : Integer.Sparse Key := [(key2390, 2), (key2392, 2), (key2378, 2), (key2392, -2), (key2378, -2), (key2381, -2), (key2480, 2), (key2482, 2), (key2472, 2), (key2482, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2538, -1), (key2409, -1), (key2522, -2), (key2503, -2), (key2506, -2), (key2522, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2554, -1), (key2440, -1), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15955 : Integer.Sparse Key := [(key2392, 2), (key2378, 2), (key2390, 2), (key2381, -2), (key2392, -2), (key2378, -2), (key2482, 2), (key2472, 2), (key2480, 2), (key2538, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2406, -1), (key2472, -1), (key2506, -2), (key2522, -2), (key2503, -2), (key2554, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2437, -1), (key2503, -1), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15956 : Integer.Sparse Key := [(key2392, 2), (key2390, 2), (key2378, 2), (key2392, -2), (key2381, -2), (key2378, -2), (key2482, 2), (key2480, 2), (key2472, 2), (key2543, -1), (key2538, -1), (key2482, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2522, -2), (key2506, -2), (key2503, -2), (key2563, -1), (key2554, -1), (key2522, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15957 : Integer.Sparse Key := [(key2381, 2), (key2392, 2), (key2392, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2538, 2), (key2543, 2), (key2543, 2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2554, -2), (key2554, -2), (key2563, -2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15958 : Integer.Sparse Key := [(key2392, 2), (key2381, 2), (key2392, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2543, 2), (key2538, 2), (key2543, 2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2554, -2), (key2563, -2), (key2554, -2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15959 : Integer.Sparse Key := [(key2392, 2), (key2392, 2), (key2381, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2543, 2), (key2543, 2), (key2538, 2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2563, -2), (key2554, -2), (key2554, -2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15960 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2440, 2), (key2406, -2), (key2409, -2), (key2440, -2), (key2472, 2), (key2503, 2), (key2506, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow15961 : Integer.Sparse Key := [(key2406, 2), (key2440, 2), (key2437, 2), (key2409, -2), (key2406, -2), (key2440, -2), (key2472, 2), (key2506, 2), (key2503, 2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow15962 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2440, 2), (key2406, -2), (key2440, -2), (key2409, -2), (key2503, 2), (key2472, 2), (key2506, 2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2482, 4), (key2392, 4), (key2543, 4)]

def rawRow15963 : Integer.Sparse Key := [(key2437, 2), (key2440, 2), (key2406, 2), (key2440, -2), (key2406, -2), (key2409, -2), (key2503, 2), (key2506, 2), (key2472, 2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow15964 : Integer.Sparse Key := [(key2440, 2), (key2406, 2), (key2437, 2), (key2409, -2), (key2440, -2), (key2406, -2), (key2506, 2), (key2472, 2), (key2503, 2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow15965 : Integer.Sparse Key := [(key2440, 2), (key2437, 2), (key2406, 2), (key2440, -2), (key2409, -2), (key2406, -2), (key2506, 2), (key2503, 2), (key2472, 2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow15966 : Integer.Sparse Key := [(key2409, 2), (key2440, 2), (key2440, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2538, 2), (key2554, 2), (key2554, 2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow15967 : Integer.Sparse Key := [(key2440, 2), (key2409, 2), (key2440, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2554, 2), (key2538, 2), (key2554, 2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow15968 : Integer.Sparse Key := [(key2440, 2), (key2440, 2), (key2409, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2554, 2), (key2554, 2), (key2538, 2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow15969 : Integer.Sparse Key := [(key2472, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2522, -2), (key2378, 2), (key2390, 2), (key2392, 2), (key2437, -1), (key2440, -1), (key2503, -1), (key2554, -1), (key2522, -1), (key2563, -1), (key2378, -2), (key2381, -2), (key2392, -2), (key2406, -1), (key2409, -1), (key2472, -1), (key2538, -1), (key2482, -1), (key2543, -1), (key2440, 4), (key2506, 4), (key2554, 4)]

def rawRow15970 : Integer.Sparse Key := [(key2472, 2), (key2482, 2), (key2480, 2), (key2506, -2), (key2503, -2), (key2522, -2), (key2378, 2), (key2392, 2), (key2390, 2), (key2440, -1), (key2437, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2522, -1), (key2381, -2), (key2378, -2), (key2392, -2), (key2409, -1), (key2406, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2482, -1), (key2440, 4), (key2554, 4), (key2506, 4)]

def rawRow15971 : Integer.Sparse Key := [(key2480, 2), (key2472, 2), (key2482, 2), (key2503, -2), (key2522, -2), (key2506, -2), (key2390, 2), (key2378, 2), (key2392, 2), (key2503, -1), (key2522, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2378, -2), (key2392, -2), (key2381, -2), (key2472, -1), (key2482, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2506, 4), (key2440, 4), (key2554, 4)]

def rawRow15972 : Integer.Sparse Key := [(key2480, 2), (key2482, 2), (key2472, 2), (key2522, -2), (key2503, -2), (key2506, -2), (key2390, 2), (key2392, 2), (key2378, 2), (key2522, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2554, -1), (key2440, -1), (key2392, -2), (key2378, -2), (key2381, -2), (key2482, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2538, -1), (key2409, -1), (key2506, 4), (key2554, 4), (key2440, 4)]

def rawRow15973 : Integer.Sparse Key := [(key2482, 2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2503, -2), (key2392, 2), (key2378, 2), (key2390, 2), (key2554, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2437, -1), (key2503, -1), (key2381, -2), (key2392, -2), (key2378, -2), (key2538, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2406, -1), (key2472, -1), (key2554, 4), (key2440, 4), (key2506, 4)]

def rawRow15974 : Integer.Sparse Key := [(key2482, 2), (key2480, 2), (key2472, 2), (key2522, -2), (key2506, -2), (key2503, -2), (key2392, 2), (key2390, 2), (key2378, 2), (key2563, -1), (key2554, -1), (key2522, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2392, -2), (key2381, -2), (key2378, -2), (key2543, -1), (key2538, -1), (key2482, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2554, 4), (key2506, 4), (key2440, 4)]

def rawRow15975 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2506, 2), (key2480, -2), (key2482, -2), (key2522, -2), (key2406, 2), (key2437, 2), (key2440, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow15976 : Integer.Sparse Key := [(key2472, 2), (key2506, 2), (key2503, 2), (key2482, -2), (key2480, -2), (key2522, -2), (key2406, 2), (key2440, 2), (key2437, 2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow15977 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2506, 2), (key2480, -2), (key2522, -2), (key2482, -2), (key2437, 2), (key2406, 2), (key2440, 2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2482, 4), (key2392, 4), (key2543, 4)]

def rawRow15978 : Integer.Sparse Key := [(key2503, 2), (key2506, 2), (key2472, 2), (key2522, -2), (key2480, -2), (key2482, -2), (key2437, 2), (key2440, 2), (key2406, 2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow15979 : Integer.Sparse Key := [(key2506, 2), (key2472, 2), (key2503, 2), (key2482, -2), (key2522, -2), (key2480, -2), (key2440, 2), (key2406, 2), (key2437, 2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow15980 : Integer.Sparse Key := [(key2506, 2), (key2503, 2), (key2472, 2), (key2522, -2), (key2482, -2), (key2480, -2), (key2440, 2), (key2437, 2), (key2406, 2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow15981 : Integer.Sparse Key := [(key2538, 2), (key2543, 2), (key2543, 2), (key2554, -2), (key2554, -2), (key2563, -2), (key2381, 2), (key2392, 2), (key2392, 2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

def rawRow15982 : Integer.Sparse Key := [(key2543, 2), (key2538, 2), (key2543, 2), (key2554, -2), (key2563, -2), (key2554, -2), (key2392, 2), (key2381, 2), (key2392, 2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

def rawRow15983 : Integer.Sparse Key := [(key2543, 2), (key2543, 2), (key2538, 2), (key2563, -2), (key2554, -2), (key2554, -2), (key2392, 2), (key2392, 2), (key2381, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

def rawRow15984 : Integer.Sparse Key := [(key2538, 2), (key2554, 2), (key2554, 2), (key2543, -2), (key2543, -2), (key2563, -2), (key2409, 2), (key2440, 2), (key2440, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow15985 : Integer.Sparse Key := [(key2554, 2), (key2538, 2), (key2554, 2), (key2543, -2), (key2563, -2), (key2543, -2), (key2440, 2), (key2409, 2), (key2440, 2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow15986 : Integer.Sparse Key := [(key2554, 2), (key2554, 2), (key2538, 2), (key2563, -2), (key2543, -2), (key2543, -2), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow15987 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2779, 2), (key2783, 2), (key2791, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2)]

def rawRow15988 : Integer.Sparse Key := [(key2629, 2), (key2625, 2), (key2637, 2), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2783, 2), (key2779, 2), (key2791, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2)]

def rawRow15989 : Integer.Sparse Key := [(key2625, 2), (key2637, 2), (key2629, 2), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 2), (key2791, 2), (key2783, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2)]

def rawRow15990 : Integer.Sparse Key := [(key2637, 2), (key2625, 2), (key2629, 2), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 2), (key2779, 2), (key2783, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2)]

def rawRow15991 : Integer.Sparse Key := [(key2629, 2), (key2637, 2), (key2625, 2), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2783, 2), (key2791, 2), (key2779, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2)]

def rawRow15992 : Integer.Sparse Key := [(key2637, 2), (key2629, 2), (key2625, 2), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2791, 2), (key2783, 2), (key2779, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2)]

def rawRow15993 : Integer.Sparse Key := [(key2647, 2), (key2647, 2), (key2652, 2), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2937, 2), (key2937, 2), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2)]

def rawRow15994 : Integer.Sparse Key := [(key2647, 2), (key2652, 2), (key2647, 2), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2937, 2), (key2942, 2), (key2937, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2)]

def rawRow15995 : Integer.Sparse Key := [(key2652, 2), (key2647, 2), (key2647, 2), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2942, 2), (key2937, 2), (key2937, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2)]

def rawRow15996 : Integer.Sparse Key := [(key2699, 2), (key2703, 2), (key2723, 2), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2)]

def rawRow15997 : Integer.Sparse Key := [(key2703, 2), (key2699, 2), (key2723, 2), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2)]

def rawRow15998 : Integer.Sparse Key := [(key2699, 2), (key2723, 2), (key2703, 2), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2)]

def rawRow15999 : Integer.Sparse Key := [(key2723, 2), (key2699, 2), (key2703, 2), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2)]

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

def rawRow16000 : Integer.Sparse Key := [(key2703, 2), (key2723, 2), (key2699, 2), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2)]

def rawRow16001 : Integer.Sparse Key := [(key2723, 2), (key2703, 2), (key2699, 2), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2)]

def rawRow16002 : Integer.Sparse Key := [(key2736, 2), (key2736, 2), (key2746, 2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2)]

def rawRow16003 : Integer.Sparse Key := [(key2736, 2), (key2746, 2), (key2736, 2), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2)]

def rawRow16004 : Integer.Sparse Key := [(key2746, 2), (key2736, 2), (key2736, 2), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2)]

def rawRow16005 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, 2), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2)]

def rawRow16006 : Integer.Sparse Key := [(key2783, 2), (key2779, 2), (key2791, 2), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2)]

def rawRow16007 : Integer.Sparse Key := [(key2779, 2), (key2791, 2), (key2783, 2), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2)]

def rawRow16008 : Integer.Sparse Key := [(key2791, 2), (key2779, 2), (key2783, 2), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2)]

def rawRow16009 : Integer.Sparse Key := [(key2783, 2), (key2791, 2), (key2779, 2), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2)]

def rawRow16010 : Integer.Sparse Key := [(key2791, 2), (key2783, 2), (key2779, 2), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2)]

def rawRow16011 : Integer.Sparse Key := [(key2802, 2), (key2806, 2), (key2826, 2), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2)]

def rawRow16012 : Integer.Sparse Key := [(key2806, 2), (key2802, 2), (key2826, 2), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2)]

def rawRow16013 : Integer.Sparse Key := [(key2802, 2), (key2826, 2), (key2806, 2), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2)]

def rawRow16014 : Integer.Sparse Key := [(key2826, 2), (key2802, 2), (key2806, 2), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2)]

def rawRow16015 : Integer.Sparse Key := [(key2806, 2), (key2826, 2), (key2802, 2), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2)]

def rawRow16016 : Integer.Sparse Key := [(key2826, 2), (key2806, 2), (key2802, 2), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2)]

def rawRow16017 : Integer.Sparse Key := [(key2937, 2), (key2937, 2), (key2942, 2), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2)]

def rawRow16018 : Integer.Sparse Key := [(key2937, 2), (key2942, 2), (key2937, 2), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2)]

def rawRow16019 : Integer.Sparse Key := [(key2942, 2), (key2937, 2), (key2937, 2), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2)]

def rawRow16020 : Integer.Sparse Key := [(key2949, 2), (key2949, 2), (key2959, 2), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2)]

def rawRow16021 : Integer.Sparse Key := [(key2949, 2), (key2959, 2), (key2949, 2), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2)]

def rawRow16022 : Integer.Sparse Key := [(key2959, 2), (key2949, 2), (key2949, 2), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2)]

def rawRow16023 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2613, 2), (key2629, 2), (key2647, 2), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2668, -2), (key2783, -2), (key2937, -2), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1), (key2826, 2), (key2867, 2), (key2903, 2), (key2723, -2), (key2867, -2), (key2982, -2)]

def rawRow16024 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2613, 2), (key2647, 2), (key2629, 2), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2668, -2), (key2937, -2), (key2783, -2), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1), (key2826, 2), (key2903, 2), (key2867, 2), (key2723, -2), (key2982, -2), (key2867, -2)]

def rawRow16025 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2629, 2), (key2613, 2), (key2647, 2), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2783, -2), (key2668, -2), (key2937, -2), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2867, 2), (key2826, 2), (key2903, 2), (key2867, -2), (key2723, -2), (key2982, -2)]

def rawRow16026 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2629, 2), (key2647, 2), (key2613, 2), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2783, -2), (key2937, -2), (key2668, -2), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1), (key2867, 2), (key2903, 2), (key2826, 2), (key2867, -2), (key2982, -2), (key2723, -2)]

def rawRow16027 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2647, 2), (key2613, 2), (key2629, 2), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2937, -2), (key2668, -2), (key2783, -2), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1), (key2903, 2), (key2826, 2), (key2867, 2), (key2982, -2), (key2723, -2), (key2867, -2)]

def rawRow16028 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2647, 2), (key2629, 2), (key2613, 2), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2937, -2), (key2783, -2), (key2668, -2), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2903, 2), (key2867, 2), (key2826, 2), (key2982, -2), (key2867, -2), (key2723, -2)]

def rawRow16029 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2609, 2), (key2625, 2), (key2625, 2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2664, -2), (key2779, -2), (key2779, -2), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2959, 2), (key2982, 2), (key2982, 2), (key2746, -2), (key2903, -2), (key2903, -2)]

def rawRow16030 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2625, 2), (key2609, 2), (key2625, 2), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2779, -2), (key2664, -2), (key2779, -2), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2982, 2), (key2959, 2), (key2982, 2), (key2903, -2), (key2746, -2), (key2903, -2)]

def rawRow16031 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2625, 2), (key2625, 2), (key2609, 2), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2779, -2), (key2779, -2), (key2664, -2), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2982, 2), (key2982, 2), (key2959, 2), (key2903, -2), (key2903, -2), (key2746, -2)]

def rawRow16032 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2668, 2), (key2703, 2), (key2736, 2), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2613, -2), (key2806, -2), (key2949, -2), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2791, 2), (key2857, 2), (key2896, 2), (key2637, -2), (key2857, -2), (key2975, -2)]

def rawRow16033 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2668, 2), (key2736, 2), (key2703, 2), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2613, -2), (key2949, -2), (key2806, -2), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2791, 2), (key2896, 2), (key2857, 2), (key2637, -2), (key2975, -2), (key2857, -2)]

def rawRow16034 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2703, 2), (key2668, 2), (key2736, 2), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2806, -2), (key2613, -2), (key2949, -2), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2857, 2), (key2791, 2), (key2896, 2), (key2857, -2), (key2637, -2), (key2975, -2)]

def rawRow16035 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2703, 2), (key2736, 2), (key2668, 2), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2806, -2), (key2949, -2), (key2613, -2), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2857, 2), (key2896, 2), (key2791, 2), (key2857, -2), (key2975, -2), (key2637, -2)]

def rawRow16036 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2736, 2), (key2668, 2), (key2703, 2), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2949, -2), (key2613, -2), (key2806, -2), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2896, 2), (key2791, 2), (key2857, 2), (key2975, -2), (key2637, -2), (key2857, -2)]

def rawRow16037 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2736, 2), (key2703, 2), (key2668, 2), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2949, -2), (key2806, -2), (key2613, -2), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2896, 2), (key2857, 2), (key2791, 2), (key2975, -2), (key2857, -2), (key2637, -2)]

def rawRow16038 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2609, -2), (key2802, -2), (key2802, -2), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2942, 2), (key2975, 2), (key2975, 2), (key2652, -2), (key2896, -2), (key2896, -2)]

def rawRow16039 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2802, -2), (key2609, -2), (key2802, -2), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2975, 2), (key2942, 2), (key2975, 2), (key2896, -2), (key2652, -2), (key2896, -2)]

def rawRow16040 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2802, -2), (key2802, -2), (key2609, -2), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2975, 2), (key2975, 2), (key2942, 2), (key2896, -2), (key2896, -2), (key2652, -2)]

def rawRow16041 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2826, 2), (key2867, 2), (key2903, 2), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1), (key2723, -2), (key2867, -2), (key2982, -2), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2613, 2), (key2629, 2), (key2647, 2), (key2668, -2), (key2783, -2), (key2937, -2)]

def rawRow16042 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2826, 2), (key2903, 2), (key2867, 2), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1), (key2723, -2), (key2982, -2), (key2867, -2), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2613, 2), (key2647, 2), (key2629, 2), (key2668, -2), (key2937, -2), (key2783, -2)]

def rawRow16043 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2867, 2), (key2826, 2), (key2903, 2), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2867, -2), (key2723, -2), (key2982, -2), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2629, 2), (key2613, 2), (key2647, 2), (key2783, -2), (key2668, -2), (key2937, -2)]

def rawRow16044 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2867, 2), (key2903, 2), (key2826, 2), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1), (key2867, -2), (key2982, -2), (key2723, -2), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2629, 2), (key2647, 2), (key2613, 2), (key2783, -2), (key2937, -2), (key2668, -2)]

def rawRow16045 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2903, 2), (key2826, 2), (key2867, 2), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1), (key2982, -2), (key2723, -2), (key2867, -2), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2647, 2), (key2613, 2), (key2629, 2), (key2937, -2), (key2668, -2), (key2783, -2)]

def rawRow16046 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2903, 2), (key2867, 2), (key2826, 2), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2982, -2), (key2867, -2), (key2723, -2), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2647, 2), (key2629, 2), (key2613, 2), (key2937, -2), (key2783, -2), (key2668, -2)]

def rawRow16047 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2791, 2), (key2857, 2), (key2896, 2), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2637, -2), (key2857, -2), (key2975, -2), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2668, 2), (key2703, 2), (key2736, 2), (key2613, -2), (key2806, -2), (key2949, -2)]

def rawRow16048 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2791, 2), (key2896, 2), (key2857, 2), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2637, -2), (key2975, -2), (key2857, -2), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2668, 2), (key2736, 2), (key2703, 2), (key2613, -2), (key2949, -2), (key2806, -2)]

def rawRow16049 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2857, 2), (key2791, 2), (key2896, 2), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2857, -2), (key2637, -2), (key2975, -2), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2703, 2), (key2668, 2), (key2736, 2), (key2806, -2), (key2613, -2), (key2949, -2)]

def rawRow16050 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2857, 2), (key2896, 2), (key2791, 2), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2857, -2), (key2975, -2), (key2637, -2), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2703, 2), (key2736, 2), (key2668, 2), (key2806, -2), (key2949, -2), (key2613, -2)]

def rawRow16051 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2896, 2), (key2791, 2), (key2857, 2), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2975, -2), (key2637, -2), (key2857, -2), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2736, 2), (key2668, 2), (key2703, 2), (key2949, -2), (key2613, -2), (key2806, -2)]

def rawRow16052 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2896, 2), (key2857, 2), (key2791, 2), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2975, -2), (key2857, -2), (key2637, -2), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2736, 2), (key2703, 2), (key2668, 2), (key2949, -2), (key2806, -2), (key2613, -2)]

def rawRow16053 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2959, 2), (key2982, 2), (key2982, 2), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2746, -2), (key2903, -2), (key2903, -2), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2609, 2), (key2625, 2), (key2625, 2), (key2664, -2), (key2779, -2), (key2779, -2)]

def rawRow16054 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2982, 2), (key2959, 2), (key2982, 2), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2903, -2), (key2746, -2), (key2903, -2), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2625, 2), (key2609, 2), (key2625, 2), (key2779, -2), (key2664, -2), (key2779, -2)]

def rawRow16055 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2982, 2), (key2982, 2), (key2959, 2), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2903, -2), (key2903, -2), (key2746, -2), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2625, 2), (key2625, 2), (key2609, 2), (key2779, -2), (key2779, -2), (key2664, -2)]

def rawRow16056 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2652, -2), (key2896, -2), (key2896, -2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2664, 2), (key2699, 2), (key2699, 2), (key2609, -2), (key2802, -2), (key2802, -2)]

def rawRow16057 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2896, -2), (key2652, -2), (key2896, -2), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2699, 2), (key2664, 2), (key2699, 2), (key2802, -2), (key2609, -2), (key2802, -2)]

def rawRow16058 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2896, -2), (key2896, -2), (key2652, -2), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2699, 2), (key2699, 2), (key2664, 2), (key2802, -2), (key2802, -2), (key2609, -2)]

def rawRow16059 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2611, 2), (key2627, 2), (key2636, 2), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2666, -2), (key2701, -2), (key2722, -2), (key2801, -1), (key2804, -1), (key2851, -1), (key2856, -1), (key2892, -1), (key2895, -1), (key2778, 1), (key2781, 1), (key2851, 1), (key2866, 1), (key2892, 1), (key2902, 1), (key2947, 2), (key2971, 2), (key2974, 2), (key2935, -2), (key2971, -2), (key2981, -2)]

def rawRow16060 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2611, 2), (key2636, 2), (key2627, 2), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2666, -2), (key2722, -2), (key2701, -2), (key2804, -1), (key2801, -1), (key2856, -1), (key2851, -1), (key2895, -1), (key2892, -1), (key2781, 1), (key2778, 1), (key2866, 1), (key2851, 1), (key2902, 1), (key2892, 1), (key2947, 2), (key2974, 2), (key2971, 2), (key2935, -2), (key2981, -2), (key2971, -2)]

def rawRow16061 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2627, 2), (key2611, 2), (key2636, 2), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2701, -2), (key2666, -2), (key2722, -2), (key2851, -1), (key2892, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2851, 1), (key2892, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2866, 1), (key2971, 2), (key2947, 2), (key2974, 2), (key2971, -2), (key2935, -2), (key2981, -2)]

def rawRow16062 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2627, 2), (key2636, 2), (key2611, 2), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2701, -2), (key2722, -2), (key2666, -2), (key2892, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2856, -1), (key2804, -1), (key2892, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2866, 1), (key2781, 1), (key2971, 2), (key2974, 2), (key2947, 2), (key2971, -2), (key2981, -2), (key2935, -2)]

def rawRow16063 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2636, 2), (key2611, 2), (key2627, 2), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2722, -2), (key2666, -2), (key2701, -2), (key2856, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2801, -1), (key2851, -1), (key2866, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2778, 1), (key2851, 1), (key2974, 2), (key2947, 2), (key2971, 2), (key2981, -2), (key2935, -2), (key2971, -2)]

def rawRow16064 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2636, 2), (key2627, 2), (key2611, 2), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2722, -2), (key2701, -2), (key2666, -2), (key2895, -1), (key2856, -1), (key2892, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 1), (key2866, 1), (key2892, 1), (key2781, 1), (key2851, 1), (key2778, 1), (key2974, 2), (key2971, 2), (key2947, 2), (key2981, -2), (key2971, -2), (key2935, -2)]

def rawRow16065 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2608, 2), (key2624, 2), (key2624, 2), (key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2734, 1), (key2734, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2902, -1), (key2902, -1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2895, 1), (key2895, 1), (key2958, 2), (key2981, 2), (key2981, 2), (key2941, -2), (key2974, -2), (key2974, -2)]

def rawRow16066 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2624, 2), (key2608, 2), (key2624, 2), (key2701, 1), (key2734, 1), (key2666, 1), (key2734, 1), (key2666, 1), (key2701, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2866, -1), (key2902, -1), (key2825, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2856, 1), (key2895, 1), (key2790, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2981, 2), (key2958, 2), (key2981, 2), (key2974, -2), (key2941, -2), (key2974, -2)]

def rawRow16067 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2624, 2), (key2624, 2), (key2608, 2), (key2734, 1), (key2701, 1), (key2734, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2902, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2825, -1), (key2895, 1), (key2856, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2790, 1), (key2981, 2), (key2981, 2), (key2958, 2), (key2974, -2), (key2974, -2), (key2941, -2)]

def rawRow16068 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2666, 2), (key2701, 2), (key2734, 2), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2611, -2), (key2804, -2), (key2825, -2), (key2698, -1), (key2701, -1), (key2851, -1), (key2856, -1), (key2971, -1), (key2974, -1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2734, 2), (key2892, 2), (key2895, 2), (key2645, -2), (key2892, -2), (key2902, -2)]

def rawRow16069 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2666, 2), (key2734, 2), (key2701, 2), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2611, -2), (key2825, -2), (key2804, -2), (key2701, -1), (key2698, -1), (key2856, -1), (key2851, -1), (key2974, -1), (key2971, -1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2734, 2), (key2895, 2), (key2892, 2), (key2645, -2), (key2902, -2), (key2892, -2)]

def rawRow16070 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2701, 2), (key2666, 2), (key2734, 2), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2804, -2), (key2611, -2), (key2825, -2), (key2851, -1), (key2971, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2892, 2), (key2734, 2), (key2895, 2), (key2892, -2), (key2645, -2), (key2902, -2)]

def rawRow16071 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2701, 2), (key2734, 2), (key2666, 2), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2804, -2), (key2825, -2), (key2611, -2), (key2971, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2856, -1), (key2701, -1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2892, 2), (key2895, 2), (key2734, 2), (key2892, -2), (key2902, -2), (key2645, -2)]

def rawRow16072 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2734, 2), (key2666, 2), (key2701, 2), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2825, -2), (key2611, -2), (key2804, -2), (key2856, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2698, -1), (key2851, -1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2895, 2), (key2734, 2), (key2892, 2), (key2902, -2), (key2645, -2), (key2892, -2)]

def rawRow16073 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2734, 2), (key2701, 2), (key2666, 2), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2825, -2), (key2804, -2), (key2611, -2), (key2974, -1), (key2856, -1), (key2971, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2895, 2), (key2892, 2), (key2734, 2), (key2902, -2), (key2892, -2), (key2645, -2)]

def rawRow16074 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2608, -2), (key2801, -2), (key2801, -2), (key2722, -1), (key2722, -1), (key2866, -1), (key2866, -1), (key2981, -1), (key2981, -1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2745, 2), (key2902, 2), (key2902, 2), (key2651, -2), (key2895, -2), (key2895, -2)]

def rawRow16075 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2801, -2), (key2608, -2), (key2801, -2), (key2866, -1), (key2981, -1), (key2722, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2902, 2), (key2745, 2), (key2902, 2), (key2895, -2), (key2651, -2), (key2895, -2)]

def rawRow16076 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2801, -2), (key2801, -2), (key2608, -2), (key2981, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2902, 2), (key2902, 2), (key2745, 2), (key2895, -2), (key2895, -2), (key2651, -2)]

def rawRow16077 : Integer.Sparse Key := [(key2801, -1), (key2804, -1), (key2851, -1), (key2892, -1), (key2856, -1), (key2895, -1), (key2825, 2), (key2866, 2), (key2902, 2), (key2698, 1), (key2701, 1), (key2851, 1), (key2971, 1), (key2856, 1), (key2974, 1), (key2722, -2), (key2866, -2), (key2981, -2), (key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2611, 2), (key2627, 2), (key2636, 2), (key2666, -2), (key2701, -2), (key2722, -2)]

def rawRow16078 : Integer.Sparse Key := [(key2804, -1), (key2801, -1), (key2892, -1), (key2851, -1), (key2895, -1), (key2856, -1), (key2825, 2), (key2902, 2), (key2866, 2), (key2701, 1), (key2698, 1), (key2971, 1), (key2851, 1), (key2974, 1), (key2856, 1), (key2722, -2), (key2981, -2), (key2866, -2), (key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2611, 2), (key2636, 2), (key2627, 2), (key2666, -2), (key2722, -2), (key2701, -2)]

def rawRow16079 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2866, 2), (key2825, 2), (key2902, 2), (key2851, 1), (key2856, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2866, -2), (key2722, -2), (key2981, -2), (key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2627, 2), (key2611, 2), (key2636, 2), (key2701, -2), (key2666, -2), (key2722, -2)]

def rawRow16080 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2892, -1), (key2804, -1), (key2866, 2), (key2902, 2), (key2825, 2), (key2856, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2971, 1), (key2701, 1), (key2866, -2), (key2981, -2), (key2722, -2), (key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2627, 2), (key2636, 2), (key2611, 2), (key2701, -2), (key2722, -2), (key2666, -2)]

def rawRow16081 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2801, -1), (key2851, -1), (key2902, 2), (key2825, 2), (key2866, 2), (key2971, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2698, 1), (key2851, 1), (key2981, -2), (key2722, -2), (key2866, -2), (key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2636, 2), (key2611, 2), (key2627, 2), (key2722, -2), (key2666, -2), (key2701, -2)]

def rawRow16082 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2856, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 2), (key2866, 2), (key2825, 2), (key2974, 1), (key2971, 1), (key2856, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, -2), (key2866, -2), (key2722, -2), (key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2636, 2), (key2627, 2), (key2611, 2), (key2722, -2), (key2701, -2), (key2666, -2)]

def rawRow16083 : Integer.Sparse Key := [(key2778, -1), (key2781, -1), (key2851, -1), (key2892, -1), (key2866, -1), (key2902, -1), (key2790, 2), (key2856, 2), (key2895, 2), (key2624, 1), (key2627, 1), (key2851, 1), (key2971, 1), (key2866, 1), (key2981, 1), (key2636, -2), (key2856, -2), (key2974, -2), (key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2666, 2), (key2781, 2), (key2790, 2), (key2611, -2), (key2804, -2), (key2825, -2)]

def rawRow16084 : Integer.Sparse Key := [(key2781, -1), (key2778, -1), (key2892, -1), (key2851, -1), (key2902, -1), (key2866, -1), (key2790, 2), (key2895, 2), (key2856, 2), (key2627, 1), (key2624, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2866, 1), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2666, 2), (key2790, 2), (key2781, 2), (key2611, -2), (key2825, -2), (key2804, -2)]

def rawRow16085 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2778, -1), (key2902, -1), (key2781, -1), (key2892, -1), (key2856, 2), (key2790, 2), (key2895, 2), (key2851, 1), (key2866, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2856, -2), (key2636, -2), (key2974, -2), (key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2781, 2), (key2666, 2), (key2790, 2), (key2804, -2), (key2611, -2), (key2825, -2)]

def rawRow16086 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2902, -1), (key2778, -1), (key2892, -1), (key2781, -1), (key2856, 2), (key2895, 2), (key2790, 2), (key2866, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2971, 1), (key2627, 1), (key2856, -2), (key2974, -2), (key2636, -2), (key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2781, 2), (key2790, 2), (key2666, 2), (key2804, -2), (key2825, -2), (key2611, -2)]

def rawRow16087 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2781, -1), (key2866, -1), (key2778, -1), (key2851, -1), (key2895, 2), (key2790, 2), (key2856, 2), (key2971, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2624, 1), (key2851, 1), (key2974, -2), (key2636, -2), (key2856, -2), (key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2790, 2), (key2666, 2), (key2781, 2), (key2825, -2), (key2611, -2), (key2804, -2)]

def rawRow16088 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2866, -1), (key2781, -1), (key2851, -1), (key2778, -1), (key2895, 2), (key2856, 2), (key2790, 2), (key2981, 1), (key2971, 1), (key2866, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2974, -2), (key2856, -2), (key2636, -2), (key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2790, 2), (key2781, 2), (key2666, 2), (key2825, -2), (key2804, -2), (key2611, -2)]

def rawRow16089 : Integer.Sparse Key := [(key2947, -1), (key2947, -1), (key2971, -1), (key2971, -1), (key2974, -1), (key2974, -1), (key2958, 2), (key2981, 2), (key2981, 2), (key2734, 1), (key2734, 1), (key2892, 1), (key2892, 1), (key2895, 1), (key2895, 1), (key2745, -2), (key2902, -2), (key2902, -2), (key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, -2), (key2698, -2), (key2698, -2)]

def rawRow16090 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2947, -1), (key2974, -1), (key2947, -1), (key2971, -1), (key2981, 2), (key2958, 2), (key2981, 2), (key2892, 1), (key2895, 1), (key2734, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2902, -2), (key2745, -2), (key2902, -2), (key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, -2), (key2663, -2), (key2698, -2)]

def rawRow16091 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2974, -1), (key2947, -1), (key2971, -1), (key2947, -1), (key2981, 2), (key2981, 2), (key2958, 2), (key2895, 1), (key2892, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2734, 1), (key2902, -2), (key2902, -2), (key2745, -2), (key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, -2), (key2698, -2), (key2663, -2)]

def rawRow16092 : Integer.Sparse Key := [(key2935, -1), (key2935, -1), (key2971, -1), (key2971, -1), (key2981, -1), (key2981, -1), (key2941, 2), (key2974, 2), (key2974, 2), (key2645, 1), (key2645, 1), (key2892, 1), (key2892, 1), (key2902, 1), (key2902, 1), (key2651, -2), (key2895, -2), (key2895, -2), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, -2), (key2801, -2), (key2801, -2)]

def rawRow16093 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2935, -1), (key2981, -1), (key2935, -1), (key2971, -1), (key2974, 2), (key2941, 2), (key2974, 2), (key2892, 1), (key2902, 1), (key2645, 1), (key2902, 1), (key2645, 1), (key2892, 1), (key2895, -2), (key2651, -2), (key2895, -2), (key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -2), (key2608, -2), (key2801, -2)]

def rawRow16094 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2981, -1), (key2935, -1), (key2971, -1), (key2935, -1), (key2974, 2), (key2974, 2), (key2941, 2), (key2902, 1), (key2892, 1), (key2902, 1), (key2645, 1), (key2892, 1), (key2645, 1), (key2895, -2), (key2895, -2), (key2651, -2), (key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, -2), (key2801, -2), (key2608, -2)]

def rawRow16095 : Integer.Sparse Key := [(key2592, 4), (key2991, 4), (key2991, 4), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16096 : Integer.Sparse Key := [(key2991, 4), (key2592, 4), (key2991, 4), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16097 : Integer.Sparse Key := [(key2991, 4), (key2991, 4), (key2592, 4), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16098 : Integer.Sparse Key := [(key2595, 4), (key2970, 4), (key2993, 4), (key2592, -2), (key2595, -2), (key2848, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16099 : Integer.Sparse Key := [(key2595, 4), (key2993, 4), (key2970, 4), (key2595, -2), (key2592, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2970, -2), (key2603, -2), (key2602, -2), (key2914, -2), (key2891, -2), (key3003, -2), (key2996, -2), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16100 : Integer.Sparse Key := [(key2970, 4), (key2595, 4), (key2993, 4), (key2848, -2), (key2970, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16101 : Integer.Sparse Key := [(key2970, 4), (key2993, 4), (key2595, 4), (key2970, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2882, -2), (key2595, -2), (key2996, -2), (key2891, -2), (key3003, -2), (key2602, -2), (key2914, -2), (key2603, -2), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16102 : Integer.Sparse Key := [(key2993, 4), (key2595, 4), (key2970, 4), (key2882, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2592, -2), (key2848, -2), (key2914, -2), (key3003, -2), (key2603, -2), (key2996, -2), (key2602, -2), (key2891, -2), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16103 : Integer.Sparse Key := [(key2993, 4), (key2970, 4), (key2595, 4), (key2991, -2), (key2882, -2), (key2970, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key3003, -2), (key2914, -2), (key2996, -2), (key2603, -2), (key2891, -2), (key2602, -2), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16104 : Integer.Sparse Key := [(key2592, 4), (key2991, 4), (key2991, 4), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16105 : Integer.Sparse Key := [(key2991, 4), (key2592, 4), (key2991, 4), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16106 : Integer.Sparse Key := [(key2991, 4), (key2991, 4), (key2592, 4), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16107 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2379, -2), (key2393, -2), (key2771, -2), (key2912, -2), (key2933, -2), (key2991, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16108 : Integer.Sparse Key := [(key2393, 4), (key2565, 4), (key2441, 4), (key2393, -2), (key2379, -2), (key2912, -2), (key2771, -2), (key2991, -2), (key2933, -2), (key2603, -2), (key2595, -2), (key2914, -2), (key2774, -2), (key2993, -2), (key2934, -2), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16109 : Integer.Sparse Key := [(key2441, 4), (key2393, 4), (key2565, 4), (key2407, -2), (key2441, -2), (key2592, -2), (key2991, -2), (key2602, -2), (key2912, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16110 : Integer.Sparse Key := [(key2441, 4), (key2565, 4), (key2393, 4), (key2441, -2), (key2407, -2), (key2991, -2), (key2592, -2), (key2912, -2), (key2602, -2), (key2934, -2), (key2774, -2), (key2993, -2), (key2595, -2), (key2914, -2), (key2603, -2), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16111 : Integer.Sparse Key := [(key2565, 4), (key2393, 4), (key2441, 4), (key2544, -2), (key2555, -2), (key2393, -2), (key2441, -2), (key2379, -2), (key2771, -2), (key2914, -2), (key2993, -2), (key2603, -2), (key2934, -2), (key2595, -2), (key2774, -2), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16112 : Integer.Sparse Key := [(key2565, 4), (key2441, 4), (key2393, 4), (key2555, -2), (key2544, -2), (key2441, -2), (key2393, -2), (key2407, -2), (key2592, -2), (key2993, -2), (key2914, -2), (key2934, -2), (key2603, -2), (key2774, -2), (key2595, -2), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16113 : Integer.Sparse Key := [(key2382, 4), (key2507, 4), (key2557, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2545, -2), (key2526, -2), (key2565, -2), (key2592, -2), (key2595, -2), (key2848, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16114 : Integer.Sparse Key := [(key2382, 4), (key2557, 4), (key2507, 4), (key2395, -2), (key2393, -2), (key2545, -2), (key2483, -2), (key2565, -2), (key2526, -2), (key2595, -2), (key2592, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2970, -2), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16115 : Integer.Sparse Key := [(key2507, 4), (key2382, 4), (key2557, 4), (key2483, -2), (key2526, -2), (key2393, -2), (key2565, -2), (key2395, -2), (key2545, -2), (key2848, -2), (key2970, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16116 : Integer.Sparse Key := [(key2507, 4), (key2557, 4), (key2382, 4), (key2526, -2), (key2483, -2), (key2565, -2), (key2393, -2), (key2545, -2), (key2395, -2), (key2970, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2882, -2), (key2595, -2), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16117 : Integer.Sparse Key := [(key2557, 4), (key2382, 4), (key2507, 4), (key2545, -2), (key2565, -2), (key2395, -2), (key2526, -2), (key2393, -2), (key2483, -2), (key2882, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2592, -2), (key2848, -2), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16118 : Integer.Sparse Key := [(key2557, 4), (key2507, 4), (key2382, 4), (key2565, -2), (key2545, -2), (key2526, -2), (key2395, -2), (key2483, -2), (key2393, -2), (key2991, -2), (key2882, -2), (key2970, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16119 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2382, -2), (key2395, -2), (key2410, -2), (key2545, -2), (key2445, -2), (key2557, -2), (key2379, -2), (key2393, -2), (key2771, -2), (key2912, -2), (key2933, -2), (key2991, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16120 : Integer.Sparse Key := [(key2393, 4), (key2565, 4), (key2441, 4), (key2395, -2), (key2382, -2), (key2545, -2), (key2410, -2), (key2557, -2), (key2445, -2), (key2393, -2), (key2379, -2), (key2912, -2), (key2771, -2), (key2991, -2), (key2933, -2), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16121 : Integer.Sparse Key := [(key2441, 4), (key2393, 4), (key2565, 4), (key2410, -2), (key2445, -2), (key2382, -2), (key2557, -2), (key2395, -2), (key2545, -2), (key2407, -2), (key2441, -2), (key2592, -2), (key2991, -2), (key2602, -2), (key2912, -2), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16122 : Integer.Sparse Key := [(key2441, 4), (key2565, 4), (key2393, 4), (key2445, -2), (key2410, -2), (key2557, -2), (key2382, -2), (key2545, -2), (key2395, -2), (key2441, -2), (key2407, -2), (key2991, -2), (key2592, -2), (key2912, -2), (key2602, -2), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16123 : Integer.Sparse Key := [(key2565, 4), (key2393, 4), (key2441, 4), (key2545, -2), (key2557, -2), (key2395, -2), (key2445, -2), (key2382, -2), (key2410, -2), (key2544, -2), (key2555, -2), (key2393, -2), (key2441, -2), (key2379, -2), (key2771, -2), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16124 : Integer.Sparse Key := [(key2565, 4), (key2441, 4), (key2393, 4), (key2557, -2), (key2545, -2), (key2445, -2), (key2395, -2), (key2410, -2), (key2382, -2), (key2555, -2), (key2544, -2), (key2441, -2), (key2393, -2), (key2407, -2), (key2592, -2), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16125 : Integer.Sparse Key := [(key2395, 4), (key2445, 4), (key2526, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2483, -2), (key2441, -2), (key2507, -2), (key2382, -2), (key2393, -2), (key2410, -2), (key2483, -2), (key2441, -2), (key2507, -2), (key2379, 4), (key2771, 4), (key2848, 4)]

def rawRow16126 : Integer.Sparse Key := [(key2395, 4), (key2526, 4), (key2445, 4), (key2393, -2), (key2382, -2), (key2483, -2), (key2410, -2), (key2507, -2), (key2441, -2), (key2393, -2), (key2382, -2), (key2483, -2), (key2410, -2), (key2507, -2), (key2441, -2), (key2379, 4), (key2848, 4), (key2771, 4)]

def rawRow16127 : Integer.Sparse Key := [(key2445, 4), (key2395, 4), (key2526, 4), (key2410, -2), (key2441, -2), (key2382, -2), (key2507, -2), (key2393, -2), (key2483, -2), (key2410, -2), (key2441, -2), (key2382, -2), (key2507, -2), (key2393, -2), (key2483, -2), (key2407, 4), (key2592, 4), (key2848, 4)]

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

def rawRow16128 : Integer.Sparse Key := [(key2445, 4), (key2526, 4), (key2395, 4), (key2441, -2), (key2410, -2), (key2507, -2), (key2382, -2), (key2483, -2), (key2393, -2), (key2441, -2), (key2410, -2), (key2507, -2), (key2382, -2), (key2483, -2), (key2393, -2), (key2407, 4), (key2848, 4), (key2592, 4)]

def rawRow16129 : Integer.Sparse Key := [(key2526, 4), (key2395, 4), (key2445, 4), (key2483, -2), (key2507, -2), (key2393, -2), (key2441, -2), (key2382, -2), (key2410, -2), (key2483, -2), (key2507, -2), (key2393, -2), (key2441, -2), (key2382, -2), (key2410, -2), (key2473, 4), (key2379, 4), (key2771, 4)]

def rawRow16130 : Integer.Sparse Key := [(key2526, 4), (key2445, 4), (key2395, 4), (key2507, -2), (key2483, -2), (key2441, -2), (key2393, -2), (key2410, -2), (key2382, -2), (key2507, -2), (key2483, -2), (key2441, -2), (key2393, -2), (key2410, -2), (key2382, -2), (key2473, 4), (key2407, 4), (key2592, 4)]

def rawRow16131 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1041, 6), (key1111, -2), (key1111, -2), (key1155, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1006, -2), (key1193, -2), (key1193, -2), (key1127, 6), (key1019, -2), (key1199, -2), (key1199, -2)]

def rawRow16132 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 6), (key1111, -2), (key1155, -2), (key1111, -2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1193, -2), (key1006, -2), (key1193, -2), (key1127, 6), (key1199, -2), (key1019, -2), (key1199, -2)]

def rawRow16133 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1041, 6), (key1155, -2), (key1111, -2), (key1111, -2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1193, -2), (key1193, -2), (key1006, -2), (key1127, 6), (key1199, -2), (key1199, -2), (key1019, -2)]

def rawRow16134 : Integer.Sparse Key := [(key1033, -2), (key1041, -2), (key1076, -2), (key1033, 6), (key1190, -2), (key1193, -2), (key1212, -2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key998, -2), (key1111, -2), (key1190, -2), (key1199, 6), (key1019, -2), (key1127, -2), (key1199, -2)]

def rawRow16135 : Integer.Sparse Key := [(key1041, -2), (key1033, -2), (key1076, -2), (key1033, 6), (key1193, -2), (key1190, -2), (key1212, -2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key998, -2), (key1190, -2), (key1111, -2), (key1199, 6), (key1019, -2), (key1199, -2), (key1127, -2)]

def rawRow16136 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1041, -2), (key1033, 6), (key1190, -2), (key1212, -2), (key1193, -2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1111, -2), (key998, -2), (key1190, -2), (key1199, 6), (key1127, -2), (key1019, -2), (key1199, -2)]

def rawRow16137 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1041, -2), (key1033, 6), (key1212, -2), (key1190, -2), (key1193, -2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1111, -2), (key1190, -2), (key998, -2), (key1199, 6), (key1127, -2), (key1199, -2), (key1019, -2)]

def rawRow16138 : Integer.Sparse Key := [(key1041, -2), (key1076, -2), (key1033, -2), (key1033, 6), (key1193, -2), (key1212, -2), (key1190, -2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1190, -2), (key998, -2), (key1111, -2), (key1199, 6), (key1199, -2), (key1019, -2), (key1127, -2)]

def rawRow16139 : Integer.Sparse Key := [(key1076, -2), (key1041, -2), (key1033, -2), (key1033, 6), (key1212, -2), (key1193, -2), (key1190, -2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1190, -2), (key1111, -2), (key998, -2), (key1199, 6), (key1199, -2), (key1127, -2), (key1019, -2)]

def rawRow16140 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1127, 6), (key1033, -2), (key1033, -2), (key1076, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1019, -2), (key1199, -2), (key1199, -2), (key1041, 6), (key1006, -2), (key1193, -2), (key1193, -2)]

def rawRow16141 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1127, 6), (key1033, -2), (key1076, -2), (key1033, -2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1199, -2), (key1019, -2), (key1199, -2), (key1041, 6), (key1193, -2), (key1006, -2), (key1193, -2)]

def rawRow16142 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1127, 6), (key1076, -2), (key1033, -2), (key1033, -2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1199, -2), (key1199, -2), (key1019, -2), (key1041, 6), (key1193, -2), (key1193, -2), (key1006, -2)]

def rawRow16143 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1155, -2), (key1111, 6), (key1190, -2), (key1199, -2), (key1212, -2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1193, 6), (key1006, -2), (key1041, -2), (key1193, -2)]

def rawRow16144 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1155, -2), (key1111, 6), (key1199, -2), (key1190, -2), (key1212, -2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1193, 6), (key1006, -2), (key1193, -2), (key1041, -2)]

def rawRow16145 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1127, -2), (key1111, 6), (key1190, -2), (key1212, -2), (key1199, -2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1193, 6), (key1041, -2), (key1006, -2), (key1193, -2)]

def rawRow16146 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1127, -2), (key1111, 6), (key1212, -2), (key1190, -2), (key1199, -2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1193, 6), (key1041, -2), (key1193, -2), (key1006, -2)]

def rawRow16147 : Integer.Sparse Key := [(key1127, -2), (key1155, -2), (key1111, -2), (key1111, 6), (key1199, -2), (key1212, -2), (key1190, -2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1193, 6), (key1193, -2), (key1006, -2), (key1041, -2)]

def rawRow16148 : Integer.Sparse Key := [(key1155, -2), (key1127, -2), (key1111, -2), (key1111, 6), (key1212, -2), (key1199, -2), (key1190, -2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1193, 6), (key1193, -2), (key1041, -2), (key1006, -2)]

def rawRow16149 : Integer.Sparse Key := [(key1190, -2), (key1193, -2), (key1212, -2), (key1199, 6), (key1033, -2), (key1041, -2), (key1076, -2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key1019, -2), (key1127, -2), (key1199, -2), (key1033, 6), (key998, -2), (key1111, -2), (key1190, -2)]

def rawRow16150 : Integer.Sparse Key := [(key1193, -2), (key1190, -2), (key1212, -2), (key1199, 6), (key1041, -2), (key1033, -2), (key1076, -2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key1019, -2), (key1199, -2), (key1127, -2), (key1033, 6), (key998, -2), (key1190, -2), (key1111, -2)]

def rawRow16151 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1193, -2), (key1199, 6), (key1033, -2), (key1076, -2), (key1041, -2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1127, -2), (key1019, -2), (key1199, -2), (key1033, 6), (key1111, -2), (key998, -2), (key1190, -2)]

def rawRow16152 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1193, -2), (key1199, 6), (key1076, -2), (key1033, -2), (key1041, -2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1127, -2), (key1199, -2), (key1019, -2), (key1033, 6), (key1111, -2), (key1190, -2), (key998, -2)]

def rawRow16153 : Integer.Sparse Key := [(key1193, -2), (key1212, -2), (key1190, -2), (key1199, 6), (key1041, -2), (key1076, -2), (key1033, -2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1199, -2), (key1019, -2), (key1127, -2), (key1033, 6), (key1190, -2), (key998, -2), (key1111, -2)]

def rawRow16154 : Integer.Sparse Key := [(key1212, -2), (key1193, -2), (key1190, -2), (key1199, 6), (key1076, -2), (key1041, -2), (key1033, -2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1199, -2), (key1127, -2), (key1019, -2), (key1033, 6), (key1190, -2), (key1111, -2), (key998, -2)]

def rawRow16155 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1212, -2), (key1193, 6), (key1111, -2), (key1127, -2), (key1155, -2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key1006, -2), (key1041, -2), (key1193, -2), (key1111, 6), (key998, -2), (key1033, -2), (key1190, -2)]

def rawRow16156 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1212, -2), (key1193, 6), (key1127, -2), (key1111, -2), (key1155, -2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key1006, -2), (key1193, -2), (key1041, -2), (key1111, 6), (key998, -2), (key1190, -2), (key1033, -2)]

def rawRow16157 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1199, -2), (key1193, 6), (key1111, -2), (key1155, -2), (key1127, -2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1041, -2), (key1006, -2), (key1193, -2), (key1111, 6), (key1033, -2), (key998, -2), (key1190, -2)]

def rawRow16158 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1199, -2), (key1193, 6), (key1155, -2), (key1111, -2), (key1127, -2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1041, -2), (key1193, -2), (key1006, -2), (key1111, 6), (key1033, -2), (key1190, -2), (key998, -2)]

def rawRow16159 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1190, -2), (key1193, 6), (key1127, -2), (key1155, -2), (key1111, -2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1193, -2), (key1006, -2), (key1041, -2), (key1111, 6), (key1190, -2), (key998, -2), (key1033, -2)]

def rawRow16160 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1190, -2), (key1193, 6), (key1155, -2), (key1127, -2), (key1111, -2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1193, -2), (key1041, -2), (key1006, -2), (key1111, 6), (key1190, -2), (key1033, -2), (key998, -2)]

def rawRow16161 : Integer.Sparse Key := [(key1193, -2), (key1199, -2), (key1212, -2), (key1190, 6), (key1193, -2), (key1199, -2), (key1212, -2), (key1006, 2), (key1019, 2), (key1041, 2), (key1127, 2), (key1076, 2), (key1155, 2), (key998, -2), (key1033, -2), (key1111, -2), (key1190, 6), (key998, -2), (key1033, -2), (key1111, -2)]

def rawRow16162 : Integer.Sparse Key := [(key1199, -2), (key1193, -2), (key1212, -2), (key1190, 6), (key1199, -2), (key1193, -2), (key1212, -2), (key1019, 2), (key1006, 2), (key1127, 2), (key1041, 2), (key1155, 2), (key1076, 2), (key998, -2), (key1111, -2), (key1033, -2), (key1190, 6), (key998, -2), (key1111, -2), (key1033, -2)]

def rawRow16163 : Integer.Sparse Key := [(key1193, -2), (key1212, -2), (key1199, -2), (key1190, 6), (key1193, -2), (key1212, -2), (key1199, -2), (key1041, 2), (key1076, 2), (key1006, 2), (key1155, 2), (key1019, 2), (key1127, 2), (key1033, -2), (key998, -2), (key1111, -2), (key1190, 6), (key1033, -2), (key998, -2), (key1111, -2)]

def rawRow16164 : Integer.Sparse Key := [(key1212, -2), (key1193, -2), (key1199, -2), (key1190, 6), (key1212, -2), (key1193, -2), (key1199, -2), (key1076, 2), (key1041, 2), (key1155, 2), (key1006, 2), (key1127, 2), (key1019, 2), (key1033, -2), (key1111, -2), (key998, -2), (key1190, 6), (key1033, -2), (key1111, -2), (key998, -2)]

def rawRow16165 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1193, -2), (key1190, 6), (key1199, -2), (key1212, -2), (key1193, -2), (key1127, 2), (key1155, 2), (key1019, 2), (key1076, 2), (key1006, 2), (key1041, 2), (key1111, -2), (key998, -2), (key1033, -2), (key1190, 6), (key1111, -2), (key998, -2), (key1033, -2)]

def rawRow16166 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1193, -2), (key1190, 6), (key1212, -2), (key1199, -2), (key1193, -2), (key1155, 2), (key1127, 2), (key1076, 2), (key1019, 2), (key1041, 2), (key1006, 2), (key1111, -2), (key1033, -2), (key998, -2), (key1190, 6), (key1111, -2), (key1033, -2), (key998, -2)]

def rawRow16167 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2408, 6), (key2847, -2), (key2847, -2), (key3020, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2596, -2), (key2884, -2), (key2884, -2), (key2917, 6), (key2605, -2), (key2926, -2), (key2926, -2)]

def rawRow16168 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 6), (key2847, -2), (key3020, -2), (key2847, -2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2884, -2), (key2596, -2), (key2884, -2), (key2917, 6), (key2926, -2), (key2605, -2), (key2926, -2)]

def rawRow16169 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2408, 6), (key3020, -2), (key2847, -2), (key2847, -2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2884, -2), (key2884, -2), (key2596, -2), (key2917, 6), (key2926, -2), (key2926, -2), (key2605, -2)]

def rawRow16170 : Integer.Sparse Key := [(key2402, -2), (key2408, -2), (key2439, -2), (key2402, 6), (key2878, -2), (key2884, -2), (key3029, -2), (key2591, 2), (key2596, 2), (key2847, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key2591, -2), (key2847, -2), (key2878, -2), (key2926, 6), (key2605, -2), (key2917, -2), (key2926, -2)]

def rawRow16171 : Integer.Sparse Key := [(key2408, -2), (key2402, -2), (key2439, -2), (key2402, 6), (key2884, -2), (key2878, -2), (key3029, -2), (key2596, 2), (key2591, 2), (key2884, 2), (key2847, 2), (key3029, 2), (key3020, 2), (key2591, -2), (key2878, -2), (key2847, -2), (key2926, 6), (key2605, -2), (key2926, -2), (key2917, -2)]

def rawRow16172 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2408, -2), (key2402, 6), (key2878, -2), (key3029, -2), (key2884, -2), (key2847, 2), (key3020, 2), (key2591, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2847, -2), (key2591, -2), (key2878, -2), (key2926, 6), (key2917, -2), (key2605, -2), (key2926, -2)]

def rawRow16173 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2408, -2), (key2402, 6), (key3029, -2), (key2878, -2), (key2884, -2), (key3020, 2), (key2847, 2), (key3029, 2), (key2591, 2), (key2884, 2), (key2596, 2), (key2847, -2), (key2878, -2), (key2591, -2), (key2926, 6), (key2917, -2), (key2926, -2), (key2605, -2)]

def rawRow16174 : Integer.Sparse Key := [(key2408, -2), (key2439, -2), (key2402, -2), (key2402, 6), (key2884, -2), (key3029, -2), (key2878, -2), (key2884, 2), (key3029, 2), (key2596, 2), (key3020, 2), (key2591, 2), (key2847, 2), (key2878, -2), (key2591, -2), (key2847, -2), (key2926, 6), (key2926, -2), (key2605, -2), (key2917, -2)]

def rawRow16175 : Integer.Sparse Key := [(key2439, -2), (key2408, -2), (key2402, -2), (key2402, 6), (key3029, -2), (key2884, -2), (key2878, -2), (key3029, 2), (key2884, 2), (key3020, 2), (key2596, 2), (key2847, 2), (key2591, 2), (key2878, -2), (key2847, -2), (key2591, -2), (key2926, 6), (key2926, -2), (key2917, -2), (key2605, -2)]

def rawRow16176 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2505, -2), (key2481, 6), (key2402, -2), (key2402, -2), (key2439, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2605, -2), (key2926, -2), (key2926, -2), (key2775, 6), (key2596, -2), (key2884, -2), (key2884, -2)]

def rawRow16177 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2468, -2), (key2481, 6), (key2402, -2), (key2439, -2), (key2402, -2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2926, -2), (key2605, -2), (key2926, -2), (key2775, 6), (key2884, -2), (key2596, -2), (key2884, -2)]

def rawRow16178 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2468, -2), (key2481, 6), (key2439, -2), (key2402, -2), (key2402, -2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2926, -2), (key2926, -2), (key2605, -2), (key2775, 6), (key2884, -2), (key2884, -2), (key2596, -2)]

def rawRow16179 : Integer.Sparse Key := [(key2468, -2), (key2481, -2), (key2505, -2), (key2468, 6), (key2535, -2), (key2542, -2), (key2553, -2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2591, -2), (key2770, -2), (key2878, -2), (key2884, 6), (key2596, -2), (key2775, -2), (key2884, -2)]

def rawRow16180 : Integer.Sparse Key := [(key2481, -2), (key2468, -2), (key2505, -2), (key2468, 6), (key2542, -2), (key2535, -2), (key2553, -2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2591, -2), (key2878, -2), (key2770, -2), (key2884, 6), (key2596, -2), (key2884, -2), (key2775, -2)]

def rawRow16181 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2481, -2), (key2468, 6), (key2535, -2), (key2553, -2), (key2542, -2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2770, -2), (key2591, -2), (key2878, -2), (key2884, 6), (key2775, -2), (key2596, -2), (key2884, -2)]

def rawRow16182 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2481, -2), (key2468, 6), (key2553, -2), (key2535, -2), (key2542, -2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2770, -2), (key2878, -2), (key2591, -2), (key2884, 6), (key2775, -2), (key2884, -2), (key2596, -2)]

def rawRow16183 : Integer.Sparse Key := [(key2481, -2), (key2505, -2), (key2468, -2), (key2468, 6), (key2542, -2), (key2553, -2), (key2535, -2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2878, -2), (key2591, -2), (key2770, -2), (key2884, 6), (key2884, -2), (key2596, -2), (key2775, -2)]

def rawRow16184 : Integer.Sparse Key := [(key2505, -2), (key2481, -2), (key2468, -2), (key2468, 6), (key2553, -2), (key2542, -2), (key2535, -2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2878, -2), (key2770, -2), (key2591, -2), (key2884, 6), (key2884, -2), (key2775, -2), (key2596, -2)]

def rawRow16185 : Integer.Sparse Key := [(key2535, -2), (key2537, -2), (key2553, -2), (key2542, 6), (key2402, -2), (key2408, -2), (key2439, -2), (key2374, 2), (key2380, 2), (key2468, 2), (key2537, 2), (key2505, 2), (key2553, 2), (key2391, -2), (key2481, -2), (key2542, -2), (key2770, 6), (key2591, -2), (key2847, -2), (key2878, -2)]

def rawRow16186 : Integer.Sparse Key := [(key2537, -2), (key2535, -2), (key2553, -2), (key2542, 6), (key2408, -2), (key2402, -2), (key2439, -2), (key2380, 2), (key2374, 2), (key2537, 2), (key2468, 2), (key2553, 2), (key2505, 2), (key2391, -2), (key2542, -2), (key2481, -2), (key2770, 6), (key2591, -2), (key2878, -2), (key2847, -2)]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow160 : Integer.Sparse Key := [(key1899, -1), (key1896, -1), (key1896, 2), (key1920, 1), (key1918, 1), (key1918, -1), (key1903, -1), (key1926, -2), (key1926, 1), (key1911, 1), (key1354, 1), (key1351, 1), (key1351, -2), (key1683, -1), (key1681, -1), (key1681, 1), (key1472, 1), (key1689, 2), (key1689, -1), (key1480, -1), (key1326, -1), (key1318, -1), (key1318, 1), (key1298, 1), (key1556, 1), (key1548, 1), (key1548, -1), (key1393, -1), (key1633, -1), (key1593, -1), (key1633, 1), (key1444, 1), (key1312, 2), (key1312, -1), (key1292, -1), (key1542, -2), (key1542, 1), (key1387, 1), (key1618, 1), (key1569, 1), (key1618, -1), (key1420, -1)]

def rawRow161 : Integer.Sparse Key := [(key1903, -1), (key1903, -1), (key1911, 2), (key1896, 1), (key1896, 1), (key1926, -1), (key1926, -1), (key1899, -2), (key1920, 1), (key1920, 1), (key1472, 1), (key1472, 1), (key1480, -2), (key1351, -1), (key1351, -1), (key1689, 1), (key1689, 1), (key1354, 2), (key1683, -1), (key1683, -1), (key1393, -1), (key1393, -1), (key1444, 1), (key1444, 1), (key1298, 1), (key1298, 1), (key1593, -1), (key1593, -1), (key1326, -1), (key1326, -1), (key1556, 1), (key1556, 1), (key1387, 2), (key1420, -1), (key1420, -1), (key1292, -2), (key1569, 1), (key1569, 1), (key1312, 1), (key1312, 1), (key1542, -1), (key1542, -1)]

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

def rawRow1475 : Integer.Sparse Key := [(key184, -2), (key164, -2), (key164, -2), (key164, 6), (key148, 2), (key87, 2), (key87, 2), (key87, -2), (key87, -2), (key4, -2), (key84, -6), (key84, 2), (key84, 2), (key1, 2)]

def rawRow1476 : Integer.Sparse Key := [(key2672, -2), (key2749, -2), (key2749, -2), (key2675, 1), (key2675, 1), (key2730, 1), (key2730, 1), (key2751, 1), (key2751, 1), (key2787, 2), (key2906, 2), (key2906, 2), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, -1), (key2915, -1), (key2940, -1), (key2940, -1), (key2985, -1), (key2985, -1), (key3001, -1), (key3001, -1), (key2945, 1), (key2945, 1), (key2962, 1), (key2962, 1), (key3004, 1), (key3004, 1)]

def rawRow1477 : Integer.Sparse Key := [(key2749, -2), (key2672, -2), (key2749, -2), (key2730, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, 1), (key2730, 1), (key2906, 2), (key2787, 2), (key2906, 2), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2985, -1), (key3001, -1), (key2940, -1), (key3001, -1), (key2940, -1), (key2985, -1), (key2962, 1), (key3004, 1), (key2945, 1), (key3004, 1), (key2945, 1), (key2962, 1)]

def rawRow1478 : Integer.Sparse Key := [(key2749, -2), (key2749, -2), (key2672, -2), (key2751, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2730, 1), (key2675, 1), (key2906, 2), (key2906, 2), (key2787, 2), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2797, -1), (key3001, -1), (key2985, -1), (key3001, -1), (key2940, -1), (key2985, -1), (key2940, -1), (key3004, 1), (key2962, 1), (key3004, 1), (key2945, 1), (key2962, 1), (key2945, 1)]

def rawRow1479 : Integer.Sparse Key := [(key2675, -2), (key2739, -2), (key2751, -2), (key2672, 1), (key2675, 1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, 1), (key2797, 2), (key2899, 2), (key2915, 2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, -1), (key2906, -1), (key2945, -1), (key2946, -1), (key2978, -1), (key2994, -1), (key2999, -1), (key3004, -1), (key2940, 1), (key2946, 1), (key2952, 1), (key2964, 1), (key2999, 1), (key3001, 1)]

def rawRow1480 : Integer.Sparse Key := [(key2675, -2), (key2751, -2), (key2739, -2), (key2675, 1), (key2672, 1), (key2730, 1), (key2707, 1), (key2749, 1), (key2739, 1), (key2797, 2), (key2915, 2), (key2899, 2), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2899, -1), (key2946, -1), (key2945, -1), (key2994, -1), (key2978, -1), (key3004, -1), (key2999, -1), (key2946, 1), (key2940, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2999, 1)]

def rawRow1481 : Integer.Sparse Key := [(key2739, -2), (key2675, -2), (key2751, -2), (key2707, 1), (key2739, 1), (key2672, 1), (key2749, 1), (key2675, 1), (key2730, 1), (key2899, 2), (key2797, 2), (key2915, 2), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2978, -1), (key2999, -1), (key2945, -1), (key3004, -1), (key2946, -1), (key2994, -1), (key2952, 1), (key2999, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2964, 1)]

def rawRow1482 : Integer.Sparse Key := [(key2739, -2), (key2751, -2), (key2675, -2), (key2739, 1), (key2707, 1), (key2749, 1), (key2672, 1), (key2730, 1), (key2675, 1), (key2899, 2), (key2915, 2), (key2797, 2), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, -1), (key2797, -1), (key2999, -1), (key2978, -1), (key3004, -1), (key2945, -1), (key2994, -1), (key2946, -1), (key2999, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2964, 1), (key2946, 1)]

def rawRow1483 : Integer.Sparse Key := [(key2751, -2), (key2675, -2), (key2739, -2), (key2730, 1), (key2749, 1), (key2675, 1), (key2739, 1), (key2672, 1), (key2707, 1), (key2915, 2), (key2797, 2), (key2899, 2), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, -1), (key2810, -1), (key2994, -1), (key3004, -1), (key2946, -1), (key2999, -1), (key2945, -1), (key2978, -1), (key2964, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2940, 1), (key2952, 1)]

def rawRow1484 : Integer.Sparse Key := [(key2751, -2), (key2739, -2), (key2675, -2), (key2749, 1), (key2730, 1), (key2739, 1), (key2675, 1), (key2707, 1), (key2672, 1), (key2915, 2), (key2899, 2), (key2797, 2), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key3004, -1), (key2994, -1), (key2999, -1), (key2946, -1), (key2978, -1), (key2945, -1), (key3001, 1), (key2964, 1), (key2999, 1), (key2946, 1), (key2952, 1), (key2940, 1)]

def rawRow1485 : Integer.Sparse Key := [(key2707, -2), (key2978, -2), (key2978, -2), (key2730, 1), (key2730, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1), (key2672, 2), (key2749, 2), (key2749, 2), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, -1), (key3004, -1), (key2675, -1), (key2675, -1), (key2730, -1), (key2730, -1), (key2751, -1), (key2751, -1), (key2797, 1), (key2797, 1), (key2833, 1), (key2833, 1), (key2915, 1), (key2915, 1)]

def rawRow1486 : Integer.Sparse Key := [(key2978, -2), (key2707, -2), (key2978, -2), (key2985, 1), (key2994, 1), (key2730, 1), (key2994, 1), (key2730, 1), (key2985, 1), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2730, -1), (key2751, -1), (key2675, -1), (key2751, -1), (key2675, -1), (key2730, -1), (key2833, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2833, 1)]

def rawRow1487 : Integer.Sparse Key := [(key2978, -2), (key2978, -2), (key2707, -2), (key2994, 1), (key2985, 1), (key2994, 1), (key2730, 1), (key2985, 1), (key2730, 1), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2945, -1), (key2751, -1), (key2730, -1), (key2751, -1), (key2675, -1), (key2730, -1), (key2675, -1), (key2915, 1), (key2833, 1), (key2915, 1), (key2797, 1), (key2833, 1), (key2797, 1)]

def rawRow1488 : Integer.Sparse Key := [(key2739, -2), (key2899, -2), (key2999, -2), (key2749, 1), (key2751, 1), (key2906, 1), (key3001, 1), (key2915, 1), (key3004, 1), (key2675, 2), (key2797, 2), (key2946, 2), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, -1), (key2994, -1), (key2672, -1), (key2675, -1), (key2707, -1), (key2730, -1), (key2739, -1), (key2749, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2833, 1), (key2899, 1), (key2906, 1)]

def rawRow1489 : Integer.Sparse Key := [(key2739, -2), (key2999, -2), (key2899, -2), (key2751, 1), (key2749, 1), (key3001, 1), (key2906, 1), (key3004, 1), (key2915, 1), (key2675, 2), (key2946, 2), (key2797, 2), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2915, -1), (key2675, -1), (key2672, -1), (key2730, -1), (key2707, -1), (key2749, -1), (key2739, -1), (key2797, 1), (key2787, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2899, 1)]

def rawRow1490 : Integer.Sparse Key := [(key2899, -2), (key2739, -2), (key2999, -2), (key2906, 1), (key2915, 1), (key2749, 1), (key3004, 1), (key2751, 1), (key3001, 1), (key2797, 2), (key2675, 2), (key2946, 2), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2707, -1), (key2739, -1), (key2672, -1), (key2749, -1), (key2675, -1), (key2730, -1), (key2810, 1), (key2899, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2833, 1)]

def rawRow1491 : Integer.Sparse Key := [(key2899, -2), (key2999, -2), (key2739, -2), (key2915, 1), (key2906, 1), (key3004, 1), (key2749, 1), (key3001, 1), (key2751, 1), (key2797, 2), (key2946, 2), (key2675, 2), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, -1), (key2751, -1), (key2739, -1), (key2707, -1), (key2749, -1), (key2672, -1), (key2730, -1), (key2675, -1), (key2899, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2833, 1), (key2797, 1)]

def rawRow1492 : Integer.Sparse Key := [(key2999, -2), (key2739, -2), (key2899, -2), (key3001, 1), (key3004, 1), (key2751, 1), (key2915, 1), (key2749, 1), (key2906, 1), (key2946, 2), (key2675, 2), (key2797, 2), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, -1), (key2833, -1), (key2730, -1), (key2749, -1), (key2675, -1), (key2739, -1), (key2672, -1), (key2707, -1), (key2833, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2787, 1), (key2810, 1)]

def rawRow1493 : Integer.Sparse Key := [(key2999, -2), (key2899, -2), (key2739, -2), (key3004, 1), (key3001, 1), (key2915, 1), (key2751, 1), (key2906, 1), (key2749, 1), (key2946, 2), (key2797, 2), (key2675, 2), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2749, -1), (key2730, -1), (key2739, -1), (key2675, -1), (key2707, -1), (key2672, -1), (key2906, 1), (key2833, 1), (key2899, 1), (key2797, 1), (key2810, 1), (key2787, 1)]

def rawRow1494 : Integer.Sparse Key := [(key1314, -6), (key1294, 2), (key1335, 2), (key1335, 2), (key1544, 6), (key1389, -2), (key1770, -2), (key1770, -2), (key1571, -2), (key1653, -2), (key1653, -2), (key1422, 2), (key1811, 2), (key1811, 2)]

def rawRow1495 : Integer.Sparse Key := [(key1314, -6), (key1335, 2), (key1294, 2), (key1335, 2), (key1544, 6), (key1770, -2), (key1389, -2), (key1770, -2), (key1653, -2), (key1571, -2), (key1653, -2), (key1811, 2), (key1422, 2), (key1811, 2)]

def rawRow1496 : Integer.Sparse Key := [(key1314, -6), (key1335, 2), (key1335, 2), (key1294, 2), (key1544, 6), (key1770, -2), (key1770, -2), (key1389, -2), (key1653, -2), (key1653, -2), (key1571, -2), (key1811, 2), (key1811, 2), (key1422, 2)]

def rawRow1497 : Integer.Sparse Key := [(key1335, -6), (key1294, 2), (key1314, 2), (key1335, 2), (key1770, 6), (key1389, -2), (key1544, -2), (key1770, -2), (key1786, -2), (key1811, -2), (key1838, -2), (key1453, 2), (key1653, 2), (key1838, 2)]

def rawRow1498 : Integer.Sparse Key := [(key1335, -6), (key1294, 2), (key1335, 2), (key1314, 2), (key1770, 6), (key1389, -2), (key1770, -2), (key1544, -2), (key1786, -2), (key1838, -2), (key1811, -2), (key1453, 2), (key1838, 2), (key1653, 2)]

def rawRow1499 : Integer.Sparse Key := [(key1335, -6), (key1314, 2), (key1294, 2), (key1335, 2), (key1770, 6), (key1544, -2), (key1389, -2), (key1770, -2), (key1811, -2), (key1786, -2), (key1838, -2), (key1653, 2), (key1453, 2), (key1838, 2)]

def rawRow1500 : Integer.Sparse Key := [(key1335, -6), (key1314, 2), (key1335, 2), (key1294, 2), (key1770, 6), (key1544, -2), (key1770, -2), (key1389, -2), (key1811, -2), (key1838, -2), (key1786, -2), (key1653, 2), (key1838, 2), (key1453, 2)]

def rawRow1501 : Integer.Sparse Key := [(key1335, -6), (key1335, 2), (key1294, 2), (key1314, 2), (key1770, 6), (key1770, -2), (key1389, -2), (key1544, -2), (key1838, -2), (key1786, -2), (key1811, -2), (key1838, 2), (key1453, 2), (key1653, 2)]

def rawRow1502 : Integer.Sparse Key := [(key1335, -6), (key1335, 2), (key1314, 2), (key1294, 2), (key1770, 6), (key1770, -2), (key1544, -2), (key1389, -2), (key1838, -2), (key1811, -2), (key1786, -2), (key1838, 2), (key1653, 2), (key1453, 2)]

def rawRow1503 : Integer.Sparse Key := [(key1544, -6), (key1571, 2), (key1653, 2), (key1653, 2), (key1314, 6), (key1422, -2), (key1811, -2), (key1811, -2), (key1294, -2), (key1335, -2), (key1335, -2), (key1389, 2), (key1770, 2), (key1770, 2)]

def rawRow1504 : Integer.Sparse Key := [(key1544, -6), (key1653, 2), (key1571, 2), (key1653, 2), (key1314, 6), (key1811, -2), (key1422, -2), (key1811, -2), (key1335, -2), (key1294, -2), (key1335, -2), (key1770, 2), (key1389, 2), (key1770, 2)]

def rawRow1505 : Integer.Sparse Key := [(key1544, -6), (key1653, 2), (key1653, 2), (key1571, 2), (key1314, 6), (key1811, -2), (key1811, -2), (key1422, -2), (key1335, -2), (key1335, -2), (key1294, -2), (key1770, 2), (key1770, 2), (key1389, 2)]

def rawRow1506 : Integer.Sparse Key := [(key1653, -6), (key1544, 2), (key1571, 2), (key1653, 2), (key1811, 6), (key1314, -2), (key1422, -2), (key1811, -2), (key1770, -2), (key1786, -2), (key1838, -2), (key1335, 2), (key1453, 2), (key1838, 2)]

def rawRow1507 : Integer.Sparse Key := [(key1653, -6), (key1544, 2), (key1653, 2), (key1571, 2), (key1811, 6), (key1314, -2), (key1811, -2), (key1422, -2), (key1770, -2), (key1838, -2), (key1786, -2), (key1335, 2), (key1838, 2), (key1453, 2)]

def rawRow1508 : Integer.Sparse Key := [(key1653, -6), (key1571, 2), (key1544, 2), (key1653, 2), (key1811, 6), (key1422, -2), (key1314, -2), (key1811, -2), (key1786, -2), (key1770, -2), (key1838, -2), (key1453, 2), (key1335, 2), (key1838, 2)]

def rawRow1509 : Integer.Sparse Key := [(key1653, -6), (key1571, 2), (key1653, 2), (key1544, 2), (key1811, 6), (key1422, -2), (key1811, -2), (key1314, -2), (key1786, -2), (key1838, -2), (key1770, -2), (key1453, 2), (key1838, 2), (key1335, 2)]

def rawRow1510 : Integer.Sparse Key := [(key1653, -6), (key1653, 2), (key1544, 2), (key1571, 2), (key1811, 6), (key1811, -2), (key1314, -2), (key1422, -2), (key1838, -2), (key1770, -2), (key1786, -2), (key1838, 2), (key1335, 2), (key1453, 2)]

def rawRow1511 : Integer.Sparse Key := [(key1653, -6), (key1653, 2), (key1571, 2), (key1544, 2), (key1811, 6), (key1811, -2), (key1422, -2), (key1314, -2), (key1838, -2), (key1786, -2), (key1770, -2), (key1838, 2), (key1453, 2), (key1335, 2)]

def rawRow1512 : Integer.Sparse Key := [(key1770, -6), (key1786, 2), (key1811, 2), (key1838, 2), (key1335, 6), (key1453, -2), (key1653, -2), (key1838, -2), (key1294, -2), (key1314, -2), (key1335, -2), (key1389, 2), (key1544, 2), (key1770, 2)]

def rawRow1513 : Integer.Sparse Key := [(key1770, -6), (key1786, 2), (key1838, 2), (key1811, 2), (key1335, 6), (key1453, -2), (key1838, -2), (key1653, -2), (key1294, -2), (key1335, -2), (key1314, -2), (key1389, 2), (key1770, 2), (key1544, 2)]

def rawRow1514 : Integer.Sparse Key := [(key1770, -6), (key1811, 2), (key1786, 2), (key1838, 2), (key1335, 6), (key1653, -2), (key1453, -2), (key1838, -2), (key1314, -2), (key1294, -2), (key1335, -2), (key1544, 2), (key1389, 2), (key1770, 2)]

def rawRow1515 : Integer.Sparse Key := [(key1770, -6), (key1811, 2), (key1838, 2), (key1786, 2), (key1335, 6), (key1653, -2), (key1838, -2), (key1453, -2), (key1314, -2), (key1335, -2), (key1294, -2), (key1544, 2), (key1770, 2), (key1389, 2)]

def rawRow1516 : Integer.Sparse Key := [(key1770, -6), (key1838, 2), (key1786, 2), (key1811, 2), (key1335, 6), (key1838, -2), (key1453, -2), (key1653, -2), (key1335, -2), (key1294, -2), (key1314, -2), (key1770, 2), (key1389, 2), (key1544, 2)]

def rawRow1517 : Integer.Sparse Key := [(key1770, -6), (key1838, 2), (key1811, 2), (key1786, 2), (key1335, 6), (key1838, -2), (key1653, -2), (key1453, -2), (key1335, -2), (key1314, -2), (key1294, -2), (key1770, 2), (key1544, 2), (key1389, 2)]

def rawRow1518 : Integer.Sparse Key := [(key1811, -6), (key1770, 2), (key1786, 2), (key1838, 2), (key1653, 6), (key1335, -2), (key1453, -2), (key1838, -2), (key1544, -2), (key1571, -2), (key1653, -2), (key1314, 2), (key1422, 2), (key1811, 2)]

def rawRow1519 : Integer.Sparse Key := [(key1811, -6), (key1770, 2), (key1838, 2), (key1786, 2), (key1653, 6), (key1335, -2), (key1838, -2), (key1453, -2), (key1544, -2), (key1653, -2), (key1571, -2), (key1314, 2), (key1811, 2), (key1422, 2)]

def rawRow1520 : Integer.Sparse Key := [(key1811, -6), (key1786, 2), (key1770, 2), (key1838, 2), (key1653, 6), (key1453, -2), (key1335, -2), (key1838, -2), (key1571, -2), (key1544, -2), (key1653, -2), (key1422, 2), (key1314, 2), (key1811, 2)]

def rawRow1521 : Integer.Sparse Key := [(key1811, -6), (key1786, 2), (key1838, 2), (key1770, 2), (key1653, 6), (key1453, -2), (key1838, -2), (key1335, -2), (key1571, -2), (key1653, -2), (key1544, -2), (key1422, 2), (key1811, 2), (key1314, 2)]

def rawRow1522 : Integer.Sparse Key := [(key1811, -6), (key1838, 2), (key1770, 2), (key1786, 2), (key1653, 6), (key1838, -2), (key1335, -2), (key1453, -2), (key1653, -2), (key1544, -2), (key1571, -2), (key1811, 2), (key1314, 2), (key1422, 2)]

def rawRow1523 : Integer.Sparse Key := [(key1811, -6), (key1838, 2), (key1786, 2), (key1770, 2), (key1653, 6), (key1838, -2), (key1453, -2), (key1335, -2), (key1653, -2), (key1571, -2), (key1544, -2), (key1811, 2), (key1422, 2), (key1314, 2)]

def rawRow1524 : Integer.Sparse Key := [(key2628, -2), (key2628, -2), (key2641, -2), (key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2706, 2), (key2706, 2), (key2753, 2), (key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2758, -1), (key2758, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2920, -1), (key2920, -1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2923, 1), (key2923, 1)]

def rawRow1525 : Integer.Sparse Key := [(key2628, -2), (key2641, -2), (key2628, -2), (key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2706, 2), (key2753, 2), (key2706, 2), (key2726, -1), (key2758, -1), (key2671, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2860, -1), (key2920, -1), (key2809, -1), (key2920, -1), (key2809, -1), (key2860, -1), (key2870, 1), (key2923, 1), (key2786, 1), (key2923, 1), (key2786, 1), (key2870, 1)]

def rawRow1526 : Integer.Sparse Key := [(key2641, -2), (key2628, -2), (key2628, -2), (key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2753, 2), (key2706, 2), (key2706, 2), (key2758, -1), (key2726, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2920, -1), (key2860, -1), (key2920, -1), (key2809, -1), (key2860, -1), (key2809, -1), (key2923, 1), (key2870, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2786, 1)]

def rawRow1527 : Integer.Sparse Key := [(key2646, -2), (key2648, -2), (key2653, -2), (key2612, 1), (key2618, 1), (key2628, 1), (key2648, 1), (key2641, 1), (key2653, 1), (key2726, 2), (key2732, 2), (key2758, 2), (key2671, -1), (key2676, -1), (key2706, -1), (key2732, -1), (key2753, -1), (key2758, -1), (key2829, -1), (key2835, -1), (key2870, -1), (key2885, -1), (key2923, -1), (key2927, -1), (key2794, 1), (key2798, 1), (key2860, 1), (key2885, 1), (key2920, 1), (key2927, 1)]

def rawRow1528 : Integer.Sparse Key := [(key2648, -2), (key2646, -2), (key2653, -2), (key2618, 1), (key2612, 1), (key2648, 1), (key2628, 1), (key2653, 1), (key2641, 1), (key2732, 2), (key2726, 2), (key2758, 2), (key2676, -1), (key2671, -1), (key2732, -1), (key2706, -1), (key2758, -1), (key2753, -1), (key2835, -1), (key2829, -1), (key2885, -1), (key2870, -1), (key2927, -1), (key2923, -1), (key2798, 1), (key2794, 1), (key2885, 1), (key2860, 1), (key2927, 1), (key2920, 1)]

def rawRow1529 : Integer.Sparse Key := [(key2646, -2), (key2653, -2), (key2648, -2), (key2628, 1), (key2641, 1), (key2612, 1), (key2653, 1), (key2618, 1), (key2648, 1), (key2726, 2), (key2758, 2), (key2732, 2), (key2706, -1), (key2753, -1), (key2671, -1), (key2758, -1), (key2676, -1), (key2732, -1), (key2870, -1), (key2923, -1), (key2829, -1), (key2927, -1), (key2835, -1), (key2885, -1), (key2860, 1), (key2920, 1), (key2794, 1), (key2927, 1), (key2798, 1), (key2885, 1)]

def rawRow1530 : Integer.Sparse Key := [(key2653, -2), (key2646, -2), (key2648, -2), (key2641, 1), (key2628, 1), (key2653, 1), (key2612, 1), (key2648, 1), (key2618, 1), (key2758, 2), (key2726, 2), (key2732, 2), (key2753, -1), (key2706, -1), (key2758, -1), (key2671, -1), (key2732, -1), (key2676, -1), (key2923, -1), (key2870, -1), (key2927, -1), (key2829, -1), (key2885, -1), (key2835, -1), (key2920, 1), (key2860, 1), (key2927, 1), (key2794, 1), (key2885, 1), (key2798, 1)]

def rawRow1531 : Integer.Sparse Key := [(key2648, -2), (key2653, -2), (key2646, -2), (key2648, 1), (key2653, 1), (key2618, 1), (key2641, 1), (key2612, 1), (key2628, 1), (key2732, 2), (key2758, 2), (key2726, 2), (key2732, -1), (key2758, -1), (key2676, -1), (key2753, -1), (key2671, -1), (key2706, -1), (key2885, -1), (key2927, -1), (key2835, -1), (key2923, -1), (key2829, -1), (key2870, -1), (key2885, 1), (key2927, 1), (key2798, 1), (key2920, 1), (key2794, 1), (key2860, 1)]

def rawRow1532 : Integer.Sparse Key := [(key2653, -2), (key2648, -2), (key2646, -2), (key2653, 1), (key2648, 1), (key2641, 1), (key2618, 1), (key2628, 1), (key2612, 1), (key2758, 2), (key2732, 2), (key2726, 2), (key2758, -1), (key2732, -1), (key2753, -1), (key2676, -1), (key2706, -1), (key2671, -1), (key2927, -1), (key2885, -1), (key2923, -1), (key2835, -1), (key2870, -1), (key2829, -1), (key2927, 1), (key2885, 1), (key2920, 1), (key2798, 1), (key2860, 1), (key2794, 1)]

def rawRow1533 : Integer.Sparse Key := [(key2782, -2), (key2782, -2), (key2795, -2), (key2805, 1), (key2805, 1), (key2893, 1), (key2893, 1), (key2897, 1), (key2897, 1), (key2628, 2), (key2628, 2), (key2641, 2), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2976, -1), (key2976, -1), (key2612, -1), (key2616, -1), (key2640, -1), (key2640, -1), (key2660, -1), (key2660, -1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1)]

def rawRow1534 : Integer.Sparse Key := [(key2782, -2), (key2795, -2), (key2782, -2), (key2893, 1), (key2897, 1), (key2805, 1), (key2897, 1), (key2805, 1), (key2893, 1), (key2628, 2), (key2641, 2), (key2628, 2), (key2972, -1), (key2976, -1), (key2702, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2646, -1), (key2653, -1), (key2612, -1), (key2653, -1), (key2616, -1), (key2640, -1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1)]

def rawRow1535 : Integer.Sparse Key := [(key2795, -2), (key2782, -2), (key2782, -2), (key2897, 1), (key2893, 1), (key2897, 1), (key2805, 1), (key2893, 1), (key2805, 1), (key2641, 2), (key2628, 2), (key2628, 2), (key2976, -1), (key2972, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2702, -1), (key2653, -1), (key2646, -1), (key2653, -1), (key2612, -1), (key2640, -1), (key2616, -1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1)]

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

def rawRow1536 : Integer.Sparse Key := [(key2893, -2), (key2897, -2), (key2904, -2), (key2782, 1), (key2795, 1), (key2805, 1), (key2897, 1), (key2831, 1), (key2904, 1), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1)]

def rawRow1537 : Integer.Sparse Key := [(key2897, -2), (key2893, -2), (key2904, -2), (key2795, 1), (key2782, 1), (key2897, 1), (key2805, 1), (key2904, 1), (key2831, 1), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1)]

def rawRow1538 : Integer.Sparse Key := [(key2893, -2), (key2904, -2), (key2897, -2), (key2805, 1), (key2831, 1), (key2782, 1), (key2904, 1), (key2795, 1), (key2897, 1), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1)]

def rawRow1539 : Integer.Sparse Key := [(key2904, -2), (key2893, -2), (key2897, -2), (key2831, 1), (key2805, 1), (key2904, 1), (key2782, 1), (key2897, 1), (key2795, 1), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1)]

def rawRow1540 : Integer.Sparse Key := [(key2897, -2), (key2904, -2), (key2893, -2), (key2897, 1), (key2904, 1), (key2795, 1), (key2831, 1), (key2782, 1), (key2805, 1), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1)]

def rawRow1541 : Integer.Sparse Key := [(key2904, -2), (key2897, -2), (key2893, -2), (key2904, 1), (key2897, 1), (key2831, 1), (key2795, 1), (key2805, 1), (key2782, 1), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

def rawRow1542 : Integer.Sparse Key := [(key2936, -2), (key2938, -2), (key2943, -2), (key2948, 1), (key2950, 1), (key2972, 1), (key2997, 1), (key2976, 1), (key2998, 1), (key2646, 2), (key2648, 2), (key2653, 2), (key2735, -1), (key2737, -1), (key2893, -1), (key2997, -1), (key2897, -1), (key2998, -1), (key2612, -1), (key2618, -1), (key2628, -1), (key2648, -1), (key2641, -1), (key2653, -1), (key2667, 1), (key2673, 1), (key2782, 1), (key2938, 1), (key2795, 1), (key2943, 1)]

def rawRow1543 : Integer.Sparse Key := [(key2938, -2), (key2936, -2), (key2943, -2), (key2950, 1), (key2948, 1), (key2997, 1), (key2972, 1), (key2998, 1), (key2976, 1), (key2648, 2), (key2646, 2), (key2653, 2), (key2737, -1), (key2735, -1), (key2997, -1), (key2893, -1), (key2998, -1), (key2897, -1), (key2618, -1), (key2612, -1), (key2648, -1), (key2628, -1), (key2653, -1), (key2641, -1), (key2673, 1), (key2667, 1), (key2938, 1), (key2782, 1), (key2943, 1), (key2795, 1)]

def rawRow1544 : Integer.Sparse Key := [(key2936, -2), (key2943, -2), (key2938, -2), (key2972, 1), (key2976, 1), (key2948, 1), (key2998, 1), (key2950, 1), (key2997, 1), (key2646, 2), (key2653, 2), (key2648, 2), (key2893, -1), (key2897, -1), (key2735, -1), (key2998, -1), (key2737, -1), (key2997, -1), (key2628, -1), (key2641, -1), (key2612, -1), (key2653, -1), (key2618, -1), (key2648, -1), (key2782, 1), (key2795, 1), (key2667, 1), (key2943, 1), (key2673, 1), (key2938, 1)]

def rawRow1545 : Integer.Sparse Key := [(key2943, -2), (key2936, -2), (key2938, -2), (key2976, 1), (key2972, 1), (key2998, 1), (key2948, 1), (key2997, 1), (key2950, 1), (key2653, 2), (key2646, 2), (key2648, 2), (key2897, -1), (key2893, -1), (key2998, -1), (key2735, -1), (key2997, -1), (key2737, -1), (key2641, -1), (key2628, -1), (key2653, -1), (key2612, -1), (key2648, -1), (key2618, -1), (key2795, 1), (key2782, 1), (key2943, 1), (key2667, 1), (key2938, 1), (key2673, 1)]

def rawRow1546 : Integer.Sparse Key := [(key2938, -2), (key2943, -2), (key2936, -2), (key2997, 1), (key2998, 1), (key2950, 1), (key2976, 1), (key2948, 1), (key2972, 1), (key2648, 2), (key2653, 2), (key2646, 2), (key2997, -1), (key2998, -1), (key2737, -1), (key2897, -1), (key2735, -1), (key2893, -1), (key2648, -1), (key2653, -1), (key2618, -1), (key2641, -1), (key2612, -1), (key2628, -1), (key2938, 1), (key2943, 1), (key2673, 1), (key2795, 1), (key2667, 1), (key2782, 1)]

def rawRow1547 : Integer.Sparse Key := [(key2943, -2), (key2938, -2), (key2936, -2), (key2998, 1), (key2997, 1), (key2976, 1), (key2950, 1), (key2972, 1), (key2948, 1), (key2653, 2), (key2648, 2), (key2646, 2), (key2998, -1), (key2997, -1), (key2897, -1), (key2737, -1), (key2893, -1), (key2735, -1), (key2653, -1), (key2648, -1), (key2641, -1), (key2618, -1), (key2628, -1), (key2612, -1), (key2943, 1), (key2938, 1), (key2795, 1), (key2673, 1), (key2782, 1), (key2667, 1)]

def rawRow1548 : Integer.Sparse Key := [(key2972, -2), (key2976, -2), (key2983, -2), (key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2893, 2), (key2897, 2), (key2904, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1)]

def rawRow1549 : Integer.Sparse Key := [(key2976, -2), (key2972, -2), (key2983, -2), (key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2897, 2), (key2893, 2), (key2904, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1)]

def rawRow1550 : Integer.Sparse Key := [(key2972, -2), (key2983, -2), (key2976, -2), (key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2893, 2), (key2904, 2), (key2897, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1)]

def rawRow1551 : Integer.Sparse Key := [(key2983, -2), (key2972, -2), (key2976, -2), (key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2904, 2), (key2893, 2), (key2897, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1)]

def rawRow1552 : Integer.Sparse Key := [(key2976, -2), (key2983, -2), (key2972, -2), (key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2897, 2), (key2904, 2), (key2893, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1)]

def rawRow1553 : Integer.Sparse Key := [(key2983, -2), (key2976, -2), (key2972, -2), (key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key2904, 2), (key2897, 2), (key2893, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

def rawRow1554 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1019, -2), (key1006, 6), (key1111, 2), (key1111, 2), (key1127, 2), (key1041, -2), (key1193, -2), (key1193, -2), (key1155, -6), (key1076, 2), (key1212, 2), (key1212, 2)]

def rawRow1555 : Integer.Sparse Key := [(key998, -2), (key1019, -2), (key998, -2), (key1006, 6), (key1111, 2), (key1127, 2), (key1111, 2), (key1193, -2), (key1041, -2), (key1193, -2), (key1155, -6), (key1212, 2), (key1076, 2), (key1212, 2)]

def rawRow1556 : Integer.Sparse Key := [(key1019, -2), (key998, -2), (key998, -2), (key1006, 6), (key1127, 2), (key1111, 2), (key1111, 2), (key1193, -2), (key1193, -2), (key1041, -2), (key1155, -6), (key1212, 2), (key1212, 2), (key1076, 2)]

def rawRow1557 : Integer.Sparse Key := [(key998, -2), (key1006, -2), (key1019, -2), (key998, 6), (key1190, 2), (key1193, 2), (key1199, 2), (key1033, -2), (key1111, -2), (key1190, -2), (key1212, -6), (key1076, 2), (key1155, 2), (key1212, 2)]

def rawRow1558 : Integer.Sparse Key := [(key1006, -2), (key998, -2), (key1019, -2), (key998, 6), (key1193, 2), (key1190, 2), (key1199, 2), (key1033, -2), (key1190, -2), (key1111, -2), (key1212, -6), (key1076, 2), (key1212, 2), (key1155, 2)]

def rawRow1559 : Integer.Sparse Key := [(key998, -2), (key1019, -2), (key1006, -2), (key998, 6), (key1190, 2), (key1199, 2), (key1193, 2), (key1111, -2), (key1033, -2), (key1190, -2), (key1212, -6), (key1155, 2), (key1076, 2), (key1212, 2)]

def rawRow1560 : Integer.Sparse Key := [(key1019, -2), (key998, -2), (key1006, -2), (key998, 6), (key1199, 2), (key1190, 2), (key1193, 2), (key1111, -2), (key1190, -2), (key1033, -2), (key1212, -6), (key1155, 2), (key1212, 2), (key1076, 2)]

def rawRow1561 : Integer.Sparse Key := [(key1006, -2), (key1019, -2), (key998, -2), (key998, 6), (key1193, 2), (key1199, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key1111, -2), (key1212, -6), (key1212, 2), (key1076, 2), (key1155, 2)]

def rawRow1562 : Integer.Sparse Key := [(key1019, -2), (key1006, -2), (key998, -2), (key998, 6), (key1199, 2), (key1193, 2), (key1190, 2), (key1190, -2), (key1111, -2), (key1033, -2), (key1212, -6), (key1212, 2), (key1155, 2), (key1076, 2)]

def rawRow1563 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1127, -2), (key1155, 6), (key998, 2), (key998, 2), (key1019, 2), (key1076, -2), (key1212, -2), (key1212, -2), (key1006, -6), (key1041, 2), (key1193, 2), (key1193, 2)]

def rawRow1564 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1111, -2), (key1155, 6), (key998, 2), (key1019, 2), (key998, 2), (key1212, -2), (key1076, -2), (key1212, -2), (key1006, -6), (key1193, 2), (key1041, 2), (key1193, 2)]

def rawRow1565 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1111, -2), (key1155, 6), (key1019, 2), (key998, 2), (key998, 2), (key1212, -2), (key1212, -2), (key1076, -2), (key1006, -6), (key1193, 2), (key1193, 2), (key1041, 2)]

def rawRow1566 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1155, -2), (key1111, 6), (key1190, 2), (key1199, 2), (key1212, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1193, -6), (key1006, 2), (key1041, 2), (key1193, 2)]

def rawRow1567 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1155, -2), (key1111, 6), (key1199, 2), (key1190, 2), (key1212, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1193, -6), (key1006, 2), (key1193, 2), (key1041, 2)]

def rawRow1568 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1127, -2), (key1111, 6), (key1190, 2), (key1212, 2), (key1199, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1193, -6), (key1041, 2), (key1006, 2), (key1193, 2)]

def rawRow1569 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1127, -2), (key1111, 6), (key1212, 2), (key1190, 2), (key1199, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1193, -6), (key1041, 2), (key1193, 2), (key1006, 2)]

def rawRow1570 : Integer.Sparse Key := [(key1127, -2), (key1155, -2), (key1111, -2), (key1111, 6), (key1199, 2), (key1212, 2), (key1190, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1193, -6), (key1193, 2), (key1006, 2), (key1041, 2)]

def rawRow1571 : Integer.Sparse Key := [(key1155, -2), (key1127, -2), (key1111, -2), (key1111, 6), (key1212, 2), (key1199, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1193, -6), (key1193, 2), (key1041, 2), (key1006, 2)]

def rawRow1572 : Integer.Sparse Key := [(key1190, -2), (key1193, -2), (key1199, -2), (key1212, 6), (key998, 2), (key1006, 2), (key1019, 2), (key1076, -2), (key1155, -2), (key1212, -2), (key998, -6), (key1033, 2), (key1111, 2), (key1190, 2)]

def rawRow1573 : Integer.Sparse Key := [(key1193, -2), (key1190, -2), (key1199, -2), (key1212, 6), (key1006, 2), (key998, 2), (key1019, 2), (key1076, -2), (key1212, -2), (key1155, -2), (key998, -6), (key1033, 2), (key1190, 2), (key1111, 2)]

def rawRow1574 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1193, -2), (key1212, 6), (key998, 2), (key1019, 2), (key1006, 2), (key1155, -2), (key1076, -2), (key1212, -2), (key998, -6), (key1111, 2), (key1033, 2), (key1190, 2)]

def rawRow1575 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1193, -2), (key1212, 6), (key1019, 2), (key998, 2), (key1006, 2), (key1155, -2), (key1212, -2), (key1076, -2), (key998, -6), (key1111, 2), (key1190, 2), (key1033, 2)]

def rawRow1576 : Integer.Sparse Key := [(key1193, -2), (key1199, -2), (key1190, -2), (key1212, 6), (key1006, 2), (key1019, 2), (key998, 2), (key1212, -2), (key1076, -2), (key1155, -2), (key998, -6), (key1190, 2), (key1033, 2), (key1111, 2)]

def rawRow1577 : Integer.Sparse Key := [(key1199, -2), (key1193, -2), (key1190, -2), (key1212, 6), (key1019, 2), (key1006, 2), (key998, 2), (key1212, -2), (key1155, -2), (key1076, -2), (key998, -6), (key1190, 2), (key1111, 2), (key1033, 2)]

def rawRow1578 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1212, -2), (key1193, 6), (key1111, 2), (key1127, 2), (key1155, 2), (key1006, -2), (key1041, -2), (key1193, -2), (key1111, -6), (key998, 2), (key1033, 2), (key1190, 2)]

def rawRow1579 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1212, -2), (key1193, 6), (key1127, 2), (key1111, 2), (key1155, 2), (key1006, -2), (key1193, -2), (key1041, -2), (key1111, -6), (key998, 2), (key1190, 2), (key1033, 2)]

def rawRow1580 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1199, -2), (key1193, 6), (key1111, 2), (key1155, 2), (key1127, 2), (key1041, -2), (key1006, -2), (key1193, -2), (key1111, -6), (key1033, 2), (key998, 2), (key1190, 2)]

def rawRow1581 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1199, -2), (key1193, 6), (key1155, 2), (key1111, 2), (key1127, 2), (key1041, -2), (key1193, -2), (key1006, -2), (key1111, -6), (key1033, 2), (key1190, 2), (key998, 2)]

def rawRow1582 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1190, -2), (key1193, 6), (key1127, 2), (key1155, 2), (key1111, 2), (key1193, -2), (key1006, -2), (key1041, -2), (key1111, -6), (key1190, 2), (key998, 2), (key1033, 2)]

def rawRow1583 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1190, -2), (key1193, 6), (key1155, 2), (key1127, 2), (key1111, 2), (key1193, -2), (key1041, -2), (key1006, -2), (key1111, -6), (key1190, 2), (key1033, 2), (key998, 2)]

def rawRow1584 : Integer.Sparse Key := [(key2631, -6), (key2615, 2), (key2639, 2), (key2639, 2), (key2705, 6), (key2670, -2), (key2725, -2), (key2725, -2), (key2808, -2), (key2859, -2), (key2859, -2), (key2785, 2), (key2869, 2), (key2869, 2)]

def rawRow1585 : Integer.Sparse Key := [(key2631, -6), (key2639, 2), (key2615, 2), (key2639, 2), (key2705, 6), (key2725, -2), (key2670, -2), (key2725, -2), (key2859, -2), (key2808, -2), (key2859, -2), (key2869, 2), (key2785, 2), (key2869, 2)]

def rawRow1586 : Integer.Sparse Key := [(key2631, -6), (key2639, 2), (key2639, 2), (key2615, 2), (key2705, 6), (key2725, -2), (key2725, -2), (key2670, -2), (key2859, -2), (key2859, -2), (key2808, -2), (key2869, 2), (key2869, 2), (key2785, 2)]

def rawRow1587 : Integer.Sparse Key := [(key2639, -6), (key2615, 2), (key2631, 2), (key2639, 2), (key2725, 6), (key2670, -2), (key2705, -2), (key2725, -2), (key2828, -2), (key2869, -2), (key2879, -2), (key2793, 2), (key2859, 2), (key2879, 2)]

def rawRow1588 : Integer.Sparse Key := [(key2639, -6), (key2615, 2), (key2639, 2), (key2631, 2), (key2725, 6), (key2670, -2), (key2725, -2), (key2705, -2), (key2828, -2), (key2879, -2), (key2869, -2), (key2793, 2), (key2879, 2), (key2859, 2)]

def rawRow1589 : Integer.Sparse Key := [(key2639, -6), (key2631, 2), (key2615, 2), (key2639, 2), (key2725, 6), (key2705, -2), (key2670, -2), (key2725, -2), (key2869, -2), (key2828, -2), (key2879, -2), (key2859, 2), (key2793, 2), (key2879, 2)]

def rawRow1590 : Integer.Sparse Key := [(key2639, -6), (key2631, 2), (key2639, 2), (key2615, 2), (key2725, 6), (key2705, -2), (key2725, -2), (key2670, -2), (key2869, -2), (key2879, -2), (key2828, -2), (key2859, 2), (key2879, 2), (key2793, 2)]

def rawRow1591 : Integer.Sparse Key := [(key2639, -6), (key2639, 2), (key2615, 2), (key2631, 2), (key2725, 6), (key2725, -2), (key2670, -2), (key2705, -2), (key2879, -2), (key2828, -2), (key2869, -2), (key2879, 2), (key2793, 2), (key2859, 2)]

def rawRow1592 : Integer.Sparse Key := [(key2639, -6), (key2639, 2), (key2631, 2), (key2615, 2), (key2725, 6), (key2725, -2), (key2705, -2), (key2670, -2), (key2879, -2), (key2869, -2), (key2828, -2), (key2879, 2), (key2859, 2), (key2793, 2)]

def rawRow1593 : Integer.Sparse Key := [(key2705, -6), (key2808, 2), (key2859, 2), (key2859, 2), (key2631, 6), (key2785, -2), (key2869, -2), (key2869, -2), (key2615, -2), (key2639, -2), (key2639, -2), (key2670, 2), (key2725, 2), (key2725, 2)]

def rawRow1594 : Integer.Sparse Key := [(key2705, -6), (key2859, 2), (key2808, 2), (key2859, 2), (key2631, 6), (key2869, -2), (key2785, -2), (key2869, -2), (key2639, -2), (key2615, -2), (key2639, -2), (key2725, 2), (key2670, 2), (key2725, 2)]

def rawRow1595 : Integer.Sparse Key := [(key2705, -6), (key2859, 2), (key2859, 2), (key2808, 2), (key2631, 6), (key2869, -2), (key2869, -2), (key2785, -2), (key2639, -2), (key2639, -2), (key2615, -2), (key2725, 2), (key2725, 2), (key2670, 2)]

def rawRow1596 : Integer.Sparse Key := [(key2859, -6), (key2705, 2), (key2808, 2), (key2859, 2), (key2869, 6), (key2631, -2), (key2785, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, 2), (key2793, 2), (key2879, 2)]

def rawRow1597 : Integer.Sparse Key := [(key2859, -6), (key2705, 2), (key2859, 2), (key2808, 2), (key2869, 6), (key2631, -2), (key2869, -2), (key2785, -2), (key2725, -2), (key2879, -2), (key2828, -2), (key2639, 2), (key2879, 2), (key2793, 2)]

def rawRow1598 : Integer.Sparse Key := [(key2859, -6), (key2808, 2), (key2705, 2), (key2859, 2), (key2869, 6), (key2785, -2), (key2631, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, 2), (key2639, 2), (key2879, 2)]

def rawRow1599 : Integer.Sparse Key := [(key2859, -6), (key2808, 2), (key2859, 2), (key2705, 2), (key2869, 6), (key2785, -2), (key2869, -2), (key2631, -2), (key2828, -2), (key2879, -2), (key2725, -2), (key2793, 2), (key2879, 2), (key2639, 2)]

def rawRow1600 : Integer.Sparse Key := [(key2859, -6), (key2859, 2), (key2705, 2), (key2808, 2), (key2869, 6), (key2869, -2), (key2631, -2), (key2785, -2), (key2879, -2), (key2725, -2), (key2828, -2), (key2879, 2), (key2639, 2), (key2793, 2)]

def rawRow1601 : Integer.Sparse Key := [(key2859, -6), (key2859, 2), (key2808, 2), (key2705, 2), (key2869, 6), (key2869, -2), (key2785, -2), (key2631, -2), (key2879, -2), (key2828, -2), (key2725, -2), (key2879, 2), (key2793, 2), (key2639, 2)]

def rawRow1602 : Integer.Sparse Key := [(key2725, -6), (key2828, 2), (key2869, 2), (key2879, 2), (key2639, 6), (key2793, -2), (key2859, -2), (key2879, -2), (key2615, -2), (key2631, -2), (key2639, -2), (key2670, 2), (key2705, 2), (key2725, 2)]

def rawRow1603 : Integer.Sparse Key := [(key2725, -6), (key2828, 2), (key2879, 2), (key2869, 2), (key2639, 6), (key2793, -2), (key2879, -2), (key2859, -2), (key2615, -2), (key2639, -2), (key2631, -2), (key2670, 2), (key2725, 2), (key2705, 2)]

def rawRow1604 : Integer.Sparse Key := [(key2725, -6), (key2869, 2), (key2828, 2), (key2879, 2), (key2639, 6), (key2859, -2), (key2793, -2), (key2879, -2), (key2631, -2), (key2615, -2), (key2639, -2), (key2705, 2), (key2670, 2), (key2725, 2)]

def rawRow1605 : Integer.Sparse Key := [(key2725, -6), (key2869, 2), (key2879, 2), (key2828, 2), (key2639, 6), (key2859, -2), (key2879, -2), (key2793, -2), (key2631, -2), (key2639, -2), (key2615, -2), (key2705, 2), (key2725, 2), (key2670, 2)]

def rawRow1606 : Integer.Sparse Key := [(key2725, -6), (key2879, 2), (key2828, 2), (key2869, 2), (key2639, 6), (key2879, -2), (key2793, -2), (key2859, -2), (key2639, -2), (key2615, -2), (key2631, -2), (key2725, 2), (key2670, 2), (key2705, 2)]

def rawRow1607 : Integer.Sparse Key := [(key2725, -6), (key2879, 2), (key2869, 2), (key2828, 2), (key2639, 6), (key2879, -2), (key2859, -2), (key2793, -2), (key2639, -2), (key2631, -2), (key2615, -2), (key2725, 2), (key2705, 2), (key2670, 2)]

def rawRow1608 : Integer.Sparse Key := [(key2869, -6), (key2725, 2), (key2828, 2), (key2879, 2), (key2859, 6), (key2639, -2), (key2793, -2), (key2879, -2), (key2705, -2), (key2808, -2), (key2859, -2), (key2631, 2), (key2785, 2), (key2869, 2)]

def rawRow1609 : Integer.Sparse Key := [(key2869, -6), (key2725, 2), (key2879, 2), (key2828, 2), (key2859, 6), (key2639, -2), (key2879, -2), (key2793, -2), (key2705, -2), (key2859, -2), (key2808, -2), (key2631, 2), (key2869, 2), (key2785, 2)]

def rawRow1610 : Integer.Sparse Key := [(key2869, -6), (key2828, 2), (key2725, 2), (key2879, 2), (key2859, 6), (key2793, -2), (key2639, -2), (key2879, -2), (key2808, -2), (key2705, -2), (key2859, -2), (key2785, 2), (key2631, 2), (key2869, 2)]

def rawRow1611 : Integer.Sparse Key := [(key2869, -6), (key2828, 2), (key2879, 2), (key2725, 2), (key2859, 6), (key2793, -2), (key2879, -2), (key2639, -2), (key2808, -2), (key2859, -2), (key2705, -2), (key2785, 2), (key2869, 2), (key2631, 2)]

def rawRow1612 : Integer.Sparse Key := [(key2869, -6), (key2879, 2), (key2725, 2), (key2828, 2), (key2859, 6), (key2879, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, 2), (key2631, 2), (key2785, 2)]

def rawRow1613 : Integer.Sparse Key := [(key2869, -6), (key2879, 2), (key2828, 2), (key2725, 2), (key2859, 6), (key2879, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, 2), (key2785, 2), (key2631, 2)]

def rawRow1614 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1781, -1), (key1781, -1), (key1398, 2), (key1775, 2), (key1775, 2), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1818, 1), (key1818, 1), (key1458, -1), (key1458, -1), (key1791, -1), (key1791, -1), (key1840, -1), (key1840, -1), (key1448, -2), (key1826, -2), (key1826, -2), (key1467, 1), (key1467, 1), (key1799, 1), (key1799, 1), (key1845, 1), (key1845, 1)]

def rawRow1615 : Integer.Sparse Key := [(key1772, -1), (key1781, -1), (key1391, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1775, 2), (key1398, 2), (key1775, 2), (key1813, 1), (key1818, 1), (key1424, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1791, -1), (key1840, -1), (key1458, -1), (key1840, -1), (key1458, -1), (key1791, -1), (key1826, -2), (key1448, -2), (key1826, -2), (key1799, 1), (key1845, 1), (key1467, 1), (key1845, 1), (key1467, 1), (key1799, 1)]

def rawRow1616 : Integer.Sparse Key := [(key1781, -1), (key1772, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1775, 2), (key1775, 2), (key1398, 2), (key1818, 1), (key1813, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1424, 1), (key1840, -1), (key1791, -1), (key1840, -1), (key1458, -1), (key1791, -1), (key1458, -1), (key1826, -2), (key1826, -2), (key1448, -2), (key1845, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1799, 1), (key1467, 1)]

def rawRow1617 : Integer.Sparse Key := [(key1391, -1), (key1398, -1), (key1546, -1), (key1775, -1), (key1560, -1), (key1781, -1), (key1391, 2), (key1546, 2), (key1772, 2), (key1455, 1), (key1458, 1), (key1655, 1), (key1840, 1), (key1660, 1), (key1842, 1), (key1424, -1), (key1455, -1), (key1573, -1), (key1788, -1), (key1655, -1), (key1813, -1), (key1467, -2), (key1668, -2), (key1845, -2), (key1448, 1), (key1467, 1), (key1597, 1), (key1799, 1), (key1668, 1), (key1826, 1)]

def rawRow1618 : Integer.Sparse Key := [(key1398, -1), (key1391, -1), (key1775, -1), (key1546, -1), (key1781, -1), (key1560, -1), (key1391, 2), (key1772, 2), (key1546, 2), (key1458, 1), (key1455, 1), (key1840, 1), (key1655, 1), (key1842, 1), (key1660, 1), (key1455, -1), (key1424, -1), (key1788, -1), (key1573, -1), (key1813, -1), (key1655, -1), (key1467, -2), (key1845, -2), (key1668, -2), (key1467, 1), (key1448, 1), (key1799, 1), (key1597, 1), (key1826, 1), (key1668, 1)]

end MUB6.Certificate.GramRows

end OAI
end


