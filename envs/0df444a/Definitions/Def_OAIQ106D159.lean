-- Prove2me | Definitions.Def_OAIQ106D159
-- name    : OAIQ106D159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:07:16.37719+00:00
-- url     : https://prove2.me/theorems/06bd7610-81a7-4577-a29e-8e8ab773aa63
-- title:
--   Definitions bundle OAIQ106D159 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 638 declarations of OpenAI's Lean: 638 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow13572`, `OAI.MUB6.Certificate.GramRows.rawRow13573`, `OAI.MUB6.Certificate.GramRows.rawRow13574`, `OAI.MUB6.Certificate.GramRows.rawRow13575`, `OAI.MUB6.Certificate.GramRows.rawRow13576`, `OAI.MUB6.Certificate.GramRows.rawRow13577`, `OAI.MUB6.Certificate.GramRows.rawRow13578`, `OAI.MUB6.Certificate.GramRows.rawRow13579`, `OAI.MUB6.Certificate.GramRows.rawRow1358`, `OAI.MUB6.Certificate.GramRows.rawRow13580`, `OAI.MUB6.Certificate.GramRows.rawRow13581`, `OAI.MUB6.Certificate.GramRows.rawRow13582`, `OAI.MUB6.Certificate.GramRows.rawRow13583`, `OAI.MUB6.Certificate.GramRows.rawRow13584`, `OAI.MUB6.Certificate.GramRows.rawRow13585`, `OAI.MUB6.Certificate.GramRows.rawRow13586`, `OAI.MUB6.Certificate.GramRows.rawRow13587`, `OAI.MUB6.Certificate.GramRows.rawRow13588`, `OAI.MUB6.Certificate.GramRows.rawRow13589`, `OAI.MUB6.Certificate.GramRows.rawRow1359`, `OAI.MUB6.Certificate.GramRows.rawRow13590`, `OAI.MUB6.Certificate.GramRows.rawRow13591`, `OAI.MUB6.Certificate.GramRows.rawRow13592`, `OAI.MUB6.Certificate.GramRows.rawRow136`, `OAI.MUB6.Certificate.GramRows.rawRow1360`, `OAI.MUB6.Certificate.GramRows.rawRow1361`, `OAI.MUB6.Certificate.GramRows.rawRow1362`, `OAI.MUB6.Certificate.GramRows.rawRow13629`, `OAI.MUB6.Certificate.GramRows.rawRow1363`, `OAI.MUB6.Certificate.GramRows.rawRow13630`, `OAI.MUB6.Certificate.GramRows.rawRow13631`, `OAI.MUB6.Certificate.GramRows.rawRow13632`, `OAI.MUB6.Certificate.GramRows.rawRow13633`, `OAI.MUB6.Certificate.GramRows.rawRow13634`, `OAI.MUB6.Certificate.GramRows.rawRow13635`, `OAI.MUB6.Certificate.GramRows.rawRow13636`, `OAI.MUB6.Certificate.GramRows.rawRow13637`, `OAI.MUB6.Certificate.GramRows.rawRow13638`, `OAI.MUB6.Certificate.GramRows.rawRow13639`, `OAI.MUB6.Certificate.GramRows.rawRow1364` and 598 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block1.lean), [`MutuallyUnbiased_GramRows_Block130`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block130.lean), [`MutuallyUnbiased_GramRows_Block131`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block131.lean), [`MutuallyUnbiased_GramRows_Block132`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block132.lean), [`MutuallyUnbiased_GramRows_Block133`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block133.lean), [`MutuallyUnbiased_GramRows_Block134`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block134.lean), [`MutuallyUnbiased_GramRows_Block135`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block135.lean), [`MutuallyUnbiased_GramRows_Block34`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block34.lean), [`MutuallyUnbiased_GramRows_Block35`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block35.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
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

def rawRow136 : Integer.Sparse Key := [(key1387, -1), (key1393, -1), (key1393, 2), (key1420, 1), (key1426, 1), (key1426, -1), (key1472, -1), (key1444, -2), (key1444, 1), (key1480, 1), (key1292, 1), (key1298, 1), (key1298, -2), (key1569, -1), (key1575, -1), (key1575, 1), (key1903, 1), (key1593, 2), (key1593, -1), (key1911, -1), (key1312, -1), (key1318, -1), (key1318, 1), (key1351, 1), (key1542, 1), (key1548, 1), (key1548, -1), (key1896, -1), (key1633, -1), (key1689, -1), (key1633, 1), (key1926, 1), (key1326, 2), (key1326, -1), (key1354, -1), (key1556, -2), (key1556, 1), (key1899, 1), (key1624, 1), (key1683, 1), (key1624, -1), (key1920, -1)]

def rawRow137 : Integer.Sparse Key := [(key1393, -1), (key1387, -1), (key1393, 2), (key1426, 1), (key1420, 1), (key1472, -1), (key1426, -1), (key1444, -2), (key1480, 1), (key1444, 1), (key1298, 1), (key1292, 1), (key1298, -2), (key1575, -1), (key1569, -1), (key1903, 1), (key1575, 1), (key1593, 2), (key1911, -1), (key1593, -1), (key1318, -1), (key1312, -1), (key1351, 1), (key1318, 1), (key1548, 1), (key1542, 1), (key1896, -1), (key1548, -1), (key1689, -1), (key1633, -1), (key1926, 1), (key1633, 1), (key1326, 2), (key1354, -1), (key1326, -1), (key1556, -2), (key1899, 1), (key1556, 1), (key1683, 1), (key1624, 1), (key1920, -1), (key1624, -1)]

def rawRow139 : Integer.Sparse Key := [(key1420, -1), (key1426, -1), (key1444, 2), (key1387, 1), (key1393, 1), (key1444, -1), (key1480, -1), (key1393, -2), (key1426, 1), (key1472, 1), (key1569, 1), (key1575, 1), (key1593, -2), (key1292, -1), (key1298, -1), (key1593, 1), (key1911, 1), (key1298, 2), (key1575, -1), (key1903, -1), (key1542, -1), (key1548, -1), (key1633, 1), (key1689, 1), (key1312, 1), (key1318, 1), (key1633, -1), (key1926, -1), (key1318, -1), (key1351, -1), (key1548, 1), (key1896, 1), (key1556, 2), (key1624, -1), (key1683, -1), (key1326, -2), (key1624, 1), (key1920, 1), (key1326, 1), (key1354, 1), (key1556, -1), (key1899, -1)]

def rawRow140 : Integer.Sparse Key := [(key1426, -1), (key1420, -1), (key1444, 2), (key1393, 1), (key1387, 1), (key1480, -1), (key1444, -1), (key1393, -2), (key1472, 1), (key1426, 1), (key1575, 1), (key1569, 1), (key1593, -2), (key1298, -1), (key1292, -1), (key1911, 1), (key1593, 1), (key1298, 2), (key1903, -1), (key1575, -1), (key1548, -1), (key1542, -1), (key1689, 1), (key1633, 1), (key1318, 1), (key1312, 1), (key1926, -1), (key1633, -1), (key1351, -1), (key1318, -1), (key1896, 1), (key1548, 1), (key1556, 2), (key1683, -1), (key1624, -1), (key1326, -2), (key1920, 1), (key1624, 1), (key1354, 1), (key1326, 1), (key1899, -1), (key1556, -1)]

def rawRow141 : Integer.Sparse Key := [(key1426, -1), (key1444, -1), (key1420, 2), (key1472, 1), (key1480, 1), (key1387, -1), (key1420, -1), (key1472, -2), (key1393, 1), (key1426, 1), (key1575, 1), (key1593, 1), (key1569, -2), (key1903, -1), (key1911, -1), (key1292, 1), (key1569, 1), (key1903, 2), (key1298, -1), (key1575, -1), (key1681, -1), (key1689, -1), (key1542, 1), (key1618, 1), (key1918, 1), (key1926, 1), (key1312, -1), (key1618, -1), (key1896, -1), (key1918, -1), (key1351, 1), (key1681, 1), (key1683, 2), (key1556, -1), (key1624, -1), (key1920, -2), (key1326, 1), (key1624, 1), (key1899, 1), (key1920, 1), (key1354, -1), (key1683, -1)]

def rawRow142 : Integer.Sparse Key := [(key1444, -1), (key1426, -1), (key1420, 2), (key1480, 1), (key1472, 1), (key1420, -1), (key1387, -1), (key1472, -2), (key1426, 1), (key1393, 1), (key1593, 1), (key1575, 1), (key1569, -2), (key1911, -1), (key1903, -1), (key1569, 1), (key1292, 1), (key1903, 2), (key1575, -1), (key1298, -1), (key1689, -1), (key1681, -1), (key1618, 1), (key1542, 1), (key1926, 1), (key1918, 1), (key1618, -1), (key1312, -1), (key1918, -1), (key1896, -1), (key1681, 1), (key1351, 1), (key1683, 2), (key1624, -1), (key1556, -1), (key1920, -2), (key1624, 1), (key1326, 1), (key1920, 1), (key1899, 1), (key1683, -1), (key1354, -1)]

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

def rawRow14241 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1069, -2), (key1034, 6), (key1107, -2), (key1112, -2), (key1148, -2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key999, -2), (key1112, -2), (key1191, -2), (key1121, 6), (key1013, -2), (key1121, -2), (key1197, -2)]

def rawRow14242 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1069, -2), (key1034, 6), (key1112, -2), (key1107, -2), (key1148, -2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key999, -2), (key1191, -2), (key1112, -2), (key1121, 6), (key1013, -2), (key1197, -2), (key1121, -2)]

def rawRow14243 : Integer.Sparse Key := [(key1029, -2), (key1069, -2), (key1034, -2), (key1034, 6), (key1107, -2), (key1148, -2), (key1112, -2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1112, -2), (key999, -2), (key1191, -2), (key1121, 6), (key1121, -2), (key1013, -2), (key1197, -2)]

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

end MUB6.Certificate.GramRows

end OAI
end


