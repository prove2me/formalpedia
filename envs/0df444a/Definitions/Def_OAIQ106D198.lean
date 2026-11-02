-- Prove2me | Definitions.Def_OAIQ106D198
-- name    : OAIQ106D198
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:09:30.434801+00:00
-- url     : https://prove2.me/theorems/ed7f8372-8aa1-4e90-ae3f-135de578450c
-- title:
--   Definitions bundle OAIQ106D198 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 125 declarations of OpenAI's Lean: 125 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows2_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows2_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows3_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows3_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows3_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows3_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows4_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows4_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows4_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows4_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows4_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows5_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows5_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows5_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows5_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows5_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows5_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows6_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows7_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_7` and 85 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block1Row2`, `MutuallyUnbiased_GramEntries_Block1Row3`, `MutuallyUnbiased_GramEntries_Block1Row4`, `MutuallyUnbiased_GramEntries_Block1Row5`, `MutuallyUnbiased_GramEntries_Block1Row6`, `MutuallyUnbiased_GramEntries_Block1Row7`, `MutuallyUnbiased_GramEntries_Block1Row8`, `MutuallyUnbiased_GramEntries_Block1Row9`, `MutuallyUnbiased_GramEntries_Block2Row0`, `MutuallyUnbiased_GramEntries_Block2Row1`, `MutuallyUnbiased_GramEntries_Block2Row10`, `MutuallyUnbiased_GramEntries_Block2Row2`, `MutuallyUnbiased_GramEntries_Block2Row3`, `MutuallyUnbiased_GramEntries_Block2Row4`, `MutuallyUnbiased_GramEntries_Block2Row5`, `MutuallyUnbiased_GramEntries_Block2Row6`, `MutuallyUnbiased_GramEntries_Block2Row7`, `MutuallyUnbiased_GramEntries_Block2Row8`, `MutuallyUnbiased_GramEntries_Block3Row11`, `MutuallyUnbiased_GramFunctions_Block1`, `MutuallyUnbiased_GramFunctions_Block2`, `MutuallyUnbiased_GramFunctions_Block3`.
--
--   **Imports.** It imports the bundles `OAIQ106D142`, `OAIQ106D143`, `OAIQ106D144`, `OAIQ106D145`, `OAIQ106D146`, `OAIQ106D147` and `OAIQ106D148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D201`; the statements `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval0_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D142
import Definitions.Def_OAIQ106D143
import Definitions.Def_OAIQ106D144
import Definitions.Def_OAIQ106D145
import Definitions.Def_OAIQ106D146
import Definitions.Def_OAIQ106D147
import Definitions.Def_OAIQ106D148

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block1

def form3 : LinearForm := ⟨14, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨14, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨30, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨14, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨30, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨14, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨30, fun k => terms9[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_1 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row718, row719, row720, row721, row722, row723, row724, row725, row726, row727, row728, row729, row730, row731, row732, row733, row734, row735, row736, row737, row738, row739, row740, row741, row742, row743, row744, row745, row746, row747]

def rows2_2 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row748, row749, row750, row751, row752, row753, row754, row755, row756, row757, row758, row759, row760, row761, row762, row763, row764, row765, row766, row767, row768, row769, row770, row771, row772, row773, row774, row775, row776, row777]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row778, row779, row780, row781, row782, row783, row784, row785, row786, row787, row788, row789, row790, row791]

def rows3_1 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row792, row793, row794, row795, row796, row797, row798, row799, row800, row801, row802, row803, row804, row805]

def rows3_2 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row806, row807, row808, row809, row810, row811, row812, row813, row814, row815, row816, row817, row818, row819]

def rows3_3 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row820, row821, row822, row823, row824, row825, row826, row827, row828, row829, row830, row831, row832, row833]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row834, row835, row836, row837, row838, row839, row840, row841, row842, row843, row844, row845, row846, row847]

def rows4_1 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row848, row849, row850, row851, row852, row853, row854, row855, row856, row857, row858, row859, row860, row861]

def rows4_2 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row862, row863, row864, row865, row866, row867, row868, row869, row870, row871, row872, row873, row874, row875]

def rows4_3 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row876, row877, row878, row879, row880, row881, row882, row883, row884, row885, row886, row887, row888, row889]

def rows4_4 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row890, row891, row892, row893, row894, row895, row896, row897, row898, row899, row900, row901, row902, row903]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row904, row905, row906, row907, row908, row909, row910, row911, row912, row913, row914, row915, row916, row917, row918, row919, row920, row921, row922, row923, row924, row925, row926, row927, row928, row929, row930, row931, row932, row933]

def rows5_1 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row934, row935, row936, row937, row938, row939, row940, row941, row942, row943, row944, row945, row946, row947, row948, row949, row950, row951, row952, row953, row954, row955, row956, row957, row958, row959, row960, row961, row962, row963]

def rows5_2 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row964, row965, row966, row967, row968, row969, row970, row971, row972, row973, row974, row975, row976, row977, row978, row979, row980, row981, row982, row983, row984, row985, row986, row987, row988, row989, row990, row991, row992, row993]

def rows5_3 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row994, row995, row996, row997, row998, row999, row1000, row1001, row1002, row1003, row1004, row1005, row1006, row1007, row1008, row1009, row1010, row1011, row1012, row1013, row1014, row1015, row1016, row1017, row1018, row1019, row1020, row1021, row1022, row1023]

def rows5_4 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row1024, row1025, row1026, row1027, row1028, row1029, row1030, row1031, row1032, row1033, row1034, row1035, row1036, row1037, row1038, row1039, row1040, row1041, row1042, row1043, row1044, row1045, row1046, row1047, row1048, row1049, row1050, row1051, row1052, row1053]

def rows5_5 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row1054, row1055, row1056, row1057, row1058, row1059, row1060, row1061, row1062, row1063, row1064, row1065, row1066, row1067, row1068, row1069, row1070, row1071, row1072, row1073, row1074, row1075, row1076, row1077, row1078, row1079, row1080, row1081, row1082, row1083]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1084, row1085, row1086, row1087, row1088, row1089, row1090, row1091, row1092, row1093, row1094, row1095, row1096, row1097]

def rows6_1 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1098, row1099, row1100, row1101, row1102, row1103, row1104, row1105, row1106, row1107, row1108, row1109, row1110, row1111]

def rows6_2 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1112, row1113, row1114, row1115, row1116, row1117, row1118, row1119, row1120, row1121, row1122, row1123, row1124, row1125]

def rows6_3 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1126, row1127, row1128, row1129, row1130, row1131, row1132, row1133, row1134, row1135, row1136, row1137, row1138, row1139]

def rows6_4 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1140, row1141, row1142, row1143, row1144, row1145, row1146, row1147, row1148, row1149, row1150, row1151, row1152, row1153]

def rows6_5 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1154, row1155, row1156, row1157, row1158, row1159, row1160, row1161, row1162, row1163, row1164, row1165, row1166, row1167]

def rows6_6 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1168, row1169, row1170, row1171, row1172, row1173, row1174, row1175, row1176, row1177, row1178, row1179, row1180, row1181]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1182, row1183, row1184, row1185, row1186, row1187, row1188, row1189, row1190, row1191, row1192, row1193, row904, row905, row906, row907, row908, row909, row1194, row1195, row1196, row1197, row1198, row1199, row913, row914, row915, row916, row917, row918]

def rows7_1 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1200, row1201, row1202, row1203, row1204, row1205, row1206, row1207, row1208, row1209, row1210, row1211, row934, row935, row936, row937, row938, row939, row1212, row1213, row1214, row1215, row1216, row1217, row943, row944, row945, row946, row947, row948]

def rows7_2 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1218, row1219, row1220, row1221, row1222, row1223, row1224, row1225, row1226, row1227, row1228, row1229, row964, row965, row966, row967, row968, row969, row1230, row1231, row1232, row1233, row1234, row1235, row973, row974, row975, row976, row977, row978]

def rows7_3 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1236, row1237, row1238, row1239, row1240, row1241, row1242, row1243, row1244, row1245, row1246, row1247, row994, row995, row996, row997, row998, row999, row1248, row1249, row1250, row1251, row1252, row1253, row1003, row1004, row1005, row1006, row1007, row1008]

def rows7_4 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1254, row1255, row1256, row1257, row1258, row1259, row1260, row1261, row1262, row1263, row1264, row1265, row1024, row1025, row1026, row1027, row1028, row1029, row1266, row1267, row1268, row1269, row1270, row1271, row1033, row1034, row1035, row1036, row1037, row1038]

def rows7_5 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1272, row1273, row1274, row1275, row1276, row1277, row1278, row1279, row1280, row1281, row1282, row1283, row1054, row1055, row1056, row1057, row1058, row1059, row1284, row1285, row1286, row1287, row1288, row1289, row1063, row1064, row1065, row1066, row1067, row1068]

def rows7_6 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1290, row1291, row1292, row1293, row1294, row1295, row1296, row1297, row1298, row1299, row1300, row1301, row1302, row1303, row1304, row1305, row1306, row1307, row1308, row1309, row1310, row1311, row1312, row1313, row1314, row1315, row1316, row1317, row1318, row1319]

def rows7_7 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1320, row1321, row1322, row1323, row1324, row1325, row1326, row1327, row1328, row1329, row1330, row1331, row1332, row1333, row1334, row1335, row1336, row1337, row1338, row1339, row1340, row1341, row1342, row1343, row1344, row1345, row1346, row1347, row1348, row1349]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1350, row1351, row1352, row1353, row1354, row1355, row1356, row1357, row1358, row1359, row1360, row1361, row1362, row1363]

def rows8_1 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1364, row1365, row1366, row1367, row1368, row1369, row1370, row1371, row1372, row1373, row1374, row1375, row1376, row1377]

def rows8_2 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1378, row1379, row1380, row1381, row1382, row1383, row1384, row1385, row1386, row1387, row1388, row1389, row1390, row1391]

def rows8_3 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1392, row1393, row1394, row1395, row1396, row1397, row1398, row1399, row1400, row1401, row1402, row1403, row1404, row1405]

def rows8_4 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1406, row1407, row1408, row1409, row1410, row1411, row1412, row1413, row1414, row1415, row1416, row1417, row1418, row1419]

def rows8_5 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1420, row1421, row1422, row1423, row1424, row1425, row1426, row1427, row1428, row1429, row1430, row1431, row1432, row1433]

def rows8_6 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1434, row1435, row1436, row1437, row1438, row1439, row1440, row1441, row1442, row1443, row1444, row1445, row1446, row1447]

def rows8_7 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1448, row1449, row1450, row1451, row1452, row1453, row1454, row1455, row1456, row1457, row1458, row1459, row1460, row1461]

def rows8_8 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1462, row1463, row1464, row1465, row1466, row1467, row1468, row1469, row1470, row1471, row1472, row1473, row1474, row1475]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1476, row1477, row1478, row1479, row1480, row1481, row1482, row1483, row1484, row1485, row1486, row1487, row642, row643, row644, row645, row646, row647, row1488, row1489, row1490, row1491, row1492, row1493, row654, row655, row656, row657, row658, row659]

def rows9_1 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1494, row1495, row1496, row1497, row1498, row1499, row1500, row1501, row1502, row1503, row1504, row1505, row1506, row1507, row1508, row1509, row1510, row1511, row1512, row1513, row1514, row1515, row1516, row1517, row1518, row1519, row1520, row1521, row1522, row1523]

def rows9_2 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1524, row1525, row1526, row1527, row1528, row1529, row1530, row1531, row1532, row1533, row1534, row1535, row1536, row1537, row1538, row1539, row1540, row1541, row1542, row1543, row1544, row1545, row1546, row1547, row1548, row1549, row1550, row1551, row1552, row1553]

def rows9_3 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1554, row1555, row1556, row1557, row1558, row1559, row1560, row1561, row1562, row1563, row1564, row1565, row1566, row1567, row1568, row1569, row1570, row1571, row1572, row1573, row1574, row1575, row1576, row1577, row1578, row1579, row1580, row1581, row1582, row1583]

def rows9_4 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1584, row1585, row1586, row1587, row1588, row1589, row1590, row1591, row1592, row1593, row1594, row1595, row1596, row1597, row1598, row1599, row1600, row1601, row1602, row1603, row1604, row1605, row1606, row1607, row1608, row1609, row1610, row1611, row1612, row1613]

def rows9_5 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1614, row1615, row1616, row1617, row1618, row1619, row1620, row1621, row1622, row1623, row1624, row1625, row1626, row1627, row1628, row1629, row1630, row1631, row1632, row1633, row1634, row1635, row1636, row1637, row1638, row1639, row1640, row1641, row1642, row1643]

def rows9_6 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1644, row1645, row1646, row1647, row1648, row1649, row1650, row1651, row1652, row1653, row1654, row1655, row1656, row1657, row1658, row1659, row1660, row1661, row1662, row1663, row1664, row1665, row1666, row1667, row1668, row1669, row1670, row1671, row1672, row1673]

def rows9_7 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1674, row1675, row1676, row1677, row1678, row1679, row1680, row1681, row1682, row1683, row1684, row1685, row1686, row1687, row1688, row1689, row1690, row1691, row1692, row1693, row1694, row1695, row1696, row1697, row1698, row1699, row1700, row1701, row1702, row1703]

def rows9_8 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1704, row1705, row1706, row1707, row1708, row1709, row1710, row1711, row1712, row1713, row1714, row1715, row1716, row1717, row1718, row1719, row1720, row1721, row1722, row1723, row1724, row1725, row1726, row1727, row1728, row1729, row1730, row1731, row1732, row1733]

def rows9_9 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1734, row1735, row1736, row1737, row1738, row1739, row1740, row1741, row1742, row1743, row1744, row1745, row1746, row1747, row1748, row1749, row1750, row1751, row1752, row1753, row1754, row1755, row1756, row1757, row1758, row1759, row1760, row1761, row1762, row1763]

end MUB6.Certificate.GramEntries.Block1

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

def form0 : LinearForm := ⟨40, fun k => terms0[k.val]!⟩

def form1 : LinearForm := ⟨40, fun k => terms1[k.val]!⟩

def form2 : LinearForm := ⟨40, fun k => terms2[k.val]!⟩

def form3 : LinearForm := ⟨30, fun k => terms3[k.val]!⟩

def form4 : LinearForm := ⟨30, fun k => terms4[k.val]!⟩

def form5 : LinearForm := ⟨40, fun k => terms5[k.val]!⟩

def form6 : LinearForm := ⟨40, fun k => terms6[k.val]!⟩

def form7 : LinearForm := ⟨40, fun k => terms7[k.val]!⟩

def form8 : LinearForm := ⟨40, fun k => terms8[k.val]!⟩

def form9 : LinearForm := ⟨30, fun k => terms9[k.val]!⟩

def form10 : LinearForm := ⟨30, fun k => terms10[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block2.form0.size → Integer.Sparse Key := ![row5148, row5149, row5150, row5151, row5152, row5153, row5154, row5155, row5156, row5157, row5158, row5159, row5160, row5161, row5162, row5163, row5164, row5165, row5166, row5167, row5168, row5169, row5170, row5171, row5172, row5173, row5174, row5175, row5176, row5177, row5178, row5179, row5180, row5181, row5182, row5183, row5184, row5185, row5186, row5187]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block2.form1.size → Integer.Sparse Key := ![row5188, row5189, row5190, row5191, row5192, row5193, row5194, row5195, row5196, row5197, row5198, row5199, row5200, row5201, row5202, row5203, row5204, row5205, row5206, row5207, row5208, row5209, row5210, row5211, row5212, row5213, row5214, row5215, row5216, row5217, row5218, row5219, row5220, row5221, row5222, row5223, row5224, row5225, row5226, row5227]

def rows1_1 : Fin GramFunctions.Block2.form1.size → Integer.Sparse Key := ![row5228, row5229, row5230, row5231, row5232, row5233, row5234, row5235, row5236, row5237, row5238, row5239, row5240, row5241, row5242, row5243, row5244, row5245, row5246, row5247, row5248, row5249, row5250, row5251, row5252, row5253, row5254, row5255, row5256, row5257, row5258, row5259, row5260, row5261, row5262, row5263, row5264, row5265, row5266, row5267]

end MUB6.Certificate.GramEntries.Block2

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

def form0 : LinearForm := ⟨24, fun k => terms0[k.val]!⟩

def form10 : LinearForm := ⟨16, fun k => terms10[k.val]!⟩

def form11 : LinearForm := ⟨8, fun k => terms11[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7018, row7019, row7020, row7021, row7022, row7023, row7024, row7025, row7026, row7027, row7028, row7029, row7030, row7031, row7032, row7033, row7034, row7035, row7036, row7037, row7038, row7039, row7040, row7041, row7042, row7043, row7044, row7045, row7046, row7047]

def rows10_1 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7048, row7049, row7050, row7051, row7052, row7053, row7054, row7055, row7056, row7057, row7058, row7059, row7060, row7061, row7062, row7063, row7064, row7065, row7066, row7067, row7068, row7069, row7070, row7071, row7072, row7073, row7074, row7075, row7076, row7077]

def rows10_2 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7078, row7079, row7080, row7081, row7082, row7083, row7084, row7085, row7086, row7087, row7088, row7089, row7090, row7091, row7092, row7093, row7094, row7095, row7096, row7097, row7098, row7099, row7100, row7101, row7102, row7103, row7104, row7105, row7106, row7107]

def rows10_3 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7108, row7109, row7110, row7111, row7112, row7113, row7114, row7115, row7116, row7117, row7118, row7119, row7120, row7121, row7122, row7123, row7124, row7125, row7126, row7127, row7128, row7129, row7130, row7131, row7132, row7133, row7134, row7135, row7136, row7137]

def rows10_4 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7138, row7139, row7140, row7141, row7142, row7143, row7144, row7145, row7146, row7147, row7148, row7149, row7150, row7151, row7152, row7153, row7154, row7155, row7156, row7157, row7158, row7159, row7160, row7161, row7162, row7163, row7164, row7165, row7166, row7167]

def rows10_5 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7168, row7169, row7170, row7171, row7172, row7173, row7174, row7175, row7176, row7177, row7178, row7179, row7180, row7181, row7182, row7183, row7184, row7185, row7186, row7187, row7188, row7189, row7190, row7191, row7192, row7193, row7194, row7195, row7196, row7197]

def rows10_6 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7198, row7199, row7200, row7201, row7202, row7203, row7204, row7205, row7206, row7207, row7208, row7209, row7210, row7211, row7212, row7213, row7214, row7215, row7216, row7217, row7218, row7219, row7220, row7221, row7222, row7223, row7224, row7225, row7226, row7227]

def rows10_7 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7228, row7229, row7230, row7231, row7232, row7233, row7234, row7235, row7236, row7237, row7238, row7239, row7240, row7241, row7242, row7243, row7244, row7245, row7246, row7247, row7248, row7249, row7250, row7251, row7252, row7253, row7254, row7255, row7256, row7257]

def rows10_8 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7258, row7259, row7260, row7261, row7262, row7263, row7264, row7265, row7266, row7267, row7268, row7269, row7270, row7271, row7272, row7273, row7274, row7275, row7276, row7277, row7278, row7279, row7280, row7281, row7282, row7283, row7284, row7285, row7286, row7287]

def rows10_9 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7288, row7289, row7290, row7291, row7292, row7293, row7294, row7295, row7296, row7297, row7298, row7299, row7300, row7301, row7302, row7303, row7304, row7305, row7306, row7307, row7308, row7309, row7310, row7311, row7312, row7313, row7314, row7315, row7316, row7317]

def rows10_10 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7318, row7319, row7320, row7321, row7322, row7323, row7324, row7325, row7326, row7327, row7328, row7329, row7330, row7331, row7332, row7333, row7334, row7335, row7336, row7337, row7338, row7339, row7340, row7341, row7342, row7343, row7344, row7345, row7346, row7347]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5268, row5269, row5270, row5271, row5272, row5273, row5274, row5275, row5276, row5277, row5278, row5279, row5280, row5281, row5282, row5283, row5284, row5285, row5286, row5287, row5288, row5289, row5290, row5291, row5292, row5293, row5294, row5295, row5296, row5297, row5298, row5299, row5300, row5301, row5302, row5303, row5304, row5305, row5306, row5307]

def rows2_1 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5308, row5309, row5310, row5311, row5312, row5313, row5314, row5315, row5316, row5317, row5318, row5319, row5320, row5321, row5322, row5323, row5324, row5325, row5326, row5327, row5328, row5329, row5330, row5331, row5332, row5333, row5334, row5335, row5336, row5337, row5338, row5339, row5340, row5341, row5342, row5343, row5344, row5345, row5346, row5347]

def rows2_2 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5348, row5349, row5350, row5351, row5352, row5353, row5354, row5355, row5356, row5357, row5358, row5359, row5360, row5361, row5362, row5363, row5364, row5365, row5366, row5367, row5368, row5369, row5370, row5371, row5372, row5373, row5374, row5375, row5376, row5377, row5378, row5379, row5380, row5381, row5382, row5383, row5384, row5385, row5386, row5387]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5388, row5389, row5390, row5391, row5392, row5393, row5394, row5395, row5396, row5397, row5398, row5399, row5400, row5401, row5402, row5403, row5404, row5405, row5406, row5407, row5408, row5409, row5410, row5411, row5412, row5413, row5414, row5415, row5416, row5417]

def rows3_1 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5418, row5419, row5420, row5421, row5422, row5423, row5424, row5425, row5426, row5427, row5428, row5429, row5430, row5431, row5432, row5433, row5434, row5435, row5436, row5437, row5438, row5439, row5440, row5441, row5442, row5443, row5444, row5445, row5446, row5447]

def rows3_2 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5448, row5449, row5450, row5451, row5452, row5453, row5454, row5455, row5456, row5457, row5458, row5459, row5460, row5461, row5462, row5463, row5464, row5465, row5466, row5467, row5468, row5469, row5470, row5471, row5472, row5473, row5474, row5475, row5476, row5477]

def rows3_3 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5478, row5479, row5480, row5481, row5482, row5483, row5484, row5485, row5486, row5487, row5488, row5489, row5490, row5491, row5492, row5493, row5494, row5495, row5496, row5497, row5498, row5499, row5500, row5501, row5502, row5503, row5504, row5505, row5506, row5507]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5508, row5509, row5510, row5511, row5512, row5513, row5514, row5515, row5516, row5517, row5518, row5519, row5520, row5521, row5522, row5523, row5524, row5525, row5526, row5527, row5528, row5529, row5530, row5531, row5532, row5533, row5534, row5535, row5536, row5537]

def rows4_1 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5538, row5539, row5540, row5541, row5542, row5543, row5544, row5545, row5546, row5547, row5548, row5549, row5550, row5551, row5552, row5553, row5554, row5555, row5556, row5557, row5558, row5559, row5560, row5561, row5562, row5563, row5564, row5565, row5566, row5567]

def rows4_2 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5568, row5569, row5570, row5571, row5572, row5573, row5574, row5575, row5576, row5577, row5578, row5579, row5580, row5581, row5582, row5583, row5584, row5585, row5586, row5587, row5588, row5589, row5590, row5591, row5592, row5593, row5594, row5595, row5596, row5597]

def rows4_3 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5598, row5599, row5600, row5601, row5602, row5603, row5604, row5605, row5606, row5607, row5608, row5609, row5610, row5611, row5612, row5613, row5614, row5615, row5616, row5617, row5618, row5619, row5620, row5621, row5622, row5623, row5624, row5625, row5626, row5627]

def rows4_4 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5628, row5629, row5630, row5631, row5632, row5633, row5634, row5635, row5636, row5637, row5638, row5639, row5640, row5641, row5642, row5643, row5644, row5645, row5646, row5647, row5648, row5649, row5650, row5651, row5652, row5653, row5654, row5655, row5656, row5657]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5658, row5659, row5660, row5661, row5662, row5663, row5664, row5665, row5666, row5667, row5668, row5669, row5670, row5671, row5672, row5673, row5674, row5675, row5676, row5677, row5678, row5679, row5680, row5681, row5682, row5683, row5684, row5685, row5686, row5687, row5688, row5689, row5690, row5691, row5692, row5693, row5694, row5695, row5696, row5697]

def rows5_1 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5698, row5699, row5700, row5701, row5702, row5703, row5704, row5705, row5706, row5707, row5708, row5709, row5710, row5711, row5712, row5713, row5714, row5715, row5716, row5717, row5718, row5719, row5720, row5721, row5722, row5723, row5724, row5725, row5726, row5727, row5728, row5729, row5730, row5731, row5732, row5733, row5734, row5735, row5736, row5737]

def rows5_2 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5738, row5739, row5740, row5741, row5742, row5743, row5744, row5745, row5746, row5747, row5748, row5749, row5750, row5751, row5752, row5753, row5754, row5755, row5756, row5757, row5758, row5759, row5760, row5761, row5762, row5763, row5764, row5765, row5766, row5767, row5768, row5769, row5770, row5771, row5772, row5773, row5774, row5775, row5776, row5777]

def rows5_3 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5778, row5779, row5780, row5781, row5782, row5783, row5784, row5785, row5786, row5787, row5788, row5789, row5790, row5791, row5792, row5793, row5794, row5795, row5796, row5797, row5798, row5799, row5800, row5801, row5802, row5803, row5804, row5805, row5806, row5807, row5808, row5809, row5810, row5811, row5812, row5813, row5814, row5815, row5816, row5817]

def rows5_4 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5818, row5819, row5820, row5821, row5822, row5823, row5824, row5825, row5826, row5827, row5828, row5829, row5830, row5831, row5832, row5833, row5834, row5835, row5836, row5837, row5838, row5839, row5840, row5841, row5842, row5843, row5844, row5845, row5846, row5847, row5848, row5849, row5850, row5851, row5852, row5853, row5854, row5855, row5856, row5857]

def rows5_5 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5858, row5859, row5860, row5861, row5862, row5863, row5864, row5865, row5866, row5867, row5868, row5869, row5870, row5871, row5872, row5873, row5874, row5875, row5876, row5877, row5878, row5879, row5880, row5881, row5882, row5883, row5884, row5885, row5886, row5887, row5888, row5889, row5890, row5891, row5892, row5893, row5894, row5895, row5896, row5897]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5898, row5899, row5900, row5901, row5902, row5903, row5904, row5905, row5906, row5907, row5908, row5909, row5910, row5911, row5912, row5913, row5914, row5915, row5916, row5917, row5918, row5919, row5920, row5921, row5922, row5923, row5924, row5925, row5926, row5927, row5928, row5929, row5930, row5931, row5932, row5933, row5934, row5935, row5936, row5937]

def rows6_1 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5938, row5939, row5940, row5941, row5942, row5943, row5944, row5945, row5946, row5947, row5948, row5949, row5950, row5951, row5952, row5953, row5954, row5955, row5956, row5957, row5958, row5959, row5960, row5961, row5962, row5963, row5964, row5965, row5966, row5967, row5968, row5969, row5970, row5971, row5972, row5973, row5974, row5975, row5976, row5977]

def rows6_2 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5978, row5979, row5980, row5981, row5982, row5983, row5984, row5985, row5986, row5987, row5988, row5989, row5990, row5991, row5992, row5993, row5994, row5995, row5996, row5997, row5998, row5999, row6000, row6001, row6002, row6003, row6004, row6005, row6006, row6007, row6008, row6009, row6010, row6011, row6012, row6013, row6014, row6015, row6016, row6017]

def rows6_3 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6018, row6019, row6020, row6021, row6022, row6023, row6024, row6025, row6026, row6027, row6028, row6029, row6030, row6031, row6032, row6033, row6034, row6035, row6036, row6037, row6038, row6039, row6040, row6041, row6042, row6043, row6044, row6045, row6046, row6047, row6048, row6049, row6050, row6051, row6052, row6053, row6054, row6055, row6056, row6057]

def rows6_4 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6058, row6059, row6060, row6061, row6062, row6063, row6064, row6065, row6066, row6067, row6068, row6069, row6070, row6071, row6072, row6073, row6074, row6075, row6076, row6077, row6078, row6079, row6080, row6081, row6082, row6083, row6084, row6085, row6086, row6087, row6088, row6089, row6090, row6091, row6092, row6093, row6094, row6095, row6096, row6097]

def rows6_5 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6098, row6099, row6100, row6101, row6102, row6103, row6104, row6105, row6106, row6107, row6108, row6109, row6110, row6111, row6112, row6113, row6114, row6115, row6116, row6117, row6118, row6119, row6120, row6121, row6122, row6123, row6124, row6125, row6126, row6127, row6128, row6129, row6130, row6131, row6132, row6133, row6134, row6135, row6136, row6137]

def rows6_6 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6138, row6139, row6140, row6141, row6142, row6143, row6144, row6145, row6146, row6147, row6148, row6149, row6150, row6151, row6152, row6153, row6154, row6155, row6156, row6157, row6158, row6159, row6160, row6161, row6162, row6163, row6164, row6165, row6166, row6167, row6168, row6169, row6170, row6171, row6172, row6173, row6174, row6175, row6176, row6177]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row5160, row5161, row5162, row5163, row5164, row5165, row5166, row5167, row5168, row5169, row5170, row5171, row6178, row6179, row5174, row5175, row6180, row6181, row5176, row5177, row5182, row5183, row6182, row6183, row5184, row5185, row6184, row6185, row6186, row6187, row6188, row6189, row6190, row6191, row6192, row6193, row6194, row6195, row6196, row6197]

def rows7_1 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6198, row6199, row6200, row6201, row6202, row6203, row6204, row6205, row6206, row6207, row6208, row6209, row6210, row6211, row6212, row6213, row6214, row6215, row6216, row6217, row6218, row6219, row6220, row6221, row6222, row6223, row6224, row6225, row6226, row6227, row6228, row6229, row6230, row6231, row6232, row6233, row6234, row6235, row6236, row6237]

def rows7_2 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6238, row6239, row6240, row6241, row6242, row6243, row6244, row6245, row6246, row6247, row6248, row6249, row6250, row6251, row6252, row6253, row6254, row6255, row6256, row6257, row6258, row6259, row6260, row6261, row6262, row6263, row6264, row6265, row6266, row6267, row6268, row6269, row6270, row6271, row6272, row6273, row6274, row6275, row6276, row6277]

def rows7_3 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6278, row6279, row6280, row6281, row6282, row6283, row6284, row6285, row6286, row6287, row6288, row6289, row6290, row6291, row6292, row6293, row6294, row6295, row6296, row6297, row6298, row6299, row6300, row6301, row6302, row6303, row6304, row6305, row6306, row6307, row6308, row6309, row6310, row6311, row6312, row6313, row6314, row6315, row6316, row6317]

def rows7_4 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6318, row6319, row6320, row6321, row6322, row6323, row6324, row6325, row6326, row6327, row6328, row6329, row6330, row6331, row6332, row6333, row6334, row6335, row6336, row6337, row6338, row6339, row6340, row6341, row6342, row6343, row6344, row6345, row6346, row6347, row6348, row6349, row6350, row6351, row6352, row6353, row6354, row6355, row6356, row6357]

def rows7_5 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6358, row6359, row6360, row6361, row6362, row6363, row6364, row6365, row6366, row6367, row6368, row6369, row6370, row6371, row6372, row6373, row6374, row6375, row6376, row6377, row6378, row6379, row6380, row6381, row6382, row6383, row6384, row6385, row6386, row6387, row6388, row6389, row6390, row6391, row6392, row6393, row6394, row6395, row6396, row6397]

def rows7_6 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6398, row6399, row6400, row6401, row6402, row6403, row6404, row6405, row6406, row6407, row6408, row6409, row6410, row6411, row6412, row6413, row6414, row6415, row6416, row6417, row6418, row6419, row6420, row6421, row6422, row6423, row6424, row6425, row6426, row6427, row6428, row6429, row6430, row6431, row6432, row6433, row6434, row6435, row6436, row6437]

def rows7_7 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6438, row6439, row6440, row6441, row6442, row6443, row6444, row6445, row6446, row6447, row6448, row6449, row6450, row6451, row6452, row6453, row6454, row6455, row6456, row6457, row6458, row6459, row6460, row6461, row6462, row6463, row6464, row6465, row6466, row6467, row6468, row6469, row6470, row6471, row6472, row6473, row6474, row6475, row6476, row6477]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6478, row6479, row6480, row6481, row6482, row6483, row6484, row6485, row6486, row6487, row6488, row6489, row5670, row5671, row5672, row5673, row5674, row5675, row5676, row5677, row5678, row5679, row5680, row5681, row5682, row5683, row6490, row6491, row5686, row5687, row6492, row6493, row6494, row6495, row5692, row5693, row6496, row6497, row5696, row5697]

def rows8_1 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6498, row6499, row6500, row6501, row6502, row6503, row6504, row6505, row6506, row6507, row6508, row6509, row5710, row5711, row5712, row5713, row5714, row5715, row5716, row5717, row5718, row5719, row5720, row5721, row5722, row5723, row6510, row6511, row5726, row5727, row6512, row6513, row6514, row6515, row5732, row5733, row6516, row6517, row5736, row5737]

def rows8_2 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6518, row6519, row6520, row6521, row6522, row6523, row6524, row6525, row6526, row6527, row6528, row6529, row5750, row5751, row5752, row5753, row5754, row5755, row5756, row5757, row5758, row5759, row5760, row5761, row5762, row5763, row6530, row6531, row5766, row5767, row6532, row6533, row6534, row6535, row5772, row5773, row6536, row6537, row5776, row5777]

def rows8_3 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6538, row6539, row6540, row6541, row6542, row6543, row6544, row6545, row6546, row6547, row6548, row6549, row5790, row5791, row5792, row5793, row5794, row5795, row5796, row5797, row5798, row5799, row5800, row5801, row5802, row5803, row6550, row6551, row5806, row5807, row6552, row6553, row6554, row6555, row5812, row5813, row6556, row6557, row5816, row5817]

def rows8_4 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6558, row6559, row6560, row6561, row6562, row6563, row6564, row6565, row6566, row6567, row6568, row6569, row5830, row5831, row5832, row5833, row5834, row5835, row5836, row5837, row5838, row5839, row5840, row5841, row5842, row5843, row6570, row6571, row5846, row5847, row6572, row6573, row6574, row6575, row5852, row5853, row6576, row6577, row5856, row5857]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8661, row8662, row8663, row8664, row8665, row8666, row8667, row8668]

end MUB6.Certificate.GramEntries.Block3

end OAI
end


