-- Prove2me | Definitions.Def_OAIQ106E051
-- name    : OAIQ106E051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:04:23.049515+00:00
-- url     : https://prove2.me/theorems/f8e82b58-d47a-4561-af34-74af89df5fe4
-- title:
--   Definitions bundle OAIQ106E051 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1632 declarations of OpenAI's Lean: 1632 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow2238`, `OAI.MUB6.Certificate.GramRows.rawRow2239`, `OAI.MUB6.Certificate.GramRows.rawRow224`, `OAI.MUB6.Certificate.GramRows.rawRow2240`, `OAI.MUB6.Certificate.GramRows.rawRow2241`, `OAI.MUB6.Certificate.GramRows.rawRow2242`, `OAI.MUB6.Certificate.GramRows.rawRow2243`, `OAI.MUB6.Certificate.GramRows.rawRow2244`, `OAI.MUB6.Certificate.GramRows.rawRow2245`, `OAI.MUB6.Certificate.GramRows.rawRow2246`, `OAI.MUB6.Certificate.GramRows.rawRow2247`, `OAI.MUB6.Certificate.GramRows.rawRow2248`, `OAI.MUB6.Certificate.GramRows.rawRow2249`, `OAI.MUB6.Certificate.GramRows.rawRow225`, `OAI.MUB6.Certificate.GramRows.rawRow2250`, `OAI.MUB6.Certificate.GramRows.rawRow2251`, `OAI.MUB6.Certificate.GramRows.rawRow2252`, `OAI.MUB6.Certificate.GramRows.rawRow2253`, `OAI.MUB6.Certificate.GramRows.rawRow2254`, `OAI.MUB6.Certificate.GramRows.rawRow2255`, `OAI.MUB6.Certificate.GramRows.rawRow2256`, `OAI.MUB6.Certificate.GramRows.rawRow2257`, `OAI.MUB6.Certificate.GramRows.rawRow2258`, `OAI.MUB6.Certificate.GramRows.rawRow2259`, `OAI.MUB6.Certificate.GramRows.rawRow226`, `OAI.MUB6.Certificate.GramRows.rawRow2260`, `OAI.MUB6.Certificate.GramRows.rawRow2261`, `OAI.MUB6.Certificate.GramRows.rawRow2262`, `OAI.MUB6.Certificate.GramRows.rawRow2263`, `OAI.MUB6.Certificate.GramRows.rawRow2264`, `OAI.MUB6.Certificate.GramRows.rawRow2265`, `OAI.MUB6.Certificate.GramRows.rawRow2267`, `OAI.MUB6.Certificate.GramRows.rawRow2268`, `OAI.MUB6.Certificate.GramRows.rawRow2269`, `OAI.MUB6.Certificate.GramRows.rawRow227`, `OAI.MUB6.Certificate.GramRows.rawRow2270`, `OAI.MUB6.Certificate.GramRows.rawRow2271`, `OAI.MUB6.Certificate.GramRows.rawRow2272`, `OAI.MUB6.Certificate.GramRows.rawRow2273`, `OAI.MUB6.Certificate.GramRows.rawRow2274` and 1592 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Integer`, `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block4`, `MutuallyUnbiased_GramRows_Block41`, `MutuallyUnbiased_GramRows_Block42`, `MutuallyUnbiased_GramRows_Block43`, `MutuallyUnbiased_GramRows_Block44`, `MutuallyUnbiased_GramRows_Block45`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block48`, `MutuallyUnbiased_GramRows_Block49`, `MutuallyUnbiased_GramRows_Block5`, `MutuallyUnbiased_GramRows_Block50`, `MutuallyUnbiased_GramRows_Block51`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block6`, `MutuallyUnbiased_GramRows_Block7`, `MutuallyUnbiased_GramRows_Block8`, `MutuallyUnbiased_GramRows_Block81`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e`, `OAI.MUB6.Certificate.MixedData.mergedEval2452_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e`, `OAI.MUB6.Certificate.MixedData.mergedEval2452_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e` and `OAI.MUB6.family_size_le_five_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Integer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer coefficient checking after denominator clearing. The arithmetic
checker uses only integer operations; its interpretation remains over arbitrary
real moment vectors. -/
namespace MUB6.Certificate.Integer

open scoped BigOperators

namespace Combination

variable {ι κ η : Type*}

noncomputable def eval (rows : κ → Sparse ι) (x : ι → ℝ) : Combination κ → ℝ
  | .leaf k => Sparse.eval (rows k) x
  | .add a b => eval rows x a + eval rows x b
  | .scale q a => (q : ℝ) * eval rows x a

end Combination
end MUB6.Certificate.Integer

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3 : Integer.Sparse Key := [(key248, -1), (key251, -1), (key260, 2), (key236, 1), (key239, 1), (key267, -1), (key271, -1), (key239, -2), (key251, 1), (key260, 1), (key316, 1), (key319, 1), (key335, -2), (key302, -1), (key305, -1), (key335, 1), (key340, 1), (key305, 2), (key319, -1), (key328, -1), (key406, -1), (key409, -1), (key467, 1), (key469, 1), (key385, 1), (key388, 1), (key467, -1), (key475, -1), (key388, -1), (key397, -1), (key409, 1), (key418, 1), (key578, 2), (key593, -1), (key595, -1), (key568, -2), (key593, 1), (key601, 1), (key568, 1), (key572, 1), (key578, -1), (key583, -1)]

def rawRow23 : Integer.Sparse Key := [(key397, -1), (key388, -1), (key385, 2), (key469, 1), (key467, 1), (key435, -1), (key406, -1), (key475, -2), (key450, 1), (key418, 1), (key260, 1), (key251, 1), (key248, -2), (key595, -1), (key593, -1), (key435, 1), (key316, 1), (key601, 2), (key450, -1), (key328, -1), (key271, -1), (key267, -1), (key248, 1), (key236, 1), (key340, 1), (key328, 1), (key316, -1), (key302, -1), (key601, -1), (key583, -1), (key595, 1), (key572, 1), (key260, 2), (key251, -1), (key239, -1), (key328, -2), (key319, 1), (key305, 1), (key450, 1), (key418, 1), (key442, -1), (key397, -1)]

def rawRow24 : Integer.Sparse Key := [(key406, -1), (key409, -1), (key418, 2), (key385, 1), (key388, 1), (key450, -1), (key475, -1), (key397, -2), (key442, 1), (key469, 1), (key316, 1), (key319, 1), (key328, -2), (key248, -1), (key251, -1), (key450, 1), (key601, 1), (key260, 2), (key442, -1), (key595, -1), (key302, -1), (key305, -1), (key328, 1), (key340, 1), (key236, 1), (key239, 1), (key578, -1), (key583, -1), (key267, -1), (key271, -1), (key335, 1), (key340, 1), (key305, 2), (key388, -1), (key397, -1), (key239, -2), (key409, 1), (key418, 1), (key251, 1), (key260, 1), (key319, -1), (key328, -1)]

def rawRow25 : Integer.Sparse Key := [(key409, -1), (key406, -1), (key418, 2), (key388, 1), (key385, 1), (key475, -1), (key450, -1), (key397, -2), (key469, 1), (key442, 1), (key319, 1), (key316, 1), (key328, -2), (key251, -1), (key248, -1), (key601, 1), (key450, 1), (key260, 2), (key595, -1), (key442, -1), (key305, -1), (key302, -1), (key340, 1), (key328, 1), (key239, 1), (key236, 1), (key583, -1), (key578, -1), (key271, -1), (key267, -1), (key340, 1), (key335, 1), (key305, 2), (key397, -1), (key388, -1), (key239, -2), (key418, 1), (key409, 1), (key260, 1), (key251, 1), (key328, -1), (key319, -1)]

def rawRow26 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key406, 2), (key467, 1), (key475, 1), (key385, -1), (key435, -1), (key469, -2), (key397, 1), (key442, 1), (key319, 1), (key328, 1), (key316, -2), (key593, -1), (key601, -1), (key248, 1), (key435, 1), (key595, 2), (key260, -1), (key442, -1), (key335, -1), (key340, -1), (key302, 1), (key316, 1), (key578, 1), (key583, 1), (key236, -1), (key406, -1), (key340, -1), (key475, -1), (key271, 1), (key469, 1), (key397, 2), (key305, -1), (key388, -1), (key418, -2), (key239, 1), (key409, 1), (key328, 1), (key450, 1), (key260, -1), (key442, -1)]

def rawRow27 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key406, 2), (key475, 1), (key467, 1), (key435, -1), (key385, -1), (key469, -2), (key442, 1), (key397, 1), (key328, 1), (key319, 1), (key316, -2), (key601, -1), (key593, -1), (key435, 1), (key248, 1), (key595, 2), (key442, -1), (key260, -1), (key340, -1), (key335, -1), (key316, 1), (key302, 1), (key583, 1), (key578, 1), (key406, -1), (key236, -1), (key475, -1), (key340, -1), (key469, 1), (key271, 1), (key397, 2), (key388, -1), (key305, -1), (key418, -2), (key409, 1), (key239, 1), (key450, 1), (key328, 1), (key442, -1), (key260, -1)]

def rawRow28 : Integer.Sparse Key := [(key467, -1), (key469, -1), (key475, 2), (key388, 1), (key397, 1), (key418, -1), (key450, -1), (key385, -2), (key406, 1), (key435, 1), (key593, 1), (key595, 1), (key601, -2), (key251, -1), (key260, -1), (key328, 1), (key450, 1), (key248, 2), (key316, -1), (key435, -1), (key568, -1), (key572, -1), (key583, 1), (key601, 1), (key267, 1), (key271, 1), (key340, -1), (key475, -1), (key236, -1), (key248, -1), (key302, 1), (key316, 1), (key328, 2), (key418, -1), (key450, -1), (key260, -2), (key397, 1), (key442, 1), (key239, 1), (key251, 1), (key305, -1), (key319, -1)]

def rawRow29 : Integer.Sparse Key := [(key469, -1), (key467, -1), (key475, 2), (key397, 1), (key388, 1), (key450, -1), (key418, -1), (key385, -2), (key435, 1), (key406, 1), (key595, 1), (key593, 1), (key601, -2), (key260, -1), (key251, -1), (key450, 1), (key328, 1), (key248, 2), (key435, -1), (key316, -1), (key572, -1), (key568, -1), (key601, 1), (key583, 1), (key271, 1), (key267, 1), (key475, -1), (key340, -1), (key248, -1), (key236, -1), (key316, 1), (key302, 1), (key328, 2), (key450, -1), (key418, -1), (key260, -2), (key442, 1), (key397, 1), (key251, 1), (key239, 1), (key319, -1), (key305, -1)]

def rawRow30 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key469, 2), (key409, 1), (key418, 1), (key397, -1), (key442, -1), (key406, -2), (key385, 1), (key435, 1), (key593, 1), (key601, 1), (key595, -2), (key319, -1), (key328, -1), (key260, 1), (key442, 1), (key316, 2), (key248, -1), (key435, -1), (key578, -1), (key583, -1), (key572, 1), (key595, 1), (key335, 1), (key340, 1), (key271, -1), (key469, -1), (key302, -1), (key316, -1), (key236, 1), (key406, 1), (key418, 2), (key328, -1), (key450, -1), (key397, -2), (key260, 1), (key442, 1), (key305, 1), (key388, 1), (key239, -1), (key409, -1)]

def rawRow31 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key469, 2), (key418, 1), (key409, 1), (key442, -1), (key397, -1), (key406, -2), (key435, 1), (key385, 1), (key601, 1), (key593, 1), (key595, -2), (key328, -1), (key319, -1), (key442, 1), (key260, 1), (key316, 2), (key435, -1), (key248, -1), (key583, -1), (key578, -1), (key595, 1), (key572, 1), (key340, 1), (key335, 1), (key469, -1), (key271, -1), (key316, -1), (key302, -1), (key406, 1), (key236, 1), (key418, 2), (key450, -1), (key328, -1), (key397, -2), (key442, 1), (key260, 1), (key388, 1), (key305, 1), (key409, -1), (key239, -1)]

def rawRow32 : Integer.Sparse Key := [(key568, -1), (key568, -1), (key572, 2), (key578, 1), (key578, 1), (key595, -1), (key595, -1), (key583, -2), (key601, 1), (key601, 1), (key267, 1), (key267, 1), (key271, -2), (key335, -1), (key335, -1), (key469, 1), (key469, 1), (key340, 2), (key475, -1), (key475, -1), (key239, -1), (key239, -1), (key260, 1), (key260, 1), (key305, 1), (key305, 1), (key397, -1), (key397, -1), (key328, -1), (key328, -1), (key418, 1), (key418, 1), (key236, 2), (key248, -1), (key248, -1), (key302, -2), (key316, 1), (key316, 1), (key385, 1), (key385, 1), (key406, -1), (key406, -1)]

def rawRow33 : Integer.Sparse Key := [(key568, -1), (key572, -1), (key568, 2), (key593, 1), (key595, 1), (key578, -1), (key593, -1), (key601, -2), (key583, 1), (key601, 1), (key267, 1), (key271, 1), (key267, -2), (key467, -1), (key469, -1), (key335, 1), (key467, 1), (key475, 2), (key340, -1), (key475, -1), (key251, -1), (key260, -1), (key239, 1), (key251, 1), (key388, 1), (key397, 1), (key305, -1), (key388, -1), (key418, -1), (key450, -1), (key328, 1), (key450, 1), (key248, 2), (key236, -1), (key248, -1), (key316, -2), (key302, 1), (key316, 1), (key406, 1), (key435, 1), (key385, -1), (key435, -1)]

def rawRow34 : Integer.Sparse Key := [(key572, -1), (key568, -1), (key568, 2), (key595, 1), (key593, 1), (key593, -1), (key578, -1), (key601, -2), (key601, 1), (key583, 1), (key271, 1), (key267, 1), (key267, -2), (key469, -1), (key467, -1), (key467, 1), (key335, 1), (key475, 2), (key475, -1), (key340, -1), (key260, -1), (key251, -1), (key251, 1), (key239, 1), (key397, 1), (key388, 1), (key388, -1), (key305, -1), (key450, -1), (key418, -1), (key450, 1), (key328, 1), (key248, 2), (key248, -1), (key236, -1), (key316, -2), (key316, 1), (key302, 1), (key435, 1), (key406, 1), (key435, -1), (key385, -1)]

def rawRow35 : Integer.Sparse Key := [(key578, -1), (key578, -1), (key583, 2), (key568, 1), (key568, 1), (key601, -1), (key601, -1), (key572, -2), (key595, 1), (key595, 1), (key335, 1), (key335, 1), (key340, -2), (key267, -1), (key267, -1), (key475, 1), (key475, 1), (key271, 2), (key469, -1), (key469, -1), (key305, -1), (key305, -1), (key328, 1), (key328, 1), (key239, 1), (key239, 1), (key418, -1), (key418, -1), (key260, -1), (key260, -1), (key397, 1), (key397, 1), (key302, 2), (key316, -1), (key316, -1), (key236, -2), (key406, 1), (key406, 1), (key248, 1), (key248, 1), (key316, -1), (key316, -1)]

def rawRow36 : Integer.Sparse Key := [(key578, -1), (key583, -1), (key578, 2), (key593, 1), (key601, 1), (key568, -1), (key593, -1), (key595, -2), (key572, 1), (key595, 1), (key335, 1), (key340, 1), (key335, -2), (key467, -1), (key475, -1), (key267, 1), (key467, 1), (key469, 2), (key271, -1), (key469, -1), (key319, -1), (key328, -1), (key305, 1), (key319, 1), (key409, 1), (key418, 1), (key239, -1), (key409, -1), (key397, -1), (key442, -1), (key260, 1), (key442, 1), (key316, 2), (key302, -1), (key316, -1), (key406, -2), (key236, 1), (key406, 1), (key316, 1), (key435, 1), (key248, -1), (key435, -1)]

def rawRow37 : Integer.Sparse Key := [(key583, -1), (key578, -1), (key578, 2), (key601, 1), (key593, 1), (key593, -1), (key568, -1), (key595, -2), (key595, 1), (key572, 1), (key340, 1), (key335, 1), (key335, -2), (key475, -1), (key467, -1), (key467, 1), (key267, 1), (key469, 2), (key469, -1), (key271, -1), (key328, -1), (key319, -1), (key319, 1), (key305, 1), (key418, 1), (key409, 1), (key409, -1), (key239, -1), (key442, -1), (key397, -1), (key442, 1), (key260, 1), (key316, 2), (key316, -1), (key302, -1), (key406, -2), (key406, 1), (key236, 1), (key435, 1), (key316, 1), (key435, -1), (key248, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow224 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key2724, 2), (key2669, 1), (key2663, 1), (key2757, -1), (key2724, -1), (key2669, -2), (key2752, 1), (key2704, 1), (key2807, 1), (key2801, 1), (key2827, -2), (key2614, -1), (key2608, -1), (key3016, 1), (key3011, 1), (key2614, 2), (key2827, -1), (key2807, -1), (key2704, -1), (key2698, -1), (key3022, 1), (key3021, 1), (key2630, 1), (key2624, 1), (key3025, -1), (key3021, -1), (key2638, -1), (key2630, -1), (key2724, 1), (key2704, 1), (key2752, 2), (key2919, -1), (key2918, -1), (key2657, -2), (key2922, 1), (key2918, 1), (key2659, 1), (key2657, 1), (key2757, -1), (key2752, -1)]

def rawRow225 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2698, 2), (key2752, 1), (key2757, 1), (key2663, -1), (key2698, -1), (key2752, -2), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2801, -2), (key3011, -1), (key3016, -1), (key2608, 1), (key2801, 1), (key2827, 2), (key2614, -1), (key2807, -1), (key2858, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key2868, 1), (key3025, 1), (key2624, -1), (key2851, -1), (key2724, -1), (key2868, -1), (key2638, 1), (key2858, 1), (key2919, 2), (key2752, -1), (key2918, -1), (key2922, -2), (key2657, 1), (key2918, 1), (key2757, 1), (key2922, 1), (key2659, -1), (key2919, -1)]

def rawRow226 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2698, 2), (key2757, 1), (key2752, 1), (key2698, -1), (key2663, -1), (key2752, -2), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2801, -2), (key3016, -1), (key3011, -1), (key2801, 1), (key2608, 1), (key2827, 2), (key2807, -1), (key2614, -1), (key3022, -1), (key2858, -1), (key2851, 1), (key2698, 1), (key3025, 1), (key2868, 1), (key2851, -1), (key2624, -1), (key2868, -1), (key2724, -1), (key2858, 1), (key2638, 1), (key2919, 2), (key2918, -1), (key2752, -1), (key2922, -2), (key2918, 1), (key2657, 1), (key2922, 1), (key2757, 1), (key2919, -1), (key2659, -1)]

def rawRow227 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2757, 2), (key2669, 1), (key2669, 1), (key2724, -1), (key2724, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key3011, 1), (key3011, 1), (key3016, -2), (key2614, -1), (key2614, -1), (key2827, 1), (key2827, 1), (key2608, 2), (key2801, -1), (key2801, -1), (key2724, -1), (key2724, -1), (key3025, 1), (key3025, 1), (key2638, 1), (key2638, 1), (key3022, -1), (key3022, -1), (key2624, -1), (key2624, -1), (key2698, 1), (key2698, 1), (key2757, 2), (key2922, -1), (key2922, -1), (key2659, -2), (key2919, 1), (key2919, 1), (key2657, 1), (key2657, 1), (key2752, -1), (key2752, -1)]

def rawRow228 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2752, 2), (key2704, 1), (key2724, 1), (key2669, -1), (key2704, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key3011, -2), (key2807, -1), (key2827, -1), (key2614, 1), (key2807, 1), (key2801, 2), (key2608, -1), (key2801, -1), (key2868, -1), (key3025, -1), (key2724, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key2638, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2624, 1), (key2851, 1), (key2922, 2), (key2757, -1), (key2922, -1), (key2919, -2), (key2659, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2657, -1), (key2918, -1)]

def rawRow229 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2752, 2), (key2724, 1), (key2704, 1), (key2704, -1), (key2669, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key3011, -2), (key2827, -1), (key2807, -1), (key2807, 1), (key2614, 1), (key2801, 2), (key2801, -1), (key2608, -1), (key3025, -1), (key2868, -1), (key2868, 1), (key2724, 1), (key3022, 1), (key2858, 1), (key2858, -1), (key2638, -1), (key2851, -1), (key2698, -1), (key2851, 1), (key2624, 1), (key2922, 2), (key2922, -1), (key2757, -1), (key2919, -2), (key2919, 1), (key2659, 1), (key2918, 1), (key2752, 1), (key2918, -1), (key2657, -1)]

def rawRow230 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, 1), (key2858, -1), (key2919, -1), (key2827, -2), (key2868, 1), (key2922, 1), (key2624, 1), (key2630, 1), (key2638, -2), (key2698, -1), (key2704, -1), (key2858, 1), (key3022, 1), (key2724, 2), (key2868, -1), (key3025, -1), (key2608, -1), (key2614, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2752, -1), (key2757, -1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key2614, 2), (key2630, -1), (key2638, -1), (key2669, -2), (key2704, 1), (key2724, 1), (key2784, 1), (key2792, 1), (key2807, -1), (key2827, -1)]

def rawRow231 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2792, 2), (key2807, 1), (key2801, 1), (key2919, -1), (key2858, -1), (key2827, -2), (key2922, 1), (key2868, 1), (key2630, 1), (key2624, 1), (key2638, -2), (key2704, -1), (key2698, -1), (key3022, 1), (key2858, 1), (key2724, 2), (key3025, -1), (key2868, -1), (key2614, -1), (key2608, -1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2757, -1), (key2752, -1), (key3009, -1), (key3007, -1), (key3016, 1), (key3011, 1), (key2614, 2), (key2638, -1), (key2630, -1), (key2669, -2), (key2724, 1), (key2704, 1), (key2792, 1), (key2784, 1), (key2827, -1), (key2807, -1)]

def rawRow232 : Integer.Sparse Key := [(key2784, -1), (key2792, -1), (key2778, 2), (key2918, 1), (key2919, 1), (key2801, -1), (key2851, -1), (key2922, -2), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2624, -2), (key3021, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key3025, 2), (key2724, -1), (key2868, -1), (key2657, -1), (key2659, -1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2663, -1), (key2698, -1), (key3016, -1), (key3025, -1), (key3009, 1), (key3022, 1), (key2638, 2), (key2614, -1), (key2630, -1), (key2724, -2), (key2669, 1), (key2704, 1), (key2827, 1), (key2868, 1), (key2792, -1), (key2858, -1)]

def rawRow233 : Integer.Sparse Key := [(key2792, -1), (key2784, -1), (key2778, 2), (key2919, 1), (key2918, 1), (key2851, -1), (key2801, -1), (key2922, -2), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2624, -2), (key3022, -1), (key3021, -1), (key2851, 1), (key2698, 1), (key3025, 2), (key2868, -1), (key2724, -1), (key2659, -1), (key2657, -1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2698, -1), (key2663, -1), (key3025, -1), (key3016, -1), (key3022, 1), (key3009, 1), (key2638, 2), (key2630, -1), (key2614, -1), (key2724, -2), (key2704, 1), (key2669, 1), (key2868, 1), (key2827, 1), (key2858, -1), (key2792, -1)]

def rawRow234 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2827, 2), (key2778, 1), (key2784, 1), (key2868, -1), (key2922, -1), (key2792, -2), (key2858, 1), (key2919, 1), (key2698, 1), (key2704, 1), (key2724, -2), (key2624, -1), (key2630, -1), (key2868, 1), (key3025, 1), (key2638, 2), (key2858, -1), (key3022, -1), (key2663, -1), (key2669, -1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key3011, -1), (key3016, -1), (key2657, -1), (key2659, -1), (key2752, 1), (key2757, 1), (key2669, 2), (key2784, -1), (key2792, -1), (key2614, -2), (key2807, 1), (key2827, 1), (key2630, 1), (key2638, 1), (key2704, -1), (key2724, -1)]

def rawRow235 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, 2), (key2784, 1), (key2778, 1), (key2922, -1), (key2868, -1), (key2792, -2), (key2919, 1), (key2858, 1), (key2704, 1), (key2698, 1), (key2724, -2), (key2630, -1), (key2624, -1), (key3025, 1), (key2868, 1), (key2638, 2), (key3022, -1), (key2858, -1), (key2669, -1), (key2663, -1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key3016, -1), (key3011, -1), (key2659, -1), (key2657, -1), (key2757, 1), (key2752, 1), (key2669, 2), (key2792, -1), (key2784, -1), (key2614, -2), (key2827, 1), (key2807, 1), (key2638, 1), (key2630, 1), (key2724, -1), (key2704, -1)]

def rawRow236 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2801, 2), (key2918, 1), (key2922, 1), (key2778, -1), (key2851, -1), (key2919, -2), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2698, -2), (key3021, -1), (key3025, -1), (key2624, 1), (key2851, 1), (key3022, 2), (key2638, -1), (key2858, -1), (key2752, -1), (key2757, -1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2608, -1), (key2801, -1), (key2757, -1), (key2922, -1), (key2659, 1), (key2919, 1), (key2792, 2), (key2669, -1), (key2784, -1), (key2827, -2), (key2614, 1), (key2807, 1), (key2724, 1), (key2868, 1), (key2638, -1), (key2858, -1)]

def rawRow237 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2801, 2), (key2922, 1), (key2918, 1), (key2851, -1), (key2778, -1), (key2919, -2), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2698, -2), (key3025, -1), (key3021, -1), (key2851, 1), (key2624, 1), (key3022, 2), (key2858, -1), (key2638, -1), (key2757, -1), (key2752, -1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2801, -1), (key2608, -1), (key2922, -1), (key2757, -1), (key2919, 1), (key2659, 1), (key2792, 2), (key2784, -1), (key2669, -1), (key2827, -2), (key2807, 1), (key2614, 1), (key2868, 1), (key2724, 1), (key2858, -1), (key2638, -1)]

def rawRow238 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2922, 2), (key2784, 1), (key2792, 1), (key2827, -1), (key2868, -1), (key2778, -2), (key2801, 1), (key2851, 1), (key3021, 1), (key3022, 1), (key3025, -2), (key2630, -1), (key2638, -1), (key2724, 1), (key2868, 1), (key2624, 2), (key2698, -1), (key2851, -1), (key3007, -1), (key3009, -1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2757, -1), (key2922, -1), (key2608, -1), (key2624, -1), (key2663, 1), (key2698, 1), (key2724, 2), (key2827, -1), (key2868, -1), (key2638, -2), (key2792, 1), (key2858, 1), (key2614, 1), (key2630, 1), (key2669, -1), (key2704, -1)]

def rawRow239 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2922, 2), (key2792, 1), (key2784, 1), (key2868, -1), (key2827, -1), (key2778, -2), (key2851, 1), (key2801, 1), (key3022, 1), (key3021, 1), (key3025, -2), (key2638, -1), (key2630, -1), (key2868, 1), (key2724, 1), (key2624, 2), (key2851, -1), (key2698, -1), (key3009, -1), (key3007, -1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2922, -1), (key2757, -1), (key2624, -1), (key2608, -1), (key2698, 1), (key2663, 1), (key2724, 2), (key2868, -1), (key2827, -1), (key2638, -2), (key2858, 1), (key2792, 1), (key2630, 1), (key2614, 1), (key2704, -1), (key2669, -1)]

def rawRow240 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2919, 2), (key2807, 1), (key2827, 1), (key2792, -1), (key2858, -1), (key2801, -2), (key2778, 1), (key2851, 1), (key3021, 1), (key3025, 1), (key3022, -2), (key2704, -1), (key2724, -1), (key2638, 1), (key2858, 1), (key2698, 2), (key2624, -1), (key2851, -1), (key3011, -1), (key3016, -1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2659, -1), (key2919, -1), (key2663, -1), (key2698, -1), (key2608, 1), (key2801, 1), (key2827, 2), (key2724, -1), (key2868, -1), (key2792, -2), (key2638, 1), (key2858, 1), (key2669, 1), (key2784, 1), (key2614, -1), (key2807, -1)]

def rawRow241 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2919, 2), (key2827, 1), (key2807, 1), (key2858, -1), (key2792, -1), (key2801, -2), (key2851, 1), (key2778, 1), (key3025, 1), (key3021, 1), (key3022, -2), (key2724, -1), (key2704, -1), (key2858, 1), (key2638, 1), (key2698, 2), (key2851, -1), (key2624, -1), (key3016, -1), (key3011, -1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2919, -1), (key2659, -1), (key2698, -1), (key2663, -1), (key2801, 1), (key2608, 1), (key2827, 2), (key2868, -1), (key2724, -1), (key2792, -2), (key2858, 1), (key2638, 1), (key2784, 1), (key2669, 1), (key2807, -1), (key2614, -1)]

def rawRow242 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3009, 2), (key3011, 1), (key3011, 1), (key3022, -1), (key3022, -1), (key3016, -2), (key3025, 1), (key3025, 1), (key2657, 1), (key2657, 1), (key2659, -2), (key2752, -1), (key2752, -1), (key2919, 1), (key2919, 1), (key2757, 2), (key2922, -1), (key2922, -1), (key2614, -1), (key2614, -1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2792, -1), (key2792, -1), (key2724, -1), (key2724, -1), (key2827, 1), (key2827, 1), (key2608, 2), (key2624, -1), (key2624, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

def rawRow243 : Integer.Sparse Key := [(key3007, -1), (key3009, -1), (key3007, 2), (key3021, 1), (key3022, 1), (key3011, -1), (key3021, -1), (key3025, -2), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2657, -2), (key2918, -1), (key2919, -1), (key2752, 1), (key2918, 1), (key2922, 2), (key2757, -1), (key2922, -1), (key2630, -1), (key2638, -1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, -1), (key2784, -1), (key2827, -1), (key2868, -1), (key2724, 1), (key2868, 1), (key2624, 2), (key2608, -1), (key2624, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

def rawRow244 : Integer.Sparse Key := [(key3009, -1), (key3007, -1), (key3007, 2), (key3022, 1), (key3021, 1), (key3021, -1), (key3011, -1), (key3025, -2), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2657, -2), (key2919, -1), (key2918, -1), (key2918, 1), (key2752, 1), (key2922, 2), (key2922, -1), (key2757, -1), (key2638, -1), (key2630, -1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2784, -1), (key2669, -1), (key2868, -1), (key2827, -1), (key2868, 1), (key2724, 1), (key2624, 2), (key2624, -1), (key2608, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

def rawRow245 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3016, 2), (key3007, 1), (key3007, 1), (key3025, -1), (key3025, -1), (key3009, -2), (key3022, 1), (key3022, 1), (key2752, 1), (key2752, 1), (key2757, -2), (key2657, -1), (key2657, -1), (key2922, 1), (key2922, 1), (key2659, 2), (key2919, -1), (key2919, -1), (key2669, -1), (key2669, -1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2827, -1), (key2827, -1), (key2638, -1), (key2638, -1), (key2792, 1), (key2792, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2608, -2), (key2801, 1), (key2801, 1), (key2624, 1), (key2624, 1), (key2698, -1), (key2698, -1)]

def rawRow246 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key3011, 2), (key3021, 1), (key3025, 1), (key3007, -1), (key3021, -1), (key3022, -2), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2752, -2), (key2918, -1), (key2922, -1), (key2657, 1), (key2918, 1), (key2919, 2), (key2659, -1), (key2919, -1), (key2704, -1), (key2724, -1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, -1), (key2807, -1), (key2792, -1), (key2858, -1), (key2638, 1), (key2858, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, -2), (key2608, 1), (key2801, 1), (key2698, 1), (key2851, 1), (key2624, -1), (key2851, -1)]

def rawRow247 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key3011, 2), (key3025, 1), (key3021, 1), (key3021, -1), (key3007, -1), (key3022, -2), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2752, -2), (key2922, -1), (key2918, -1), (key2918, 1), (key2657, 1), (key2919, 2), (key2919, -1), (key2659, -1), (key2724, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2807, -1), (key2614, -1), (key2858, -1), (key2792, -1), (key2858, 1), (key2638, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2801, -2), (key2801, 1), (key2608, 1), (key2851, 1), (key2698, 1), (key2851, -1), (key2624, -1)]

def rawRow248 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3025, 2), (key3007, 1), (key3009, 1), (key3016, -1), (key3025, -1), (key3007, -2), (key3011, 1), (key3021, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key2657, -1), (key2659, -1), (key2757, 1), (key2922, 1), (key2657, 2), (key2752, -1), (key2918, -1), (key2784, -1), (key2792, -1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2724, -1), (key2868, -1), (key2614, -1), (key2630, -1), (key2669, 1), (key2784, 1), (key2778, 2), (key2801, -1), (key2851, -1), (key2624, -2), (key2698, 1), (key2851, 1), (key2608, 1), (key2624, 1), (key2663, -1), (key2698, -1)]

def rawRow249 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3025, 2), (key3009, 1), (key3007, 1), (key3025, -1), (key3016, -1), (key3007, -2), (key3021, 1), (key3011, 1), (key2919, 1), (key2918, 1), (key2922, -2), (key2659, -1), (key2657, -1), (key2922, 1), (key2757, 1), (key2657, 2), (key2918, -1), (key2752, -1), (key2792, -1), (key2784, -1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2868, -1), (key2724, -1), (key2630, -1), (key2614, -1), (key2784, 1), (key2669, 1), (key2778, 2), (key2851, -1), (key2801, -1), (key2624, -2), (key2851, 1), (key2698, 1), (key2624, 1), (key2608, 1), (key2698, -1), (key2663, -1)]

def rawRow250 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3022, 2), (key3011, 1), (key3016, 1), (key3009, -1), (key3022, -1), (key3011, -2), (key3007, 1), (key3021, 1), (key2918, 1), (key2922, 1), (key2919, -2), (key2752, -1), (key2757, -1), (key2659, 1), (key2919, 1), (key2752, 2), (key2657, -1), (key2918, -1), (key2807, -1), (key2827, -1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2638, -1), (key2858, -1), (key2669, -1), (key2704, -1), (key2614, 1), (key2807, 1), (key2801, 2), (key2778, -1), (key2851, -1), (key2698, -2), (key2624, 1), (key2851, 1), (key2663, 1), (key2698, 1), (key2608, -1), (key2801, -1)]

def rawRow251 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3022, 2), (key3016, 1), (key3011, 1), (key3022, -1), (key3009, -1), (key3011, -2), (key3021, 1), (key3007, 1), (key2922, 1), (key2918, 1), (key2919, -2), (key2757, -1), (key2752, -1), (key2919, 1), (key2659, 1), (key2752, 2), (key2918, -1), (key2657, -1), (key2827, -1), (key2807, -1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2858, -1), (key2638, -1), (key2704, -1), (key2669, -1), (key2807, 1), (key2614, 1), (key2801, 2), (key2851, -1), (key2778, -1), (key2698, -2), (key2851, 1), (key2624, 1), (key2698, 1), (key2663, 1), (key2801, -1), (key2608, -1)]

def rawRow252 : Integer.Sparse Key := [(key242, -1), (key242, -1), (key244, 2), (key254, 1), (key254, 1), (key265, -1), (key265, -1), (key269, -2), (key274, 1), (key274, 1), (key308, 1), (key308, 1), (key310, -2), (key322, -1), (key322, -1), (key333, 1), (key333, 1), (key337, 2), (key343, -1), (key343, -1), (key391, -1), (key391, -1), (key402, 1), (key402, 1), (key412, 1), (key412, 1), (key423, -1), (key423, -1), (key472, -1), (key472, -1), (key478, 1), (key478, 1), (key570, 2), (key575, -1), (key575, -1), (key580, -2), (key586, 1), (key586, 1), (key598, 1), (key598, 1), (key604, -1), (key604, -1)]

def rawRow253 : Integer.Sparse Key := [(key242, -1), (key244, -1), (key242, 2), (key264, 1), (key265, 1), (key254, -1), (key264, -1), (key274, -2), (key269, 1), (key274, 1), (key308, 1), (key310, 1), (key308, -2), (key332, -1), (key333, -1), (key322, 1), (key332, 1), (key343, 2), (key337, -1), (key343, -1), (key401, -1), (key402, -1), (key391, 1), (key401, 1), (key422, 1), (key423, 1), (key412, -1), (key422, -1), (key478, -1), (key484, -1), (key472, 1), (key484, 1), (key575, 2), (key570, -1), (key575, -1), (key586, -2), (key580, 1), (key586, 1), (key604, 1), (key610, 1), (key598, -1), (key610, -1)]

def rawRow254 : Integer.Sparse Key := [(key244, -1), (key242, -1), (key242, 2), (key265, 1), (key264, 1), (key264, -1), (key254, -1), (key274, -2), (key274, 1), (key269, 1), (key310, 1), (key308, 1), (key308, -2), (key333, -1), (key332, -1), (key332, 1), (key322, 1), (key343, 2), (key343, -1), (key337, -1), (key402, -1), (key401, -1), (key401, 1), (key391, 1), (key423, 1), (key422, 1), (key422, -1), (key412, -1), (key484, -1), (key478, -1), (key484, 1), (key472, 1), (key575, 2), (key575, -1), (key570, -1), (key586, -2), (key586, 1), (key580, 1), (key610, 1), (key604, 1), (key610, -1), (key598, -1)]

def rawRow255 : Integer.Sparse Key := [(key254, -1), (key254, -1), (key269, 2), (key242, 1), (key242, 1), (key274, -1), (key274, -1), (key244, -2), (key265, 1), (key265, 1), (key322, 1), (key322, 1), (key337, -2), (key308, -1), (key308, -1), (key343, 1), (key343, 1), (key310, 2), (key333, -1), (key333, -1), (key412, -1), (key412, -1), (key472, 1), (key472, 1), (key391, 1), (key391, 1), (key478, -1), (key478, -1), (key402, -1), (key402, -1), (key423, 1), (key423, 1), (key580, 2), (key598, -1), (key598, -1), (key570, -2), (key604, 1), (key604, 1), (key575, 1), (key575, 1), (key586, -1), (key586, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2238 : Integer.Sparse Key := [(key1773, -1), (key1773, -1), (key1547, -1), (key1547, -1), (key1542, -1), (key1542, -1), (key1779, 2), (key1555, 2), (key1555, 2), (key1789, 1), (key1789, 1), (key1574, 1), (key1574, 1), (key1569, 1), (key1569, 1), (key1816, -1), (key1816, -1), (key1658, -1), (key1658, -1), (key1623, -1), (key1623, -1), (key1797, -2), (key1592, -2), (key1592, -2), (key1824, 1), (key1824, 1), (key1666, 1), (key1666, 1), (key1632, 1), (key1632, 1)]

def rawRow2239 : Integer.Sparse Key := [(key1387, -1), (key1392, -1), (key1542, -1), (key1773, -1), (key1555, -1), (key1779, -1), (key1392, 2), (key1547, 2), (key1773, 2), (key1420, 1), (key1425, 1), (key1618, 1), (key1814, 1), (key1623, 1), (key1816, 1), (key1425, -1), (key1456, -1), (key1574, -1), (key1789, -1), (key1656, -1), (key1814, -1), (key1443, -2), (key1632, -2), (key1824, -2), (key1443, 1), (key1465, 1), (key1592, 1), (key1797, 1), (key1666, 1), (key1824, 1)]

def rawRow2240 : Integer.Sparse Key := [(key1392, -1), (key1387, -1), (key1773, -1), (key1542, -1), (key1779, -1), (key1555, -1), (key1392, 2), (key1773, 2), (key1547, 2), (key1425, 1), (key1420, 1), (key1814, 1), (key1618, 1), (key1816, 1), (key1623, 1), (key1456, -1), (key1425, -1), (key1789, -1), (key1574, -1), (key1814, -1), (key1656, -1), (key1443, -2), (key1824, -2), (key1632, -2), (key1465, 1), (key1443, 1), (key1797, 1), (key1592, 1), (key1824, 1), (key1666, 1)]

def rawRow2241 : Integer.Sparse Key := [(key1542, -1), (key1555, -1), (key1387, -1), (key1779, -1), (key1392, -1), (key1773, -1), (key1547, 2), (key1392, 2), (key1773, 2), (key1618, 1), (key1623, 1), (key1420, 1), (key1816, 1), (key1425, 1), (key1814, 1), (key1574, -1), (key1656, -1), (key1425, -1), (key1814, -1), (key1456, -1), (key1789, -1), (key1632, -2), (key1443, -2), (key1824, -2), (key1592, 1), (key1666, 1), (key1443, 1), (key1824, 1), (key1465, 1), (key1797, 1)]

def rawRow2242 : Integer.Sparse Key := [(key1555, -1), (key1542, -1), (key1779, -1), (key1387, -1), (key1773, -1), (key1392, -1), (key1547, 2), (key1773, 2), (key1392, 2), (key1623, 1), (key1618, 1), (key1816, 1), (key1420, 1), (key1814, 1), (key1425, 1), (key1656, -1), (key1574, -1), (key1814, -1), (key1425, -1), (key1789, -1), (key1456, -1), (key1632, -2), (key1824, -2), (key1443, -2), (key1666, 1), (key1592, 1), (key1824, 1), (key1443, 1), (key1797, 1), (key1465, 1)]

def rawRow2243 : Integer.Sparse Key := [(key1773, -1), (key1779, -1), (key1392, -1), (key1555, -1), (key1387, -1), (key1542, -1), (key1773, 2), (key1392, 2), (key1547, 2), (key1814, 1), (key1816, 1), (key1425, 1), (key1623, 1), (key1420, 1), (key1618, 1), (key1789, -1), (key1814, -1), (key1456, -1), (key1656, -1), (key1425, -1), (key1574, -1), (key1824, -2), (key1443, -2), (key1632, -2), (key1797, 1), (key1824, 1), (key1465, 1), (key1666, 1), (key1443, 1), (key1592, 1)]

def rawRow2244 : Integer.Sparse Key := [(key1779, -1), (key1773, -1), (key1555, -1), (key1392, -1), (key1542, -1), (key1387, -1), (key1773, 2), (key1547, 2), (key1392, 2), (key1816, 1), (key1814, 1), (key1623, 1), (key1425, 1), (key1618, 1), (key1420, 1), (key1814, -1), (key1789, -1), (key1656, -1), (key1456, -1), (key1574, -1), (key1425, -1), (key1824, -2), (key1632, -2), (key1443, -2), (key1824, 1), (key1797, 1), (key1666, 1), (key1465, 1), (key1592, 1), (key1443, 1)]

def rawRow2245 : Integer.Sparse Key := [(key1569, -1), (key1574, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1789, -1), (key1592, 2), (key1592, 2), (key1797, 2), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1), (key1632, -1), (key1666, -1), (key1632, -1), (key1824, -1), (key1666, -1), (key1824, -1), (key1555, -2), (key1555, -2), (key1779, -2), (key1623, 1), (key1658, 1), (key1623, 1), (key1816, 1), (key1658, 1), (key1816, 1)]

def rawRow2246 : Integer.Sparse Key := [(key1574, -1), (key1569, -1), (key1789, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1592, 2), (key1797, 2), (key1592, 2), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1666, -1), (key1632, -1), (key1824, -1), (key1632, -1), (key1824, -1), (key1666, -1), (key1555, -2), (key1779, -2), (key1555, -2), (key1658, 1), (key1623, 1), (key1816, 1), (key1623, 1), (key1816, 1), (key1658, 1)]

def rawRow2247 : Integer.Sparse Key := [(key1789, -1), (key1789, -1), (key1574, -1), (key1574, -1), (key1569, -1), (key1569, -1), (key1797, 2), (key1592, 2), (key1592, 2), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1), (key1824, -1), (key1824, -1), (key1666, -1), (key1666, -1), (key1632, -1), (key1632, -1), (key1779, -2), (key1555, -2), (key1555, -2), (key1816, 1), (key1816, 1), (key1658, 1), (key1658, 1), (key1623, 1), (key1623, 1)]

def rawRow2248 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1569, -1), (key1789, -1), (key1592, -1), (key1797, -1), (key1297, 2), (key1574, 2), (key1789, 2), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1), (key1317, -1), (key1338, -1), (key1547, -1), (key1773, -1), (key1656, -1), (key1814, -1), (key1325, -2), (key1623, -2), (key1816, -2), (key1325, 1), (key1344, 1), (key1555, 1), (key1779, 1), (key1658, 1), (key1816, 1)]

def rawRow2249 : Integer.Sparse Key := [(key1297, -1), (key1292, -1), (key1789, -1), (key1569, -1), (key1797, -1), (key1592, -1), (key1297, 2), (key1789, 2), (key1574, 2), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1), (key1338, -1), (key1317, -1), (key1773, -1), (key1547, -1), (key1814, -1), (key1656, -1), (key1325, -2), (key1816, -2), (key1623, -2), (key1344, 1), (key1325, 1), (key1779, 1), (key1555, 1), (key1816, 1), (key1658, 1)]

def rawRow2250 : Integer.Sparse Key := [(key1569, -1), (key1592, -1), (key1292, -1), (key1797, -1), (key1297, -1), (key1789, -1), (key1574, 2), (key1297, 2), (key1789, 2), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1), (key1547, -1), (key1656, -1), (key1317, -1), (key1814, -1), (key1338, -1), (key1773, -1), (key1623, -2), (key1325, -2), (key1816, -2), (key1555, 1), (key1658, 1), (key1325, 1), (key1816, 1), (key1344, 1), (key1779, 1)]

def rawRow2251 : Integer.Sparse Key := [(key1592, -1), (key1569, -1), (key1797, -1), (key1292, -1), (key1789, -1), (key1297, -1), (key1574, 2), (key1789, 2), (key1297, 2), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1), (key1656, -1), (key1547, -1), (key1814, -1), (key1317, -1), (key1773, -1), (key1338, -1), (key1623, -2), (key1816, -2), (key1325, -2), (key1658, 1), (key1555, 1), (key1816, 1), (key1325, 1), (key1779, 1), (key1344, 1)]

def rawRow2252 : Integer.Sparse Key := [(key1789, -1), (key1797, -1), (key1297, -1), (key1592, -1), (key1292, -1), (key1569, -1), (key1789, 2), (key1297, 2), (key1574, 2), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1), (key1773, -1), (key1814, -1), (key1338, -1), (key1656, -1), (key1317, -1), (key1547, -1), (key1816, -2), (key1325, -2), (key1623, -2), (key1779, 1), (key1816, 1), (key1344, 1), (key1658, 1), (key1325, 1), (key1555, 1)]

def rawRow2253 : Integer.Sparse Key := [(key1797, -1), (key1789, -1), (key1592, -1), (key1297, -1), (key1569, -1), (key1292, -1), (key1789, 2), (key1574, 2), (key1297, 2), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1), (key1814, -1), (key1773, -1), (key1656, -1), (key1338, -1), (key1547, -1), (key1317, -1), (key1816, -2), (key1623, -2), (key1325, -2), (key1816, 1), (key1779, 1), (key1658, 1), (key1344, 1), (key1555, 1), (key1325, 1)]

def rawRow2254 : Integer.Sparse Key := [(key1420, -1), (key1425, -1), (key1618, -1), (key1814, -1), (key1623, -1), (key1816, -1), (key1443, 2), (key1632, 2), (key1824, 2), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1), (key1443, -1), (key1465, -1), (key1592, -1), (key1797, -1), (key1666, -1), (key1824, -1), (key1392, -2), (key1547, -2), (key1773, -2), (key1425, 1), (key1456, 1), (key1574, 1), (key1789, 1), (key1656, 1), (key1814, 1)]

def rawRow2255 : Integer.Sparse Key := [(key1425, -1), (key1420, -1), (key1814, -1), (key1618, -1), (key1816, -1), (key1623, -1), (key1443, 2), (key1824, 2), (key1632, 2), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1), (key1465, -1), (key1443, -1), (key1797, -1), (key1592, -1), (key1824, -1), (key1666, -1), (key1392, -2), (key1773, -2), (key1547, -2), (key1456, 1), (key1425, 1), (key1789, 1), (key1574, 1), (key1814, 1), (key1656, 1)]

def rawRow2256 : Integer.Sparse Key := [(key1618, -1), (key1623, -1), (key1420, -1), (key1816, -1), (key1425, -1), (key1814, -1), (key1632, 2), (key1443, 2), (key1824, 2), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1), (key1592, -1), (key1666, -1), (key1443, -1), (key1824, -1), (key1465, -1), (key1797, -1), (key1547, -2), (key1392, -2), (key1773, -2), (key1574, 1), (key1656, 1), (key1425, 1), (key1814, 1), (key1456, 1), (key1789, 1)]

def rawRow2257 : Integer.Sparse Key := [(key1623, -1), (key1618, -1), (key1816, -1), (key1420, -1), (key1814, -1), (key1425, -1), (key1632, 2), (key1824, 2), (key1443, 2), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1), (key1666, -1), (key1592, -1), (key1824, -1), (key1443, -1), (key1797, -1), (key1465, -1), (key1547, -2), (key1773, -2), (key1392, -2), (key1656, 1), (key1574, 1), (key1814, 1), (key1425, 1), (key1789, 1), (key1456, 1)]

def rawRow2258 : Integer.Sparse Key := [(key1814, -1), (key1816, -1), (key1425, -1), (key1623, -1), (key1420, -1), (key1618, -1), (key1824, 2), (key1443, 2), (key1632, 2), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1), (key1797, -1), (key1824, -1), (key1465, -1), (key1666, -1), (key1443, -1), (key1592, -1), (key1773, -2), (key1392, -2), (key1547, -2), (key1789, 1), (key1814, 1), (key1456, 1), (key1656, 1), (key1425, 1), (key1574, 1)]

def rawRow2259 : Integer.Sparse Key := [(key1816, -1), (key1814, -1), (key1623, -1), (key1425, -1), (key1618, -1), (key1420, -1), (key1824, 2), (key1632, 2), (key1443, 2), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1), (key1824, -1), (key1797, -1), (key1666, -1), (key1465, -1), (key1592, -1), (key1443, -1), (key1773, -2), (key1547, -2), (key1392, -2), (key1814, 1), (key1789, 1), (key1656, 1), (key1456, 1), (key1574, 1), (key1425, 1)]

def rawRow2260 : Integer.Sparse Key := [(key1312, -1), (key1317, -1), (key1618, -1), (key1814, -1), (key1632, -1), (key1824, -1), (key1325, 2), (key1623, 2), (key1816, 2), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1), (key1325, -1), (key1344, -1), (key1555, -1), (key1779, -1), (key1658, -1), (key1816, -1), (key1297, -2), (key1574, -2), (key1789, -2), (key1317, 1), (key1338, 1), (key1547, 1), (key1773, 1), (key1656, 1), (key1814, 1)]

def rawRow2261 : Integer.Sparse Key := [(key1317, -1), (key1312, -1), (key1814, -1), (key1618, -1), (key1824, -1), (key1632, -1), (key1325, 2), (key1816, 2), (key1623, 2), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1), (key1344, -1), (key1325, -1), (key1779, -1), (key1555, -1), (key1816, -1), (key1658, -1), (key1297, -2), (key1789, -2), (key1574, -2), (key1338, 1), (key1317, 1), (key1773, 1), (key1547, 1), (key1814, 1), (key1656, 1)]

def rawRow2262 : Integer.Sparse Key := [(key1618, -1), (key1632, -1), (key1312, -1), (key1824, -1), (key1317, -1), (key1814, -1), (key1623, 2), (key1325, 2), (key1816, 2), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1), (key1555, -1), (key1658, -1), (key1325, -1), (key1816, -1), (key1344, -1), (key1779, -1), (key1574, -2), (key1297, -2), (key1789, -2), (key1547, 1), (key1656, 1), (key1317, 1), (key1814, 1), (key1338, 1), (key1773, 1)]

def rawRow2263 : Integer.Sparse Key := [(key1632, -1), (key1618, -1), (key1824, -1), (key1312, -1), (key1814, -1), (key1317, -1), (key1623, 2), (key1816, 2), (key1325, 2), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1), (key1658, -1), (key1555, -1), (key1816, -1), (key1325, -1), (key1779, -1), (key1344, -1), (key1574, -2), (key1789, -2), (key1297, -2), (key1656, 1), (key1547, 1), (key1814, 1), (key1317, 1), (key1773, 1), (key1338, 1)]

def rawRow2264 : Integer.Sparse Key := [(key1814, -1), (key1824, -1), (key1317, -1), (key1632, -1), (key1312, -1), (key1618, -1), (key1816, 2), (key1325, 2), (key1623, 2), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1), (key1779, -1), (key1816, -1), (key1344, -1), (key1658, -1), (key1325, -1), (key1555, -1), (key1789, -2), (key1297, -2), (key1574, -2), (key1773, 1), (key1814, 1), (key1338, 1), (key1656, 1), (key1317, 1), (key1547, 1)]

def rawRow2265 : Integer.Sparse Key := [(key1824, -1), (key1814, -1), (key1632, -1), (key1317, -1), (key1618, -1), (key1312, -1), (key1816, 2), (key1623, 2), (key1325, 2), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1), (key1816, -1), (key1779, -1), (key1658, -1), (key1344, -1), (key1555, -1), (key1325, -1), (key1789, -2), (key1574, -2), (key1297, -2), (key1814, 1), (key1773, 1), (key1656, 1), (key1338, 1), (key1547, 1), (key1317, 1)]

def rawRow2267 : Integer.Sparse Key := [(key3071, -2), (key3062, -2), (key3071, -2), (key3073, 2), (key3067, 2), (key3073, 2), (key3108, 2), (key3097, 2), (key3108, 2), (key3135, -6), (key3111, -2), (key3104, -2), (key3111, -2), (key3137, 6)]

def rawRow2268 : Integer.Sparse Key := [(key3071, -2), (key3071, -2), (key3062, -2), (key3073, 2), (key3073, 2), (key3067, 2), (key3108, 2), (key3108, 2), (key3097, 2), (key3135, -6), (key3111, -2), (key3111, -2), (key3104, -2), (key3137, 6)]

def rawRow2269 : Integer.Sparse Key := [(key3048, -2), (key3056, -2), (key3073, -2), (key3052, 2), (key3056, 2), (key3071, 2), (key3097, 2), (key3108, 2), (key3135, 2), (key3108, -6), (key3104, -2), (key3111, -2), (key3137, -2), (key3111, 6)]

def rawRow2270 : Integer.Sparse Key := [(key3056, -2), (key3048, -2), (key3073, -2), (key3056, 2), (key3052, 2), (key3071, 2), (key3108, 2), (key3097, 2), (key3135, 2), (key3108, -6), (key3111, -2), (key3104, -2), (key3137, -2), (key3111, 6)]

def rawRow2271 : Integer.Sparse Key := [(key3048, -2), (key3073, -2), (key3056, -2), (key3052, 2), (key3071, 2), (key3056, 2), (key3097, 2), (key3135, 2), (key3108, 2), (key3108, -6), (key3104, -2), (key3137, -2), (key3111, -2), (key3111, 6)]

def rawRow2272 : Integer.Sparse Key := [(key3073, -2), (key3048, -2), (key3056, -2), (key3071, 2), (key3052, 2), (key3056, 2), (key3135, 2), (key3097, 2), (key3108, 2), (key3108, -6), (key3137, -2), (key3104, -2), (key3111, -2), (key3111, 6)]

def rawRow2273 : Integer.Sparse Key := [(key3056, -2), (key3073, -2), (key3048, -2), (key3056, 2), (key3071, 2), (key3052, 2), (key3108, 2), (key3135, 2), (key3097, 2), (key3108, -6), (key3111, -2), (key3137, -2), (key3104, -2), (key3111, 6)]

def rawRow2274 : Integer.Sparse Key := [(key3073, -2), (key3056, -2), (key3048, -2), (key3071, 2), (key3056, 2), (key3052, 2), (key3135, 2), (key3108, 2), (key3097, 2), (key3108, -6), (key3137, -2), (key3111, -2), (key3104, -2), (key3111, 6)]

def rawRow2275 : Integer.Sparse Key := [(key3097, -2), (key3108, -2), (key3108, -2), (key3104, 2), (key3111, 2), (key3111, 2), (key3062, 2), (key3071, 2), (key3071, 2), (key3137, -6), (key3067, -2), (key3073, -2), (key3073, -2), (key3135, 6)]

def rawRow2276 : Integer.Sparse Key := [(key3108, -2), (key3097, -2), (key3108, -2), (key3111, 2), (key3104, 2), (key3111, 2), (key3071, 2), (key3062, 2), (key3071, 2), (key3137, -6), (key3073, -2), (key3067, -2), (key3073, -2), (key3135, 6)]

def rawRow2277 : Integer.Sparse Key := [(key3108, -2), (key3108, -2), (key3097, -2), (key3111, 2), (key3111, 2), (key3104, 2), (key3071, 2), (key3071, 2), (key3062, 2), (key3137, -6), (key3073, -2), (key3073, -2), (key3067, -2), (key3135, 6)]

def rawRow2278 : Integer.Sparse Key := [(key3048, -2), (key3056, -2), (key3111, -2), (key3052, 2), (key3056, 2), (key3108, 2), (key3062, 2), (key3071, 2), (key3137, 2), (key3071, -6), (key3067, -2), (key3073, -2), (key3135, -2), (key3073, 6)]

def rawRow2279 : Integer.Sparse Key := [(key3056, -2), (key3048, -2), (key3111, -2), (key3056, 2), (key3052, 2), (key3108, 2), (key3071, 2), (key3062, 2), (key3137, 2), (key3071, -6), (key3073, -2), (key3067, -2), (key3135, -2), (key3073, 6)]

def rawRow2280 : Integer.Sparse Key := [(key3048, -2), (key3111, -2), (key3056, -2), (key3052, 2), (key3108, 2), (key3056, 2), (key3062, 2), (key3137, 2), (key3071, 2), (key3071, -6), (key3067, -2), (key3135, -2), (key3073, -2), (key3073, 6)]

def rawRow2281 : Integer.Sparse Key := [(key3111, -2), (key3048, -2), (key3056, -2), (key3108, 2), (key3052, 2), (key3056, 2), (key3137, 2), (key3062, 2), (key3071, 2), (key3071, -6), (key3135, -2), (key3067, -2), (key3073, -2), (key3073, 6)]

def rawRow2282 : Integer.Sparse Key := [(key3056, -2), (key3111, -2), (key3048, -2), (key3056, 2), (key3108, 2), (key3052, 2), (key3071, 2), (key3137, 2), (key3062, 2), (key3071, -6), (key3073, -2), (key3135, -2), (key3067, -2), (key3073, 6)]

def rawRow2283 : Integer.Sparse Key := [(key3111, -2), (key3056, -2), (key3048, -2), (key3108, 2), (key3056, 2), (key3052, 2), (key3137, 2), (key3071, 2), (key3062, 2), (key3071, -6), (key3135, -2), (key3073, -2), (key3067, -2), (key3073, 6)]

def rawRow2284 : Integer.Sparse Key := [(key3097, -2), (key3108, -2), (key3135, -2), (key3104, 2), (key3111, 2), (key3137, 2), (key3048, 2), (key3056, 2), (key3073, 2), (key3111, -6), (key3052, -2), (key3056, -2), (key3071, -2), (key3108, 6)]

def rawRow2285 : Integer.Sparse Key := [(key3108, -2), (key3097, -2), (key3135, -2), (key3111, 2), (key3104, 2), (key3137, 2), (key3056, 2), (key3048, 2), (key3073, 2), (key3111, -6), (key3056, -2), (key3052, -2), (key3071, -2), (key3108, 6)]

def rawRow2286 : Integer.Sparse Key := [(key3097, -2), (key3135, -2), (key3108, -2), (key3104, 2), (key3137, 2), (key3111, 2), (key3048, 2), (key3073, 2), (key3056, 2), (key3111, -6), (key3052, -2), (key3071, -2), (key3056, -2), (key3108, 6)]

def rawRow2287 : Integer.Sparse Key := [(key3135, -2), (key3097, -2), (key3108, -2), (key3137, 2), (key3104, 2), (key3111, 2), (key3073, 2), (key3048, 2), (key3056, 2), (key3111, -6), (key3071, -2), (key3052, -2), (key3056, -2), (key3108, 6)]

def rawRow2288 : Integer.Sparse Key := [(key3108, -2), (key3135, -2), (key3097, -2), (key3111, 2), (key3137, 2), (key3104, 2), (key3056, 2), (key3073, 2), (key3048, 2), (key3111, -6), (key3056, -2), (key3071, -2), (key3052, -2), (key3108, 6)]

def rawRow2289 : Integer.Sparse Key := [(key3135, -2), (key3108, -2), (key3097, -2), (key3137, 2), (key3111, 2), (key3104, 2), (key3073, 2), (key3056, 2), (key3048, 2), (key3111, -6), (key3071, -2), (key3056, -2), (key3052, -2), (key3108, 6)]

def rawRow2290 : Integer.Sparse Key := [(key3062, -2), (key3071, -2), (key3137, -2), (key3067, 2), (key3073, 2), (key3135, 2), (key3048, 2), (key3056, 2), (key3111, 2), (key3073, -6), (key3052, -2), (key3056, -2), (key3108, -2), (key3071, 6)]

def rawRow2291 : Integer.Sparse Key := [(key3071, -2), (key3062, -2), (key3137, -2), (key3073, 2), (key3067, 2), (key3135, 2), (key3056, 2), (key3048, 2), (key3111, 2), (key3073, -6), (key3056, -2), (key3052, -2), (key3108, -2), (key3071, 6)]

def rawRow2292 : Integer.Sparse Key := [(key3062, -2), (key3137, -2), (key3071, -2), (key3067, 2), (key3135, 2), (key3073, 2), (key3048, 2), (key3111, 2), (key3056, 2), (key3073, -6), (key3052, -2), (key3108, -2), (key3056, -2), (key3071, 6)]

def rawRow2293 : Integer.Sparse Key := [(key3137, -2), (key3062, -2), (key3071, -2), (key3135, 2), (key3067, 2), (key3073, 2), (key3111, 2), (key3048, 2), (key3056, 2), (key3073, -6), (key3108, -2), (key3052, -2), (key3056, -2), (key3071, 6)]

def rawRow2294 : Integer.Sparse Key := [(key3071, -2), (key3137, -2), (key3062, -2), (key3073, 2), (key3135, 2), (key3067, 2), (key3056, 2), (key3111, 2), (key3048, 2), (key3073, -6), (key3056, -2), (key3108, -2), (key3052, -2), (key3071, 6)]

def rawRow2295 : Integer.Sparse Key := [(key3137, -2), (key3071, -2), (key3062, -2), (key3135, 2), (key3073, 2), (key3067, 2), (key3111, 2), (key3056, 2), (key3048, 2), (key3073, -6), (key3108, -2), (key3056, -2), (key3052, -2), (key3071, 6)]

def rawRow2296 : Integer.Sparse Key := [(key1292, -2), (key1297, -2), (key1297, -2), (key1312, 1), (key1317, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1338, 1), (key1387, 2), (key1392, 2), (key1392, 2), (key1542, -1), (key1547, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1773, -1), (key1420, -1), (key1425, -1), (key1420, -1), (key1456, -1), (key1425, -1), (key1456, -1), (key1569, 1), (key1574, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1789, 1)]

def rawRow2297 : Integer.Sparse Key := [(key1297, -2), (key1292, -2), (key1297, -2), (key1317, 1), (key1312, 1), (key1338, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1392, 2), (key1387, 2), (key1392, 2), (key1547, -1), (key1542, -1), (key1773, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1425, -1), (key1420, -1), (key1456, -1), (key1420, -1), (key1456, -1), (key1425, -1), (key1574, 1), (key1569, 1), (key1789, 1), (key1569, 1), (key1789, 1), (key1574, 1)]

def rawRow2298 : Integer.Sparse Key := [(key1297, -2), (key1297, -2), (key1292, -2), (key1338, 1), (key1338, 1), (key1317, 1), (key1317, 1), (key1312, 1), (key1312, 1), (key1392, 2), (key1392, 2), (key1387, 2), (key1773, -1), (key1773, -1), (key1547, -1), (key1547, -1), (key1542, -1), (key1542, -1), (key1456, -1), (key1456, -1), (key1425, -1), (key1425, -1), (key1420, -1), (key1420, -1), (key1789, 1), (key1789, 1), (key1574, 1), (key1574, 1), (key1569, 1), (key1569, 1)]

def rawRow2299 : Integer.Sparse Key := [(key1312, -2), (key1317, -2), (key1325, -2), (key1292, 1), (key1297, 1), (key1312, 1), (key1338, 1), (key1325, 1), (key1344, 1), (key1542, 2), (key1547, 2), (key1555, 2), (key1387, -1), (key1392, -1), (key1542, -1), (key1773, -1), (key1555, -1), (key1779, -1), (key1569, -1), (key1574, -1), (key1618, -1), (key1656, -1), (key1623, -1), (key1658, -1), (key1420, 1), (key1425, 1), (key1618, 1), (key1814, 1), (key1623, 1), (key1816, 1)]

def rawRow2300 : Integer.Sparse Key := [(key1317, -2), (key1312, -2), (key1325, -2), (key1297, 1), (key1292, 1), (key1338, 1), (key1312, 1), (key1344, 1), (key1325, 1), (key1547, 2), (key1542, 2), (key1555, 2), (key1392, -1), (key1387, -1), (key1773, -1), (key1542, -1), (key1779, -1), (key1555, -1), (key1574, -1), (key1569, -1), (key1656, -1), (key1618, -1), (key1658, -1), (key1623, -1), (key1425, 1), (key1420, 1), (key1814, 1), (key1618, 1), (key1816, 1), (key1623, 1)]

def rawRow2301 : Integer.Sparse Key := [(key1312, -2), (key1325, -2), (key1317, -2), (key1312, 1), (key1325, 1), (key1292, 1), (key1344, 1), (key1297, 1), (key1338, 1), (key1542, 2), (key1555, 2), (key1547, 2), (key1542, -1), (key1555, -1), (key1387, -1), (key1779, -1), (key1392, -1), (key1773, -1), (key1618, -1), (key1623, -1), (key1569, -1), (key1658, -1), (key1574, -1), (key1656, -1), (key1618, 1), (key1623, 1), (key1420, 1), (key1816, 1), (key1425, 1), (key1814, 1)]

def rawRow2302 : Integer.Sparse Key := [(key1325, -2), (key1312, -2), (key1317, -2), (key1325, 1), (key1312, 1), (key1344, 1), (key1292, 1), (key1338, 1), (key1297, 1), (key1555, 2), (key1542, 2), (key1547, 2), (key1555, -1), (key1542, -1), (key1779, -1), (key1387, -1), (key1773, -1), (key1392, -1), (key1623, -1), (key1618, -1), (key1658, -1), (key1569, -1), (key1656, -1), (key1574, -1), (key1623, 1), (key1618, 1), (key1816, 1), (key1420, 1), (key1814, 1), (key1425, 1)]

def rawRow2303 : Integer.Sparse Key := [(key1317, -2), (key1325, -2), (key1312, -2), (key1338, 1), (key1344, 1), (key1297, 1), (key1325, 1), (key1292, 1), (key1312, 1), (key1547, 2), (key1555, 2), (key1542, 2), (key1773, -1), (key1779, -1), (key1392, -1), (key1555, -1), (key1387, -1), (key1542, -1), (key1656, -1), (key1658, -1), (key1574, -1), (key1623, -1), (key1569, -1), (key1618, -1), (key1814, 1), (key1816, 1), (key1425, 1), (key1623, 1), (key1420, 1), (key1618, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2304 : Integer.Sparse Key := [(key1325, -2), (key1317, -2), (key1312, -2), (key1344, 1), (key1338, 1), (key1325, 1), (key1297, 1), (key1312, 1), (key1292, 1), (key1555, 2), (key1547, 2), (key1542, 2), (key1779, -1), (key1773, -1), (key1555, -1), (key1392, -1), (key1542, -1), (key1387, -1), (key1658, -1), (key1656, -1), (key1623, -1), (key1574, -1), (key1618, -1), (key1569, -1), (key1816, 1), (key1814, 1), (key1623, 1), (key1425, 1), (key1618, 1), (key1420, 1)]

def rawRow2305 : Integer.Sparse Key := [(key1387, -2), (key1392, -2), (key1392, -2), (key1420, 1), (key1425, 1), (key1420, 1), (key1456, 1), (key1425, 1), (key1456, 1), (key1292, 2), (key1297, 2), (key1297, 2), (key1569, -1), (key1574, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1789, -1), (key1312, -1), (key1317, -1), (key1312, -1), (key1338, -1), (key1317, -1), (key1338, -1), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1)]

def rawRow2306 : Integer.Sparse Key := [(key1392, -2), (key1387, -2), (key1392, -2), (key1425, 1), (key1420, 1), (key1456, 1), (key1420, 1), (key1456, 1), (key1425, 1), (key1297, 2), (key1292, 2), (key1297, 2), (key1574, -1), (key1569, -1), (key1789, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1317, -1), (key1312, -1), (key1338, -1), (key1312, -1), (key1338, -1), (key1317, -1), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1)]

def rawRow2307 : Integer.Sparse Key := [(key1392, -2), (key1392, -2), (key1387, -2), (key1456, 1), (key1456, 1), (key1425, 1), (key1425, 1), (key1420, 1), (key1420, 1), (key1297, 2), (key1297, 2), (key1292, 2), (key1789, -1), (key1789, -1), (key1574, -1), (key1574, -1), (key1569, -1), (key1569, -1), (key1338, -1), (key1338, -1), (key1317, -1), (key1317, -1), (key1312, -1), (key1312, -1), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1)]

def rawRow2308 : Integer.Sparse Key := [(key1420, -2), (key1425, -2), (key1443, -2), (key1387, 1), (key1392, 1), (key1420, 1), (key1456, 1), (key1443, 1), (key1465, 1), (key1569, 2), (key1574, 2), (key1592, 2), (key1292, -1), (key1297, -1), (key1569, -1), (key1789, -1), (key1592, -1), (key1797, -1), (key1542, -1), (key1547, -1), (key1618, -1), (key1656, -1), (key1632, -1), (key1666, -1), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1)]

def rawRow2309 : Integer.Sparse Key := [(key1425, -2), (key1420, -2), (key1443, -2), (key1392, 1), (key1387, 1), (key1456, 1), (key1420, 1), (key1465, 1), (key1443, 1), (key1574, 2), (key1569, 2), (key1592, 2), (key1297, -1), (key1292, -1), (key1789, -1), (key1569, -1), (key1797, -1), (key1592, -1), (key1547, -1), (key1542, -1), (key1656, -1), (key1618, -1), (key1666, -1), (key1632, -1), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1)]

def rawRow2310 : Integer.Sparse Key := [(key1420, -2), (key1443, -2), (key1425, -2), (key1420, 1), (key1443, 1), (key1387, 1), (key1465, 1), (key1392, 1), (key1456, 1), (key1569, 2), (key1592, 2), (key1574, 2), (key1569, -1), (key1592, -1), (key1292, -1), (key1797, -1), (key1297, -1), (key1789, -1), (key1618, -1), (key1632, -1), (key1542, -1), (key1666, -1), (key1547, -1), (key1656, -1), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1)]

def rawRow2311 : Integer.Sparse Key := [(key1443, -2), (key1420, -2), (key1425, -2), (key1443, 1), (key1420, 1), (key1465, 1), (key1387, 1), (key1456, 1), (key1392, 1), (key1592, 2), (key1569, 2), (key1574, 2), (key1592, -1), (key1569, -1), (key1797, -1), (key1292, -1), (key1789, -1), (key1297, -1), (key1632, -1), (key1618, -1), (key1666, -1), (key1542, -1), (key1656, -1), (key1547, -1), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1)]

def rawRow2312 : Integer.Sparse Key := [(key1425, -2), (key1443, -2), (key1420, -2), (key1456, 1), (key1465, 1), (key1392, 1), (key1443, 1), (key1387, 1), (key1420, 1), (key1574, 2), (key1592, 2), (key1569, 2), (key1789, -1), (key1797, -1), (key1297, -1), (key1592, -1), (key1292, -1), (key1569, -1), (key1656, -1), (key1666, -1), (key1547, -1), (key1632, -1), (key1542, -1), (key1618, -1), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1)]

def rawRow2313 : Integer.Sparse Key := [(key1443, -2), (key1425, -2), (key1420, -2), (key1465, 1), (key1456, 1), (key1443, 1), (key1392, 1), (key1420, 1), (key1387, 1), (key1592, 2), (key1574, 2), (key1569, 2), (key1797, -1), (key1789, -1), (key1592, -1), (key1297, -1), (key1569, -1), (key1292, -1), (key1666, -1), (key1656, -1), (key1632, -1), (key1547, -1), (key1618, -1), (key1542, -1), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1)]

def rawRow2314 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, -2), (key1569, 1), (key1574, 1), (key1618, 1), (key1656, 1), (key1623, 1), (key1658, 1), (key1312, 2), (key1317, 2), (key1325, 2), (key1420, -1), (key1425, -1), (key1618, -1), (key1814, -1), (key1623, -1), (key1816, -1), (key1292, -1), (key1297, -1), (key1312, -1), (key1338, -1), (key1325, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1)]

def rawRow2315 : Integer.Sparse Key := [(key1547, -2), (key1542, -2), (key1555, -2), (key1574, 1), (key1569, 1), (key1656, 1), (key1618, 1), (key1658, 1), (key1623, 1), (key1317, 2), (key1312, 2), (key1325, 2), (key1425, -1), (key1420, -1), (key1814, -1), (key1618, -1), (key1816, -1), (key1623, -1), (key1297, -1), (key1292, -1), (key1338, -1), (key1312, -1), (key1344, -1), (key1325, -1), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1)]

def rawRow2316 : Integer.Sparse Key := [(key1542, -2), (key1555, -2), (key1547, -2), (key1618, 1), (key1623, 1), (key1569, 1), (key1658, 1), (key1574, 1), (key1656, 1), (key1312, 2), (key1325, 2), (key1317, 2), (key1618, -1), (key1623, -1), (key1420, -1), (key1816, -1), (key1425, -1), (key1814, -1), (key1312, -1), (key1325, -1), (key1292, -1), (key1344, -1), (key1297, -1), (key1338, -1), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1)]

def rawRow2317 : Integer.Sparse Key := [(key1555, -2), (key1542, -2), (key1547, -2), (key1623, 1), (key1618, 1), (key1658, 1), (key1569, 1), (key1656, 1), (key1574, 1), (key1325, 2), (key1312, 2), (key1317, 2), (key1623, -1), (key1618, -1), (key1816, -1), (key1420, -1), (key1814, -1), (key1425, -1), (key1325, -1), (key1312, -1), (key1344, -1), (key1292, -1), (key1338, -1), (key1297, -1), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1)]

def rawRow2318 : Integer.Sparse Key := [(key1547, -2), (key1555, -2), (key1542, -2), (key1656, 1), (key1658, 1), (key1574, 1), (key1623, 1), (key1569, 1), (key1618, 1), (key1317, 2), (key1325, 2), (key1312, 2), (key1814, -1), (key1816, -1), (key1425, -1), (key1623, -1), (key1420, -1), (key1618, -1), (key1338, -1), (key1344, -1), (key1297, -1), (key1325, -1), (key1292, -1), (key1312, -1), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1)]

def rawRow2319 : Integer.Sparse Key := [(key1555, -2), (key1547, -2), (key1542, -2), (key1658, 1), (key1656, 1), (key1623, 1), (key1574, 1), (key1618, 1), (key1569, 1), (key1325, 2), (key1317, 2), (key1312, 2), (key1816, -1), (key1814, -1), (key1623, -1), (key1425, -1), (key1618, -1), (key1420, -1), (key1344, -1), (key1338, -1), (key1325, -1), (key1297, -1), (key1312, -1), (key1292, -1), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1)]

def rawRow2320 : Integer.Sparse Key := [(key1569, -2), (key1574, -2), (key1592, -2), (key1542, 1), (key1547, 1), (key1618, 1), (key1656, 1), (key1632, 1), (key1666, 1), (key1420, 2), (key1425, 2), (key1443, 2), (key1312, -1), (key1317, -1), (key1618, -1), (key1814, -1), (key1632, -1), (key1824, -1), (key1387, -1), (key1392, -1), (key1420, -1), (key1456, -1), (key1443, -1), (key1465, -1), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1)]

def rawRow2321 : Integer.Sparse Key := [(key1574, -2), (key1569, -2), (key1592, -2), (key1547, 1), (key1542, 1), (key1656, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1425, 2), (key1420, 2), (key1443, 2), (key1317, -1), (key1312, -1), (key1814, -1), (key1618, -1), (key1824, -1), (key1632, -1), (key1392, -1), (key1387, -1), (key1456, -1), (key1420, -1), (key1465, -1), (key1443, -1), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1)]

def rawRow2322 : Integer.Sparse Key := [(key1569, -2), (key1592, -2), (key1574, -2), (key1618, 1), (key1632, 1), (key1542, 1), (key1666, 1), (key1547, 1), (key1656, 1), (key1420, 2), (key1443, 2), (key1425, 2), (key1618, -1), (key1632, -1), (key1312, -1), (key1824, -1), (key1317, -1), (key1814, -1), (key1420, -1), (key1443, -1), (key1387, -1), (key1465, -1), (key1392, -1), (key1456, -1), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1)]

def rawRow2323 : Integer.Sparse Key := [(key1592, -2), (key1569, -2), (key1574, -2), (key1632, 1), (key1618, 1), (key1666, 1), (key1542, 1), (key1656, 1), (key1547, 1), (key1443, 2), (key1420, 2), (key1425, 2), (key1632, -1), (key1618, -1), (key1824, -1), (key1312, -1), (key1814, -1), (key1317, -1), (key1443, -1), (key1420, -1), (key1465, -1), (key1387, -1), (key1456, -1), (key1392, -1), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1)]

def rawRow2324 : Integer.Sparse Key := [(key1574, -2), (key1592, -2), (key1569, -2), (key1656, 1), (key1666, 1), (key1547, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1425, 2), (key1443, 2), (key1420, 2), (key1814, -1), (key1824, -1), (key1317, -1), (key1632, -1), (key1312, -1), (key1618, -1), (key1456, -1), (key1465, -1), (key1392, -1), (key1443, -1), (key1387, -1), (key1420, -1), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1)]

def rawRow2325 : Integer.Sparse Key := [(key1592, -2), (key1574, -2), (key1569, -2), (key1666, 1), (key1656, 1), (key1632, 1), (key1547, 1), (key1618, 1), (key1542, 1), (key1443, 2), (key1425, 2), (key1420, 2), (key1824, -1), (key1814, -1), (key1632, -1), (key1317, -1), (key1618, -1), (key1312, -1), (key1465, -1), (key1456, -1), (key1443, -1), (key1392, -1), (key1420, -1), (key1387, -1), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1)]

def rawRow2326 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key997, -2), (key1012, 6), (key1028, 2), (key1032, 2), (key1032, 2), (key1120, -2), (key1120, -2), (key1196, -2), (key1068, -6), (key1147, 2), (key1147, 2), (key1209, 2)]

def rawRow2327 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key997, -2), (key1012, 6), (key1032, 2), (key1028, 2), (key1032, 2), (key1120, -2), (key1196, -2), (key1120, -2), (key1068, -6), (key1147, 2), (key1209, 2), (key1147, 2)]

def rawRow2328 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key993, -2), (key1012, 6), (key1032, 2), (key1032, 2), (key1028, 2), (key1196, -2), (key1120, -2), (key1120, -2), (key1068, -6), (key1209, 2), (key1147, 2), (key1147, 2)]

def rawRow2329 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key1012, -2), (key997, 6), (key1106, 2), (key1110, 2), (key1120, 2), (key1032, -2), (key1110, -2), (key1189, -2), (key1147, -6), (key1068, 2), (key1147, 2), (key1209, 2)]

def rawRow2330 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key1012, -2), (key997, 6), (key1110, 2), (key1106, 2), (key1120, 2), (key1032, -2), (key1189, -2), (key1110, -2), (key1147, -6), (key1068, 2), (key1209, 2), (key1147, 2)]

def rawRow2331 : Integer.Sparse Key := [(key993, -2), (key1012, -2), (key997, -2), (key997, 6), (key1106, 2), (key1120, 2), (key1110, 2), (key1110, -2), (key1032, -2), (key1189, -2), (key1147, -6), (key1147, 2), (key1068, 2), (key1209, 2)]

def rawRow2332 : Integer.Sparse Key := [(key1012, -2), (key993, -2), (key997, -2), (key997, 6), (key1120, 2), (key1106, 2), (key1110, 2), (key1110, -2), (key1189, -2), (key1032, -2), (key1147, -6), (key1147, 2), (key1209, 2), (key1068, 2)]

def rawRow2333 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key993, -2), (key997, 6), (key1110, 2), (key1120, 2), (key1106, 2), (key1189, -2), (key1032, -2), (key1110, -2), (key1147, -6), (key1209, 2), (key1068, 2), (key1147, 2)]

def rawRow2334 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key993, -2), (key997, 6), (key1120, 2), (key1110, 2), (key1106, 2), (key1189, -2), (key1110, -2), (key1032, -2), (key1147, -6), (key1209, 2), (key1147, 2), (key1068, 2)]

def rawRow2335 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1032, -2), (key1068, 6), (key993, 2), (key997, 2), (key997, 2), (key1147, -2), (key1147, -2), (key1209, -2), (key1012, -6), (key1120, 2), (key1120, 2), (key1196, 2)]

def rawRow2336 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1032, -2), (key1068, 6), (key997, 2), (key993, 2), (key997, 2), (key1147, -2), (key1209, -2), (key1147, -2), (key1012, -6), (key1120, 2), (key1196, 2), (key1120, 2)]

def rawRow2337 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1028, -2), (key1068, 6), (key997, 2), (key997, 2), (key993, 2), (key1209, -2), (key1147, -2), (key1147, -2), (key1012, -6), (key1196, 2), (key1120, 2), (key1120, 2)]

def rawRow2338 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1068, -2), (key1032, 6), (key1106, 2), (key1110, 2), (key1147, 2), (key997, -2), (key1110, -2), (key1189, -2), (key1120, -6), (key1012, 2), (key1120, 2), (key1196, 2)]

def rawRow2339 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1068, -2), (key1032, 6), (key1110, 2), (key1106, 2), (key1147, 2), (key997, -2), (key1189, -2), (key1110, -2), (key1120, -6), (key1012, 2), (key1196, 2), (key1120, 2)]

def rawRow2340 : Integer.Sparse Key := [(key1028, -2), (key1068, -2), (key1032, -2), (key1032, 6), (key1106, 2), (key1147, 2), (key1110, 2), (key1110, -2), (key997, -2), (key1189, -2), (key1120, -6), (key1120, 2), (key1012, 2), (key1196, 2)]

def rawRow2341 : Integer.Sparse Key := [(key1068, -2), (key1028, -2), (key1032, -2), (key1032, 6), (key1147, 2), (key1106, 2), (key1110, 2), (key1110, -2), (key1189, -2), (key997, -2), (key1120, -6), (key1120, 2), (key1196, 2), (key1012, 2)]

def rawRow2342 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1028, -2), (key1032, 6), (key1110, 2), (key1147, 2), (key1106, 2), (key1189, -2), (key997, -2), (key1110, -2), (key1120, -6), (key1196, 2), (key1012, 2), (key1120, 2)]

def rawRow2343 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1028, -2), (key1032, 6), (key1147, 2), (key1110, 2), (key1106, 2), (key1189, -2), (key1110, -2), (key997, -2), (key1120, -6), (key1196, 2), (key1120, 2), (key1012, 2)]

def rawRow2344 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1120, -2), (key1147, 6), (key993, 2), (key997, 2), (key1012, 2), (key1068, -2), (key1147, -2), (key1209, -2), (key997, -6), (key1032, 2), (key1110, 2), (key1189, 2)]

def rawRow2345 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1120, -2), (key1147, 6), (key997, 2), (key993, 2), (key1012, 2), (key1068, -2), (key1209, -2), (key1147, -2), (key997, -6), (key1032, 2), (key1189, 2), (key1110, 2)]

def rawRow2346 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1110, -2), (key1147, 6), (key993, 2), (key1012, 2), (key997, 2), (key1147, -2), (key1068, -2), (key1209, -2), (key997, -6), (key1110, 2), (key1032, 2), (key1189, 2)]

def rawRow2347 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1110, -2), (key1147, 6), (key1012, 2), (key993, 2), (key997, 2), (key1147, -2), (key1209, -2), (key1068, -2), (key997, -6), (key1110, 2), (key1189, 2), (key1032, 2)]

def rawRow2348 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1106, -2), (key1147, 6), (key997, 2), (key1012, 2), (key993, 2), (key1209, -2), (key1068, -2), (key1147, -2), (key997, -6), (key1189, 2), (key1032, 2), (key1110, 2)]

def rawRow2349 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1106, -2), (key1147, 6), (key1012, 2), (key997, 2), (key993, 2), (key1209, -2), (key1147, -2), (key1068, -2), (key997, -6), (key1189, 2), (key1110, 2), (key1032, 2)]

def rawRow2350 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1147, -2), (key1120, 6), (key1028, 2), (key1032, 2), (key1068, 2), (key1012, -2), (key1120, -2), (key1196, -2), (key1032, -6), (key997, 2), (key1110, 2), (key1189, 2)]

def rawRow2351 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1147, -2), (key1120, 6), (key1032, 2), (key1028, 2), (key1068, 2), (key1012, -2), (key1196, -2), (key1120, -2), (key1032, -6), (key997, 2), (key1189, 2), (key1110, 2)]

def rawRow2352 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1110, -2), (key1120, 6), (key1028, 2), (key1068, 2), (key1032, 2), (key1120, -2), (key1012, -2), (key1196, -2), (key1032, -6), (key1110, 2), (key997, 2), (key1189, 2)]

def rawRow2353 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1110, -2), (key1120, 6), (key1068, 2), (key1028, 2), (key1032, 2), (key1120, -2), (key1196, -2), (key1012, -2), (key1032, -6), (key1110, 2), (key1189, 2), (key997, 2)]

def rawRow2354 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1106, -2), (key1120, 6), (key1032, 2), (key1068, 2), (key1028, 2), (key1196, -2), (key1012, -2), (key1120, -2), (key1032, -6), (key1189, 2), (key997, 2), (key1110, 2)]

def rawRow2355 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1106, -2), (key1120, 6), (key1068, 2), (key1032, 2), (key1028, 2), (key1196, -2), (key1120, -2), (key1012, -2), (key1032, -6), (key1189, 2), (key1110, 2), (key997, 2)]

def rawRow2356 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2640, 1), (key2642, 1), (key2640, 1), (key2654, 1), (key2642, 1), (key2654, 1), (key2706, 2), (key2706, 2), (key2738, 2), (key2860, -1), (key2898, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2977, -1), (key2726, -1), (key2729, -1), (key2726, -1), (key2748, -1), (key2729, -1), (key2748, -1), (key2870, 1), (key2905, 1), (key2870, 1), (key2984, 1), (key2905, 1), (key2984, 1)]

def rawRow2357 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2642, 1), (key2640, 1), (key2654, 1), (key2640, 1), (key2654, 1), (key2642, 1), (key2706, 2), (key2738, 2), (key2706, 2), (key2898, -1), (key2860, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2729, -1), (key2726, -1), (key2748, -1), (key2726, -1), (key2748, -1), (key2729, -1), (key2905, 1), (key2870, 1), (key2984, 1), (key2870, 1), (key2984, 1), (key2905, 1)]

def rawRow2358 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2654, 1), (key2654, 1), (key2642, 1), (key2642, 1), (key2640, 1), (key2640, 1), (key2738, 2), (key2706, 2), (key2706, 2), (key2977, -1), (key2977, -1), (key2898, -1), (key2898, -1), (key2860, -1), (key2860, -1), (key2748, -1), (key2748, -1), (key2729, -1), (key2729, -1), (key2726, -1), (key2726, -1), (key2984, 1), (key2984, 1), (key2905, 1), (key2905, 1), (key2870, 1), (key2870, 1)]

def rawRow2359 : Integer.Sparse Key := [(key2616, -2), (key2640, -2), (key2654, -2), (key2616, 1), (key2619, 1), (key2632, 1), (key2649, 1), (key2642, 1), (key2654, 1), (key2809, 2), (key2860, 2), (key2898, 2), (key2706, -1), (key2738, -1), (key2809, -1), (key2951, -1), (key2898, -1), (key2977, -1), (key2829, -1), (key2832, -1), (key2870, -1), (key2905, -1), (key2883, -1), (key2913, -1), (key2726, 1), (key2748, 1), (key2829, 1), (key2961, 1), (key2913, 1), (key2992, 1)]

def rawRow2360 : Integer.Sparse Key := [(key2616, -2), (key2654, -2), (key2640, -2), (key2619, 1), (key2616, 1), (key2649, 1), (key2632, 1), (key2654, 1), (key2642, 1), (key2809, 2), (key2898, 2), (key2860, 2), (key2738, -1), (key2706, -1), (key2951, -1), (key2809, -1), (key2977, -1), (key2898, -1), (key2832, -1), (key2829, -1), (key2905, -1), (key2870, -1), (key2913, -1), (key2883, -1), (key2748, 1), (key2726, 1), (key2961, 1), (key2829, 1), (key2992, 1), (key2913, 1)]

def rawRow2361 : Integer.Sparse Key := [(key2640, -2), (key2616, -2), (key2654, -2), (key2632, 1), (key2642, 1), (key2616, 1), (key2654, 1), (key2619, 1), (key2649, 1), (key2860, 2), (key2809, 2), (key2898, 2), (key2809, -1), (key2898, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2870, -1), (key2883, -1), (key2829, -1), (key2913, -1), (key2832, -1), (key2905, -1), (key2829, 1), (key2913, 1), (key2726, 1), (key2992, 1), (key2748, 1), (key2961, 1)]

def rawRow2362 : Integer.Sparse Key := [(key2640, -2), (key2654, -2), (key2616, -2), (key2642, 1), (key2632, 1), (key2654, 1), (key2616, 1), (key2649, 1), (key2619, 1), (key2860, 2), (key2898, 2), (key2809, 2), (key2898, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2951, -1), (key2738, -1), (key2883, -1), (key2870, -1), (key2913, -1), (key2829, -1), (key2905, -1), (key2832, -1), (key2913, 1), (key2829, 1), (key2992, 1), (key2726, 1), (key2961, 1), (key2748, 1)]

def rawRow2363 : Integer.Sparse Key := [(key2654, -2), (key2616, -2), (key2640, -2), (key2649, 1), (key2654, 1), (key2619, 1), (key2642, 1), (key2616, 1), (key2632, 1), (key2898, 2), (key2809, 2), (key2860, 2), (key2951, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2706, -1), (key2809, -1), (key2905, -1), (key2913, -1), (key2832, -1), (key2883, -1), (key2829, -1), (key2870, -1), (key2961, 1), (key2992, 1), (key2748, 1), (key2913, 1), (key2726, 1), (key2829, 1)]

def rawRow2364 : Integer.Sparse Key := [(key2654, -2), (key2640, -2), (key2616, -2), (key2654, 1), (key2649, 1), (key2642, 1), (key2619, 1), (key2632, 1), (key2616, 1), (key2898, 2), (key2860, 2), (key2809, 2), (key2977, -1), (key2951, -1), (key2898, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2913, -1), (key2905, -1), (key2883, -1), (key2832, -1), (key2870, -1), (key2829, -1), (key2992, 1), (key2961, 1), (key2913, 1), (key2748, 1), (key2829, 1), (key2726, 1)]

def rawRow2365 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2726, 1), (key2729, 1), (key2726, 1), (key2748, 1), (key2729, 1), (key2748, 1), (key2632, 2), (key2632, 2), (key2649, 2), (key2870, -1), (key2905, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2984, -1), (key2640, -1), (key2642, -1), (key2640, -1), (key2654, -1), (key2642, -1), (key2654, -1), (key2860, 1), (key2898, 1), (key2860, 1), (key2977, 1), (key2898, 1), (key2977, 1)]

def rawRow2366 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2729, 1), (key2726, 1), (key2748, 1), (key2726, 1), (key2748, 1), (key2729, 1), (key2632, 2), (key2649, 2), (key2632, 2), (key2905, -1), (key2870, -1), (key2984, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2642, -1), (key2640, -1), (key2654, -1), (key2640, -1), (key2654, -1), (key2642, -1), (key2898, 1), (key2860, 1), (key2977, 1), (key2860, 1), (key2977, 1), (key2898, 1)]

def rawRow2367 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2748, 1), (key2748, 1), (key2729, 1), (key2729, 1), (key2726, 1), (key2726, 1), (key2649, 2), (key2632, 2), (key2632, 2), (key2984, -1), (key2984, -1), (key2905, -1), (key2905, -1), (key2870, -1), (key2870, -1), (key2654, -1), (key2654, -1), (key2642, -1), (key2642, -1), (key2640, -1), (key2640, -1), (key2977, 1), (key2977, 1), (key2898, 1), (key2898, 1), (key2860, 1), (key2860, 1)]

def rawRow2368 : Integer.Sparse Key := [(key2671, -2), (key2726, -2), (key2748, -2), (key2671, 1), (key2674, 1), (key2706, 1), (key2738, 1), (key2729, 1), (key2748, 1), (key2786, 2), (key2870, 2), (key2905, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2939, -1), (key2905, -1), (key2984, -1), (key2794, -1), (key2796, -1), (key2860, -1), (key2898, -1), (key2883, -1), (key2913, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2944, 1), (key2913, 1), (key2992, 1)]

def rawRow2369 : Integer.Sparse Key := [(key2671, -2), (key2748, -2), (key2726, -2), (key2674, 1), (key2671, 1), (key2738, 1), (key2706, 1), (key2748, 1), (key2729, 1), (key2786, 2), (key2905, 2), (key2870, 2), (key2649, -1), (key2632, -1), (key2939, -1), (key2786, -1), (key2984, -1), (key2905, -1), (key2796, -1), (key2794, -1), (key2898, -1), (key2860, -1), (key2913, -1), (key2883, -1), (key2654, 1), (key2640, 1), (key2944, 1), (key2794, 1), (key2992, 1), (key2913, 1)]

def rawRow2370 : Integer.Sparse Key := [(key2726, -2), (key2671, -2), (key2748, -2), (key2706, 1), (key2729, 1), (key2671, 1), (key2748, 1), (key2674, 1), (key2738, 1), (key2870, 2), (key2786, 2), (key2905, 2), (key2786, -1), (key2905, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2860, -1), (key2883, -1), (key2794, -1), (key2913, -1), (key2796, -1), (key2898, -1), (key2794, 1), (key2913, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2944, 1)]

def rawRow2371 : Integer.Sparse Key := [(key2726, -2), (key2748, -2), (key2671, -2), (key2729, 1), (key2706, 1), (key2748, 1), (key2671, 1), (key2738, 1), (key2674, 1), (key2870, 2), (key2905, 2), (key2786, 2), (key2905, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2939, -1), (key2649, -1), (key2883, -1), (key2860, -1), (key2913, -1), (key2794, -1), (key2898, -1), (key2796, -1), (key2913, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2944, 1), (key2654, 1)]

def rawRow2372 : Integer.Sparse Key := [(key2748, -2), (key2671, -2), (key2726, -2), (key2738, 1), (key2748, 1), (key2674, 1), (key2729, 1), (key2671, 1), (key2706, 1), (key2905, 2), (key2786, 2), (key2870, 2), (key2939, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2632, -1), (key2786, -1), (key2898, -1), (key2913, -1), (key2796, -1), (key2883, -1), (key2794, -1), (key2860, -1), (key2944, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2640, 1), (key2794, 1)]

def rawRow2373 : Integer.Sparse Key := [(key2748, -2), (key2726, -2), (key2671, -2), (key2748, 1), (key2738, 1), (key2729, 1), (key2674, 1), (key2706, 1), (key2671, 1), (key2905, 2), (key2870, 2), (key2786, 2), (key2984, -1), (key2939, -1), (key2905, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2913, -1), (key2898, -1), (key2883, -1), (key2796, -1), (key2860, -1), (key2794, -1), (key2992, 1), (key2944, 1), (key2913, 1), (key2654, 1), (key2794, 1), (key2640, 1)]

def rawRow2374 : Integer.Sparse Key := [(key2809, -2), (key2860, -2), (key2898, -2), (key2829, 1), (key2832, 1), (key2870, 1), (key2905, 1), (key2883, 1), (key2913, 1), (key2616, 2), (key2640, 2), (key2654, 2), (key2726, -1), (key2748, -1), (key2829, -1), (key2961, -1), (key2913, -1), (key2992, -1), (key2616, -1), (key2619, -1), (key2632, -1), (key2649, -1), (key2642, -1), (key2654, -1), (key2706, 1), (key2738, 1), (key2809, 1), (key2951, 1), (key2898, 1), (key2977, 1)]

def rawRow2375 : Integer.Sparse Key := [(key2809, -2), (key2898, -2), (key2860, -2), (key2832, 1), (key2829, 1), (key2905, 1), (key2870, 1), (key2913, 1), (key2883, 1), (key2616, 2), (key2654, 2), (key2640, 2), (key2748, -1), (key2726, -1), (key2961, -1), (key2829, -1), (key2992, -1), (key2913, -1), (key2619, -1), (key2616, -1), (key2649, -1), (key2632, -1), (key2654, -1), (key2642, -1), (key2738, 1), (key2706, 1), (key2951, 1), (key2809, 1), (key2977, 1), (key2898, 1)]

def rawRow2376 : Integer.Sparse Key := [(key2860, -2), (key2809, -2), (key2898, -2), (key2870, 1), (key2883, 1), (key2829, 1), (key2913, 1), (key2832, 1), (key2905, 1), (key2640, 2), (key2616, 2), (key2654, 2), (key2829, -1), (key2913, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2632, -1), (key2642, -1), (key2616, -1), (key2654, -1), (key2619, -1), (key2649, -1), (key2809, 1), (key2898, 1), (key2706, 1), (key2977, 1), (key2738, 1), (key2951, 1)]

def rawRow2377 : Integer.Sparse Key := [(key2860, -2), (key2898, -2), (key2809, -2), (key2883, 1), (key2870, 1), (key2913, 1), (key2829, 1), (key2905, 1), (key2832, 1), (key2640, 2), (key2654, 2), (key2616, 2), (key2913, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2961, -1), (key2748, -1), (key2642, -1), (key2632, -1), (key2654, -1), (key2616, -1), (key2649, -1), (key2619, -1), (key2898, 1), (key2809, 1), (key2977, 1), (key2706, 1), (key2951, 1), (key2738, 1)]

def rawRow2378 : Integer.Sparse Key := [(key2898, -2), (key2809, -2), (key2860, -2), (key2905, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2829, 1), (key2870, 1), (key2654, 2), (key2616, 2), (key2640, 2), (key2961, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2726, -1), (key2829, -1), (key2649, -1), (key2654, -1), (key2619, -1), (key2642, -1), (key2616, -1), (key2632, -1), (key2951, 1), (key2977, 1), (key2738, 1), (key2898, 1), (key2706, 1), (key2809, 1)]

def rawRow2379 : Integer.Sparse Key := [(key2898, -2), (key2860, -2), (key2809, -2), (key2913, 1), (key2905, 1), (key2883, 1), (key2832, 1), (key2870, 1), (key2829, 1), (key2654, 2), (key2640, 2), (key2616, 2), (key2992, -1), (key2961, -1), (key2913, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2654, -1), (key2649, -1), (key2642, -1), (key2619, -1), (key2632, -1), (key2616, -1), (key2977, 1), (key2951, 1), (key2898, 1), (key2738, 1), (key2809, 1), (key2706, 1)]

def rawRow2380 : Integer.Sparse Key := [(key2786, -2), (key2870, -2), (key2905, -2), (key2794, 1), (key2796, 1), (key2860, 1), (key2898, 1), (key2883, 1), (key2913, 1), (key2671, 2), (key2726, 2), (key2748, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2944, -1), (key2913, -1), (key2992, -1), (key2671, -1), (key2674, -1), (key2706, -1), (key2738, -1), (key2729, -1), (key2748, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2939, 1), (key2905, 1), (key2984, 1)]

def rawRow2381 : Integer.Sparse Key := [(key2786, -2), (key2905, -2), (key2870, -2), (key2796, 1), (key2794, 1), (key2898, 1), (key2860, 1), (key2913, 1), (key2883, 1), (key2671, 2), (key2748, 2), (key2726, 2), (key2654, -1), (key2640, -1), (key2944, -1), (key2794, -1), (key2992, -1), (key2913, -1), (key2674, -1), (key2671, -1), (key2738, -1), (key2706, -1), (key2748, -1), (key2729, -1), (key2649, 1), (key2632, 1), (key2939, 1), (key2786, 1), (key2984, 1), (key2905, 1)]

def rawRow2382 : Integer.Sparse Key := [(key2870, -2), (key2786, -2), (key2905, -2), (key2860, 1), (key2883, 1), (key2794, 1), (key2913, 1), (key2796, 1), (key2898, 1), (key2726, 2), (key2671, 2), (key2748, 2), (key2794, -1), (key2913, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2706, -1), (key2729, -1), (key2671, -1), (key2748, -1), (key2674, -1), (key2738, -1), (key2786, 1), (key2905, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2939, 1)]

def rawRow2383 : Integer.Sparse Key := [(key2870, -2), (key2905, -2), (key2786, -2), (key2883, 1), (key2860, 1), (key2913, 1), (key2794, 1), (key2898, 1), (key2796, 1), (key2726, 2), (key2748, 2), (key2671, 2), (key2913, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2944, -1), (key2654, -1), (key2729, -1), (key2706, -1), (key2748, -1), (key2671, -1), (key2738, -1), (key2674, -1), (key2905, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2939, 1), (key2649, 1)]

def rawRow2384 : Integer.Sparse Key := [(key2905, -2), (key2786, -2), (key2870, -2), (key2898, 1), (key2913, 1), (key2796, 1), (key2883, 1), (key2794, 1), (key2860, 1), (key2748, 2), (key2671, 2), (key2726, 2), (key2944, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2640, -1), (key2794, -1), (key2738, -1), (key2748, -1), (key2674, -1), (key2729, -1), (key2671, -1), (key2706, -1), (key2939, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2632, 1), (key2786, 1)]

def rawRow2385 : Integer.Sparse Key := [(key2905, -2), (key2870, -2), (key2786, -2), (key2913, 1), (key2898, 1), (key2883, 1), (key2796, 1), (key2860, 1), (key2794, 1), (key2748, 2), (key2726, 2), (key2671, 2), (key2992, -1), (key2944, -1), (key2913, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2748, -1), (key2738, -1), (key2729, -1), (key2674, -1), (key2706, -1), (key2671, -1), (key2984, 1), (key2939, 1), (key2905, 1), (key2649, 1), (key2786, 1), (key2632, 1)]

def rawRow2386 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2375, -2), (key2387, 6), (key2399, 2), (key2403, 2), (key2403, 2), (key2477, -2), (key2477, -2), (key2541, -2), (key2434, -6), (key2500, 2), (key2500, 2), (key2552, 2)]

def rawRow2387 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2375, -2), (key2387, 6), (key2403, 2), (key2399, 2), (key2403, 2), (key2477, -2), (key2541, -2), (key2477, -2), (key2434, -6), (key2500, 2), (key2552, 2), (key2500, 2)]

def rawRow2388 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2371, -2), (key2387, 6), (key2403, 2), (key2403, 2), (key2399, 2), (key2541, -2), (key2477, -2), (key2477, -2), (key2434, -6), (key2552, 2), (key2500, 2), (key2500, 2)]

def rawRow2389 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2387, -2), (key2375, 6), (key2465, 2), (key2469, 2), (key2477, 2), (key2403, -2), (key2469, -2), (key2536, -2), (key2500, -6), (key2434, 2), (key2500, 2), (key2552, 2)]

def rawRow2390 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2387, -2), (key2375, 6), (key2469, 2), (key2465, 2), (key2477, 2), (key2403, -2), (key2536, -2), (key2469, -2), (key2500, -6), (key2434, 2), (key2552, 2), (key2500, 2)]

def rawRow2391 : Integer.Sparse Key := [(key2371, -2), (key2387, -2), (key2375, -2), (key2375, 6), (key2465, 2), (key2477, 2), (key2469, 2), (key2469, -2), (key2403, -2), (key2536, -2), (key2500, -6), (key2500, 2), (key2434, 2), (key2552, 2)]

def rawRow2392 : Integer.Sparse Key := [(key2387, -2), (key2371, -2), (key2375, -2), (key2375, 6), (key2477, 2), (key2465, 2), (key2469, 2), (key2469, -2), (key2536, -2), (key2403, -2), (key2500, -6), (key2500, 2), (key2552, 2), (key2434, 2)]

def rawRow2393 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2371, -2), (key2375, 6), (key2469, 2), (key2477, 2), (key2465, 2), (key2536, -2), (key2403, -2), (key2469, -2), (key2500, -6), (key2552, 2), (key2434, 2), (key2500, 2)]

def rawRow2394 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2371, -2), (key2375, 6), (key2477, 2), (key2469, 2), (key2465, 2), (key2536, -2), (key2469, -2), (key2403, -2), (key2500, -6), (key2552, 2), (key2500, 2), (key2434, 2)]

def rawRow2395 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2403, -2), (key2434, 6), (key2371, 2), (key2375, 2), (key2375, 2), (key2500, -2), (key2500, -2), (key2552, -2), (key2387, -6), (key2477, 2), (key2477, 2), (key2541, 2)]

def rawRow2396 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2403, -2), (key2434, 6), (key2375, 2), (key2371, 2), (key2375, 2), (key2500, -2), (key2552, -2), (key2500, -2), (key2387, -6), (key2477, 2), (key2541, 2), (key2477, 2)]

def rawRow2397 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2399, -2), (key2434, 6), (key2375, 2), (key2375, 2), (key2371, 2), (key2552, -2), (key2500, -2), (key2500, -2), (key2387, -6), (key2541, 2), (key2477, 2), (key2477, 2)]

def rawRow2398 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2434, -2), (key2403, 6), (key2465, 2), (key2469, 2), (key2500, 2), (key2375, -2), (key2469, -2), (key2536, -2), (key2477, -6), (key2387, 2), (key2477, 2), (key2541, 2)]

def rawRow2399 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2434, -2), (key2403, 6), (key2469, 2), (key2465, 2), (key2500, 2), (key2375, -2), (key2536, -2), (key2469, -2), (key2477, -6), (key2387, 2), (key2541, 2), (key2477, 2)]

def rawRow2400 : Integer.Sparse Key := [(key2399, -2), (key2434, -2), (key2403, -2), (key2403, 6), (key2465, 2), (key2500, 2), (key2469, 2), (key2469, -2), (key2375, -2), (key2536, -2), (key2477, -6), (key2477, 2), (key2387, 2), (key2541, 2)]

def rawRow2401 : Integer.Sparse Key := [(key2434, -2), (key2399, -2), (key2403, -2), (key2403, 6), (key2500, 2), (key2465, 2), (key2469, 2), (key2469, -2), (key2536, -2), (key2375, -2), (key2477, -6), (key2477, 2), (key2541, 2), (key2387, 2)]

def rawRow2402 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2399, -2), (key2403, 6), (key2469, 2), (key2500, 2), (key2465, 2), (key2536, -2), (key2375, -2), (key2469, -2), (key2477, -6), (key2541, 2), (key2387, 2), (key2477, 2)]

def rawRow2403 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2399, -2), (key2403, 6), (key2500, 2), (key2469, 2), (key2465, 2), (key2536, -2), (key2469, -2), (key2375, -2), (key2477, -6), (key2541, 2), (key2477, 2), (key2387, 2)]

def rawRow2404 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2477, -2), (key2500, 6), (key2371, 2), (key2375, 2), (key2387, 2), (key2434, -2), (key2500, -2), (key2552, -2), (key2375, -6), (key2403, 2), (key2469, 2), (key2536, 2)]

def rawRow2405 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2477, -2), (key2500, 6), (key2375, 2), (key2371, 2), (key2387, 2), (key2434, -2), (key2552, -2), (key2500, -2), (key2375, -6), (key2403, 2), (key2536, 2), (key2469, 2)]

def rawRow2406 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2469, -2), (key2500, 6), (key2371, 2), (key2387, 2), (key2375, 2), (key2500, -2), (key2434, -2), (key2552, -2), (key2375, -6), (key2469, 2), (key2403, 2), (key2536, 2)]

def rawRow2407 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2469, -2), (key2500, 6), (key2387, 2), (key2371, 2), (key2375, 2), (key2500, -2), (key2552, -2), (key2434, -2), (key2375, -6), (key2469, 2), (key2536, 2), (key2403, 2)]

def rawRow2408 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2465, -2), (key2500, 6), (key2375, 2), (key2387, 2), (key2371, 2), (key2552, -2), (key2434, -2), (key2500, -2), (key2375, -6), (key2536, 2), (key2403, 2), (key2469, 2)]

def rawRow2409 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2465, -2), (key2500, 6), (key2387, 2), (key2375, 2), (key2371, 2), (key2552, -2), (key2500, -2), (key2434, -2), (key2375, -6), (key2536, 2), (key2469, 2), (key2403, 2)]

def rawRow2410 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2500, -2), (key2477, 6), (key2399, 2), (key2403, 2), (key2434, 2), (key2387, -2), (key2477, -2), (key2541, -2), (key2403, -6), (key2375, 2), (key2469, 2), (key2536, 2)]

def rawRow2411 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2500, -2), (key2477, 6), (key2403, 2), (key2399, 2), (key2434, 2), (key2387, -2), (key2541, -2), (key2477, -2), (key2403, -6), (key2375, 2), (key2536, 2), (key2469, 2)]

def rawRow2412 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2469, -2), (key2477, 6), (key2399, 2), (key2434, 2), (key2403, 2), (key2477, -2), (key2387, -2), (key2541, -2), (key2403, -6), (key2469, 2), (key2375, 2), (key2536, 2)]

def rawRow2413 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2469, -2), (key2477, 6), (key2434, 2), (key2399, 2), (key2403, 2), (key2477, -2), (key2541, -2), (key2387, -2), (key2403, -6), (key2469, 2), (key2536, 2), (key2375, 2)]

def rawRow2414 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2465, -2), (key2477, 6), (key2403, 2), (key2434, 2), (key2399, 2), (key2541, -2), (key2387, -2), (key2477, -2), (key2403, -6), (key2536, 2), (key2375, 2), (key2469, 2)]

def rawRow2415 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2465, -2), (key2477, 6), (key2434, 2), (key2403, 2), (key2399, 2), (key2541, -2), (key2477, -2), (key2387, -2), (key2403, -6), (key2536, 2), (key2469, 2), (key2375, 2)]

def rawRow2416 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2373, -2), (key2386, 6), (key2762, 2), (key2765, 2), (key2765, 2), (key2886, -2), (key2886, -2), (key2908, -2), (key2928, -6), (key2965, 2), (key2965, 2), (key2987, 2)]

def rawRow2417 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2373, -2), (key2386, 6), (key2765, 2), (key2762, 2), (key2765, 2), (key2886, -2), (key2908, -2), (key2886, -2), (key2928, -6), (key2965, 2), (key2987, 2), (key2965, 2)]

def rawRow2418 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2370, -2), (key2386, 6), (key2765, 2), (key2765, 2), (key2762, 2), (key2908, -2), (key2886, -2), (key2886, -2), (key2928, -6), (key2987, 2), (key2965, 2), (key2965, 2)]

def rawRow2419 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2373, 6), (key2839, 2), (key2842, 2), (key2886, 2), (key2765, -2), (key2842, -2), (key2874, -2), (key2965, -6), (key2928, 2), (key2965, 2), (key2987, 2)]

def rawRow2420 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2386, -2), (key2373, 6), (key2842, 2), (key2839, 2), (key2886, 2), (key2765, -2), (key2874, -2), (key2842, -2), (key2965, -6), (key2928, 2), (key2987, 2), (key2965, 2)]

def rawRow2421 : Integer.Sparse Key := [(key2370, -2), (key2386, -2), (key2373, -2), (key2373, 6), (key2839, 2), (key2886, 2), (key2842, 2), (key2842, -2), (key2765, -2), (key2874, -2), (key2965, -6), (key2965, 2), (key2928, 2), (key2987, 2)]

def rawRow2422 : Integer.Sparse Key := [(key2386, -2), (key2370, -2), (key2373, -2), (key2373, 6), (key2886, 2), (key2839, 2), (key2842, 2), (key2842, -2), (key2874, -2), (key2765, -2), (key2965, -6), (key2965, 2), (key2987, 2), (key2928, 2)]

def rawRow2423 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2370, -2), (key2373, 6), (key2842, 2), (key2886, 2), (key2839, 2), (key2874, -2), (key2765, -2), (key2842, -2), (key2965, -6), (key2987, 2), (key2928, 2), (key2965, 2)]

def rawRow2424 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2370, -2), (key2373, 6), (key2886, 2), (key2842, 2), (key2839, 2), (key2874, -2), (key2842, -2), (key2765, -2), (key2965, -6), (key2987, 2), (key2965, 2), (key2928, 2)]

def rawRow2425 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2401, -2), (key2433, 6), (key2583, 2), (key2586, 2), (key2586, 2), (key2965, -2), (key2965, -2), (key2987, -2), (key2597, -6), (key2886, 2), (key2886, 2), (key2908, 2)]

def rawRow2426 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2401, -2), (key2433, 6), (key2586, 2), (key2583, 2), (key2586, 2), (key2965, -2), (key2987, -2), (key2965, -2), (key2597, -6), (key2886, 2), (key2908, 2), (key2886, 2)]

def rawRow2427 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2398, -2), (key2433, 6), (key2586, 2), (key2586, 2), (key2583, 2), (key2987, -2), (key2965, -2), (key2965, -2), (key2597, -6), (key2908, 2), (key2886, 2), (key2886, 2)]

def rawRow2428 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2401, 6), (key2839, 2), (key2842, 2), (key2965, 2), (key2586, -2), (key2842, -2), (key2874, -2), (key2886, -6), (key2597, 2), (key2886, 2), (key2908, 2)]

def rawRow2429 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2433, -2), (key2401, 6), (key2842, 2), (key2839, 2), (key2965, 2), (key2586, -2), (key2874, -2), (key2842, -2), (key2886, -6), (key2597, 2), (key2908, 2), (key2886, 2)]

def rawRow2430 : Integer.Sparse Key := [(key2398, -2), (key2433, -2), (key2401, -2), (key2401, 6), (key2839, 2), (key2965, 2), (key2842, 2), (key2842, -2), (key2586, -2), (key2874, -2), (key2886, -6), (key2886, 2), (key2597, 2), (key2908, 2)]

def rawRow2431 : Integer.Sparse Key := [(key2433, -2), (key2398, -2), (key2401, -2), (key2401, 6), (key2965, 2), (key2839, 2), (key2842, 2), (key2842, -2), (key2874, -2), (key2586, -2), (key2886, -6), (key2886, 2), (key2908, 2), (key2597, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2432 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2398, -2), (key2401, 6), (key2842, 2), (key2965, 2), (key2839, 2), (key2874, -2), (key2586, -2), (key2842, -2), (key2886, -6), (key2908, 2), (key2597, 2), (key2886, 2)]

def rawRow2433 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2398, -2), (key2401, 6), (key2965, 2), (key2842, 2), (key2839, 2), (key2874, -2), (key2842, -2), (key2586, -2), (key2886, -6), (key2908, 2), (key2886, 2), (key2597, 2)]

def rawRow2434 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2370, 2), (key2373, 2), (key2386, 2), (key2928, -2), (key2965, -2), (key2987, -2), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2)]

def rawRow2435 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2476, -2), (key2499, 6), (key2373, 2), (key2370, 2), (key2386, 2), (key2928, -2), (key2987, -2), (key2965, -2), (key2586, -6), (key2765, 2), (key2874, 2), (key2842, 2)]

def rawRow2436 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2467, -2), (key2499, 6), (key2370, 2), (key2386, 2), (key2373, 2), (key2965, -2), (key2928, -2), (key2987, -2), (key2586, -6), (key2842, 2), (key2765, 2), (key2874, 2)]

def rawRow2437 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2467, -2), (key2499, 6), (key2386, 2), (key2370, 2), (key2373, 2), (key2965, -2), (key2987, -2), (key2928, -2), (key2586, -6), (key2842, 2), (key2874, 2), (key2765, 2)]

def rawRow2438 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2464, -2), (key2499, 6), (key2373, 2), (key2386, 2), (key2370, 2), (key2987, -2), (key2928, -2), (key2965, -2), (key2586, -6), (key2874, 2), (key2765, 2), (key2842, 2)]

def rawRow2439 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2464, -2), (key2499, 6), (key2386, 2), (key2373, 2), (key2370, 2), (key2987, -2), (key2965, -2), (key2928, -2), (key2586, -6), (key2874, 2), (key2842, 2), (key2765, 2)]

def rawRow2440 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2499, -2), (key2476, 6), (key2398, 2), (key2401, 2), (key2433, 2), (key2597, -2), (key2886, -2), (key2908, -2), (key2765, -6), (key2586, 2), (key2842, 2), (key2874, 2)]

def rawRow2441 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2499, -2), (key2476, 6), (key2401, 2), (key2398, 2), (key2433, 2), (key2597, -2), (key2908, -2), (key2886, -2), (key2765, -6), (key2586, 2), (key2874, 2), (key2842, 2)]

def rawRow2442 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2467, -2), (key2476, 6), (key2398, 2), (key2433, 2), (key2401, 2), (key2886, -2), (key2597, -2), (key2908, -2), (key2765, -6), (key2842, 2), (key2586, 2), (key2874, 2)]

def rawRow2443 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2433, 2), (key2398, 2), (key2401, 2), (key2886, -2), (key2908, -2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2586, 2)]

def rawRow2444 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2464, -2), (key2476, 6), (key2401, 2), (key2433, 2), (key2398, 2), (key2908, -2), (key2597, -2), (key2886, -2), (key2765, -6), (key2874, 2), (key2586, 2), (key2842, 2)]

def rawRow2445 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2464, -2), (key2476, 6), (key2433, 2), (key2401, 2), (key2398, 2), (key2908, -2), (key2886, -2), (key2597, -2), (key2765, -6), (key2874, 2), (key2842, 2), (key2586, 2)]

def rawRow2446 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2663, 2), (key2666, 2), (key2666, 2), (key2698, -1), (key2701, -1), (key2698, -1), (key2722, -1), (key2701, -1), (key2722, -1), (key2778, -1), (key2781, -1), (key2778, -1), (key2790, -1), (key2781, -1), (key2790, -1), (key2801, 1), (key2804, 1), (key2801, 1), (key2825, 1), (key2804, 1), (key2825, 1)]

def rawRow2447 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2666, 2), (key2663, 2), (key2666, 2), (key2701, -1), (key2698, -1), (key2722, -1), (key2698, -1), (key2722, -1), (key2701, -1), (key2781, -1), (key2778, -1), (key2790, -1), (key2778, -1), (key2790, -1), (key2781, -1), (key2804, 1), (key2801, 1), (key2825, 1), (key2801, 1), (key2825, 1), (key2804, 1)]

def rawRow2448 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2666, 2), (key2666, 2), (key2663, 2), (key2722, -1), (key2722, -1), (key2701, -1), (key2701, -1), (key2698, -1), (key2698, -1), (key2790, -1), (key2790, -1), (key2781, -1), (key2781, -1), (key2778, -1), (key2778, -1), (key2825, 1), (key2825, 1), (key2804, 1), (key2804, 1), (key2801, 1), (key2801, 1)]

def rawRow2449 : Integer.Sparse Key := [(key2624, -2), (key2627, -2), (key2636, -2), (key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2698, 2), (key2701, 2), (key2734, 2), (key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, -1), (key2851, -1), (key2856, -1), (key2892, -1), (key2895, -1), (key2778, 1), (key2781, 1), (key2851, 1), (key2866, 1), (key2892, 1), (key2902, 1)]

def rawRow2450 : Integer.Sparse Key := [(key2627, -2), (key2624, -2), (key2636, -2), (key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2701, 2), (key2698, 2), (key2734, 2), (key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2804, -1), (key2801, -1), (key2856, -1), (key2851, -1), (key2895, -1), (key2892, -1), (key2781, 1), (key2778, 1), (key2866, 1), (key2851, 1), (key2902, 1), (key2892, 1)]

def rawRow2451 : Integer.Sparse Key := [(key2624, -2), (key2636, -2), (key2627, -2), (key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 2), (key2734, 2), (key2701, 2), (key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2851, -1), (key2892, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2851, 1), (key2892, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2866, 1)]

def rawRow2452 : Integer.Sparse Key := [(key2636, -2), (key2624, -2), (key2627, -2), (key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 2), (key2698, 2), (key2701, 2), (key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2892, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2856, -1), (key2804, -1), (key2892, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2866, 1), (key2781, 1)]

def rawRow2453 : Integer.Sparse Key := [(key2627, -2), (key2636, -2), (key2624, -2), (key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2701, 2), (key2734, 2), (key2698, 2), (key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2856, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2801, -1), (key2851, -1), (key2866, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2778, 1), (key2851, 1)]

def rawRow2454 : Integer.Sparse Key := [(key2636, -2), (key2627, -2), (key2624, -2), (key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2734, 2), (key2701, 2), (key2698, 2), (key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2895, -1), (key2856, -1), (key2892, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 1), (key2866, 1), (key2892, 1), (key2781, 1), (key2851, 1), (key2778, 1)]

def rawRow2455 : Integer.Sparse Key := [(key2663, -2), (key2666, -2), (key2666, -2), (key2698, 1), (key2701, 1), (key2698, 1), (key2734, 1), (key2701, 1), (key2734, 1), (key2608, 2), (key2611, 2), (key2611, 2), (key2801, -1), (key2804, -1), (key2801, -1), (key2825, -1), (key2804, -1), (key2825, -1), (key2624, -1), (key2627, -1), (key2624, -1), (key2636, -1), (key2627, -1), (key2636, -1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1)]

def rawRow2456 : Integer.Sparse Key := [(key2666, -2), (key2663, -2), (key2666, -2), (key2701, 1), (key2698, 1), (key2734, 1), (key2698, 1), (key2734, 1), (key2701, 1), (key2611, 2), (key2608, 2), (key2611, 2), (key2804, -1), (key2801, -1), (key2825, -1), (key2801, -1), (key2825, -1), (key2804, -1), (key2627, -1), (key2624, -1), (key2636, -1), (key2624, -1), (key2636, -1), (key2627, -1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1)]

def rawRow2457 : Integer.Sparse Key := [(key2666, -2), (key2666, -2), (key2663, -2), (key2734, 1), (key2734, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2611, 2), (key2611, 2), (key2608, 2), (key2825, -1), (key2825, -1), (key2804, -1), (key2804, -1), (key2801, -1), (key2801, -1), (key2636, -1), (key2636, -1), (key2627, -1), (key2627, -1), (key2624, -1), (key2624, -1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1)]

def rawRow2458 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2801, 2), (key2804, 2), (key2825, 2), (key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2698, -1), (key2701, -1), (key2851, -1), (key2856, -1), (key2971, -1), (key2974, -1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1)]

def rawRow2459 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2804, 2), (key2801, 2), (key2825, 2), (key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2701, -1), (key2698, -1), (key2856, -1), (key2851, -1), (key2974, -1), (key2971, -1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1)]

def rawRow2460 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 2), (key2825, 2), (key2804, 2), (key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2851, -1), (key2971, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1)]

def rawRow2461 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 2), (key2801, 2), (key2804, 2), (key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2856, -1), (key2701, -1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1)]

def rawRow2462 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2804, 2), (key2825, 2), (key2801, 2), (key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2856, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2698, -1), (key2851, -1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1)]

def rawRow2463 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2825, 2), (key2804, 2), (key2801, 2), (key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2974, -1), (key2856, -1), (key2971, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1)]

def rawRow2464 : Integer.Sparse Key := [(key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2851, 1), (key2892, 1), (key2856, 1), (key2895, 1), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, -1), (key2701, -1), (key2851, -1), (key2971, -1), (key2856, -1), (key2974, -1), (key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1)]

def rawRow2465 : Integer.Sparse Key := [(key2781, -2), (key2778, -2), (key2790, -2), (key2804, 1), (key2801, 1), (key2892, 1), (key2851, 1), (key2895, 1), (key2856, 1), (key2627, 2), (key2624, 2), (key2636, 2), (key2701, -1), (key2698, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2856, -1), (key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1)]

def rawRow2466 : Integer.Sparse Key := [(key2778, -2), (key2790, -2), (key2781, -2), (key2851, 1), (key2856, 1), (key2801, 1), (key2895, 1), (key2804, 1), (key2892, 1), (key2624, 2), (key2636, 2), (key2627, 2), (key2851, -1), (key2856, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1)]

def rawRow2467 : Integer.Sparse Key := [(key2790, -2), (key2778, -2), (key2781, -2), (key2856, 1), (key2851, 1), (key2895, 1), (key2801, 1), (key2892, 1), (key2804, 1), (key2636, 2), (key2624, 2), (key2627, 2), (key2856, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2971, -1), (key2701, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1)]

def rawRow2468 : Integer.Sparse Key := [(key2781, -2), (key2790, -2), (key2778, -2), (key2892, 1), (key2895, 1), (key2804, 1), (key2856, 1), (key2801, 1), (key2851, 1), (key2627, 2), (key2636, 2), (key2624, 2), (key2971, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1)]

def rawRow2469 : Integer.Sparse Key := [(key2790, -2), (key2781, -2), (key2778, -2), (key2895, 1), (key2892, 1), (key2856, 1), (key2804, 1), (key2851, 1), (key2801, 1), (key2636, 2), (key2627, 2), (key2624, 2), (key2974, -1), (key2971, -1), (key2856, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1)]

def rawRow2470 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2778, 1), (key2781, 1), (key2851, 1), (key2892, 1), (key2866, 1), (key2902, 1), (key2698, 2), (key2701, 2), (key2722, 2), (key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1)]

def rawRow2471 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2781, 1), (key2778, 1), (key2892, 1), (key2851, 1), (key2902, 1), (key2866, 1), (key2701, 2), (key2698, 2), (key2722, 2), (key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1)]

def rawRow2472 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2851, 1), (key2866, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2698, 2), (key2722, 2), (key2701, 2), (key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1)]

def rawRow2473 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2866, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2892, 1), (key2781, 1), (key2722, 2), (key2698, 2), (key2701, 2), (key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1)]

def rawRow2474 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2892, 1), (key2902, 1), (key2781, 1), (key2866, 1), (key2778, 1), (key2851, 1), (key2701, 2), (key2722, 2), (key2698, 2), (key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1)]

def rawRow2475 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2902, 1), (key2892, 1), (key2866, 1), (key2781, 1), (key2851, 1), (key2778, 1), (key2722, 2), (key2701, 2), (key2698, 2), (key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1)]

def rawRow2476 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2189, -2), (key2175, 1), (key2179, 1), (key2175, 1), (key2189, 1), (key2179, 1), (key2189, 1), (key2275, 2), (key2275, 2), (key2289, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2327, -1), (key2328, -1), (key2327, -1), (key2333, -1), (key2328, -1), (key2333, -1), (key2327, 1), (key2330, 1), (key2327, 1), (key2333, 1), (key2330, 1), (key2333, 1)]

def rawRow2477 : Integer.Sparse Key := [(key2175, -2), (key2189, -2), (key2175, -2), (key2179, 1), (key2175, 1), (key2189, 1), (key2175, 1), (key2189, 1), (key2179, 1), (key2275, 2), (key2289, 2), (key2275, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2328, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2328, -1), (key2330, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2330, 1)]

def rawRow2478 : Integer.Sparse Key := [(key2189, -2), (key2175, -2), (key2175, -2), (key2189, 1), (key2189, 1), (key2179, 1), (key2179, 1), (key2175, 1), (key2175, 1), (key2289, 2), (key2275, 2), (key2275, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2333, -1), (key2333, -1), (key2328, -1), (key2328, -1), (key2327, -1), (key2327, -1), (key2333, 1), (key2333, 1), (key2330, 1), (key2330, 1), (key2327, 1), (key2327, 1)]

def rawRow2479 : Integer.Sparse Key := [(key2179, -2), (key2179, -2), (key2179, -2), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2281, 2), (key2281, 2), (key2281, 2), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1)]

def rawRow2480 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2289, -2), (key2327, 1), (key2328, 1), (key2327, 1), (key2333, 1), (key2328, 1), (key2333, 1), (key2175, 2), (key2175, 2), (key2189, 2), (key2327, -1), (key2330, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2333, -1), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2275, 1), (key2281, 1), (key2275, 1), (key2289, 1), (key2281, 1), (key2289, 1)]

def rawRow2481 : Integer.Sparse Key := [(key2275, -2), (key2289, -2), (key2275, -2), (key2328, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2328, 1), (key2175, 2), (key2189, 2), (key2175, 2), (key2330, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2281, 1), (key2275, 1), (key2289, 1), (key2275, 1), (key2289, 1), (key2281, 1)]

def rawRow2482 : Integer.Sparse Key := [(key2289, -2), (key2275, -2), (key2275, -2), (key2333, 1), (key2333, 1), (key2328, 1), (key2328, 1), (key2327, 1), (key2327, 1), (key2189, 2), (key2175, 2), (key2175, 2), (key2333, -1), (key2333, -1), (key2330, -1), (key2330, -1), (key2327, -1), (key2327, -1), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2289, 1), (key2289, 1), (key2281, 1), (key2281, 1), (key2275, 1), (key2275, 1)]

def rawRow2483 : Integer.Sparse Key := [(key2082, -2), (key2328, -2), (key2328, -2), (key2078, 1), (key2078, 1), (key2275, 1), (key2275, 1), (key2327, 1), (key2327, 1), (key2087, 2), (key2330, 2), (key2330, 2), (key2078, -1), (key2078, -1), (key2175, -1), (key2175, -1), (key2327, -1), (key2327, -1), (key2087, -1), (key2087, -1), (key2281, -1), (key2281, -1), (key2330, -1), (key2330, -1), (key2082, 1), (key2082, 1), (key2179, 1), (key2179, 1), (key2328, 1), (key2328, 1)]

def rawRow2484 : Integer.Sparse Key := [(key2328, -2), (key2082, -2), (key2328, -2), (key2275, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2275, 1), (key2330, 2), (key2087, 2), (key2330, 2), (key2175, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2281, -1), (key2330, -1), (key2087, -1), (key2330, -1), (key2087, -1), (key2281, -1), (key2179, 1), (key2328, 1), (key2082, 1), (key2328, 1), (key2082, 1), (key2179, 1)]

def rawRow2485 : Integer.Sparse Key := [(key2328, -2), (key2328, -2), (key2082, -2), (key2327, 1), (key2275, 1), (key2327, 1), (key2078, 1), (key2275, 1), (key2078, 1), (key2330, 2), (key2330, 2), (key2087, 2), (key2327, -1), (key2175, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2078, -1), (key2330, -1), (key2281, -1), (key2330, -1), (key2087, -1), (key2281, -1), (key2087, -1), (key2328, 1), (key2179, 1), (key2328, 1), (key2082, 1), (key2179, 1), (key2082, 1)]

def rawRow2486 : Integer.Sparse Key := [(key2281, -2), (key2281, -2), (key2281, -2), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2179, 2), (key2179, 2), (key2179, 2), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1)]

def rawRow2487 : Integer.Sparse Key := [(key2087, -2), (key2330, -2), (key2330, -2), (key2087, 1), (key2087, 1), (key2281, 1), (key2281, 1), (key2330, 1), (key2330, 1), (key2082, 2), (key2328, 2), (key2328, 2), (key2082, -1), (key2082, -1), (key2179, -1), (key2179, -1), (key2328, -1), (key2328, -1), (key2078, -1), (key2078, -1), (key2275, -1), (key2275, -1), (key2327, -1), (key2327, -1), (key2078, 1), (key2078, 1), (key2175, 1), (key2175, 1), (key2327, 1), (key2327, 1)]

def rawRow2488 : Integer.Sparse Key := [(key2330, -2), (key2087, -2), (key2330, -2), (key2281, 1), (key2330, 1), (key2087, 1), (key2330, 1), (key2087, 1), (key2281, 1), (key2328, 2), (key2082, 2), (key2328, 2), (key2179, -1), (key2328, -1), (key2082, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2275, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2275, -1), (key2175, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2175, 1)]

def rawRow2489 : Integer.Sparse Key := [(key2330, -2), (key2330, -2), (key2087, -2), (key2330, 1), (key2281, 1), (key2330, 1), (key2087, 1), (key2281, 1), (key2087, 1), (key2328, 2), (key2328, 2), (key2082, 2), (key2328, -1), (key2179, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2082, -1), (key2327, -1), (key2275, -1), (key2327, -1), (key2078, -1), (key2275, -1), (key2078, -1), (key2327, 1), (key2175, 1), (key2327, 1), (key2078, 1), (key2175, 1), (key2078, 1)]

def rawRow2490 : Integer.Sparse Key := [(key754, -6), (key754, 2), (key754, 2), (key755, 2), (key843, 6), (key843, -2), (key843, -2), (key844, -2), (key943, -2), (key943, -2), (key944, -2), (key943, 2), (key943, 2), (key945, 2)]

def rawRow2491 : Integer.Sparse Key := [(key754, -6), (key754, 2), (key755, 2), (key754, 2), (key843, 6), (key843, -2), (key844, -2), (key843, -2), (key943, -2), (key944, -2), (key943, -2), (key943, 2), (key945, 2), (key943, 2)]

def rawRow2492 : Integer.Sparse Key := [(key754, -6), (key755, 2), (key754, 2), (key754, 2), (key843, 6), (key844, -2), (key843, -2), (key843, -2), (key944, -2), (key943, -2), (key943, -2), (key945, 2), (key943, 2), (key943, 2)]

def rawRow2493 : Integer.Sparse Key := [(key755, -6), (key754, 2), (key754, 2), (key754, 2), (key844, 6), (key843, -2), (key843, -2), (key843, -2), (key945, -2), (key945, -2), (key945, -2), (key944, 2), (key944, 2), (key944, 2)]

def rawRow2494 : Integer.Sparse Key := [(key843, -6), (key943, 2), (key943, 2), (key944, 2), (key754, 6), (key943, -2), (key943, -2), (key945, -2), (key754, -2), (key754, -2), (key755, -2), (key843, 2), (key843, 2), (key844, 2)]

def rawRow2495 : Integer.Sparse Key := [(key843, -6), (key943, 2), (key944, 2), (key943, 2), (key754, 6), (key943, -2), (key945, -2), (key943, -2), (key754, -2), (key755, -2), (key754, -2), (key843, 2), (key844, 2), (key843, 2)]

def rawRow2496 : Integer.Sparse Key := [(key843, -6), (key944, 2), (key943, 2), (key943, 2), (key754, 6), (key945, -2), (key943, -2), (key943, -2), (key755, -2), (key754, -2), (key754, -2), (key844, 2), (key843, 2), (key843, 2)]

def rawRow2497 : Integer.Sparse Key := [(key944, -6), (key843, 2), (key943, 2), (key943, 2), (key945, 6), (key754, -2), (key943, -2), (key943, -2), (key844, -2), (key945, -2), (key945, -2), (key755, 2), (key944, 2), (key944, 2)]

def rawRow2498 : Integer.Sparse Key := [(key944, -6), (key943, 2), (key843, 2), (key943, 2), (key945, 6), (key943, -2), (key754, -2), (key943, -2), (key945, -2), (key844, -2), (key945, -2), (key944, 2), (key755, 2), (key944, 2)]

def rawRow2499 : Integer.Sparse Key := [(key944, -6), (key943, 2), (key943, 2), (key843, 2), (key945, 6), (key943, -2), (key943, -2), (key754, -2), (key945, -2), (key945, -2), (key844, -2), (key944, 2), (key944, 2), (key755, 2)]

def rawRow2500 : Integer.Sparse Key := [(key844, -6), (key945, 2), (key945, 2), (key945, 2), (key755, 6), (key944, -2), (key944, -2), (key944, -2), (key754, -2), (key754, -2), (key754, -2), (key843, 2), (key843, 2), (key843, 2)]

def rawRow2501 : Integer.Sparse Key := [(key945, -6), (key844, 2), (key945, 2), (key945, 2), (key944, 6), (key755, -2), (key944, -2), (key944, -2), (key843, -2), (key943, -2), (key943, -2), (key754, 2), (key943, 2), (key943, 2)]

def rawRow2502 : Integer.Sparse Key := [(key945, -6), (key945, 2), (key844, 2), (key945, 2), (key944, 6), (key944, -2), (key755, -2), (key944, -2), (key943, -2), (key843, -2), (key943, -2), (key943, 2), (key754, 2), (key943, 2)]

def rawRow2503 : Integer.Sparse Key := [(key945, -6), (key945, 2), (key945, 2), (key844, 2), (key944, 6), (key944, -2), (key944, -2), (key755, -2), (key943, -2), (key943, -2), (key843, -2), (key943, 2), (key943, 2), (key754, 2)]

def rawRow2504 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, -1), (key2176, -1), (key2174, -1), (key2187, -1), (key2176, -1), (key2187, -1), (key2274, -1), (key2276, -1), (key2274, -1), (key2279, -1), (key2276, -1), (key2279, -1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1)]

def rawRow2505 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 2), (key2174, 2), (key2176, 2), (key2176, -1), (key2174, -1), (key2187, -1), (key2174, -1), (key2187, -1), (key2176, -1), (key2276, -1), (key2274, -1), (key2279, -1), (key2274, -1), (key2279, -1), (key2276, -1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1)]

def rawRow2506 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, -1), (key2187, -1), (key2176, -1), (key2176, -1), (key2174, -1), (key2174, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1), (key2274, -1), (key2274, -1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1)]

def rawRow2507 : Integer.Sparse Key := [(key2085, -2), (key2085, -2), (key2085, -2), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2187, 2), (key2187, 2), (key2187, 2), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1)]

def rawRow2508 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2077, 2), (key2079, 2), (key2079, 2), (key2274, -1), (key2276, -1), (key2274, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2077, -1), (key2079, -1), (key2077, -1), (key2085, -1), (key2079, -1), (key2085, -1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1)]

def rawRow2509 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2079, 2), (key2077, 2), (key2079, 2), (key2276, -1), (key2274, -1), (key2287, -1), (key2274, -1), (key2287, -1), (key2276, -1), (key2079, -1), (key2077, -1), (key2085, -1), (key2077, -1), (key2085, -1), (key2079, -1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1)]

def rawRow2510 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2079, 2), (key2079, 2), (key2077, 2), (key2287, -1), (key2287, -1), (key2276, -1), (key2276, -1), (key2274, -1), (key2274, -1), (key2085, -1), (key2085, -1), (key2079, -1), (key2079, -1), (key2077, -1), (key2077, -1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1)]

def rawRow2511 : Integer.Sparse Key := [(key2279, -2), (key2279, -2), (key2343, -2), (key2176, 1), (key2176, 1), (key2276, 1), (key2276, 1), (key2341, 1), (key2341, 1), (key2287, 2), (key2287, 2), (key2347, 2), (key2079, -1), (key2079, -1), (key2276, -1), (key2276, -1), (key2341, -1), (key2341, -1), (key2187, -1), (key2187, -1), (key2287, -1), (key2287, -1), (key2347, -1), (key2347, -1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1)]

def rawRow2512 : Integer.Sparse Key := [(key2279, -2), (key2343, -2), (key2279, -2), (key2276, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2176, 1), (key2276, 1), (key2287, 2), (key2347, 2), (key2287, 2), (key2276, -1), (key2341, -1), (key2079, -1), (key2341, -1), (key2079, -1), (key2276, -1), (key2287, -1), (key2347, -1), (key2187, -1), (key2347, -1), (key2187, -1), (key2287, -1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1)]

def rawRow2513 : Integer.Sparse Key := [(key2343, -2), (key2279, -2), (key2279, -2), (key2341, 1), (key2276, 1), (key2341, 1), (key2176, 1), (key2276, 1), (key2176, 1), (key2347, 2), (key2287, 2), (key2287, 2), (key2341, -1), (key2276, -1), (key2341, -1), (key2079, -1), (key2276, -1), (key2079, -1), (key2347, -1), (key2287, -1), (key2347, -1), (key2187, -1), (key2287, -1), (key2187, -1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1)]

def rawRow2514 : Integer.Sparse Key := [(key2187, -2), (key2187, -2), (key2187, -2), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2085, 2), (key2085, 2), (key2085, 2), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1)]

def rawRow2515 : Integer.Sparse Key := [(key2287, -2), (key2287, -2), (key2347, -2), (key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2279, 2), (key2279, 2), (key2343, 2), (key2085, -1), (key2085, -1), (key2279, -1), (key2279, -1), (key2343, -1), (key2343, -1), (key2176, -1), (key2176, -1), (key2276, -1), (key2276, -1), (key2341, -1), (key2341, -1), (key2079, 1), (key2079, 1), (key2276, 1), (key2276, 1), (key2341, 1), (key2341, 1)]

def rawRow2516 : Integer.Sparse Key := [(key2287, -2), (key2347, -2), (key2287, -2), (key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 2), (key2343, 2), (key2279, 2), (key2279, -1), (key2343, -1), (key2085, -1), (key2343, -1), (key2085, -1), (key2279, -1), (key2276, -1), (key2341, -1), (key2176, -1), (key2341, -1), (key2176, -1), (key2276, -1), (key2276, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2276, 1)]

def rawRow2517 : Integer.Sparse Key := [(key2347, -2), (key2287, -2), (key2287, -2), (key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 2), (key2279, 2), (key2279, 2), (key2343, -1), (key2279, -1), (key2343, -1), (key2085, -1), (key2279, -1), (key2085, -1), (key2341, -1), (key2276, -1), (key2341, -1), (key2176, -1), (key2276, -1), (key2176, -1), (key2341, 1), (key2276, 1), (key2341, 1), (key2079, 1), (key2276, 1), (key2079, 1)]

def rawRow2518 : Integer.Sparse Key := [(key713, -2), (key715, -2), (key715, -2), (key715, 6), (key890, 2), (key892, 2), (key892, 2), (key892, -2), (key892, -2), (key914, -2), (key959, -6), (key959, 2), (key959, 2), (key966, 2)]

def rawRow2519 : Integer.Sparse Key := [(key715, -2), (key713, -2), (key715, -2), (key715, 6), (key892, 2), (key890, 2), (key892, 2), (key892, -2), (key914, -2), (key892, -2), (key959, -6), (key959, 2), (key966, 2), (key959, 2)]

def rawRow2520 : Integer.Sparse Key := [(key715, -2), (key715, -2), (key713, -2), (key715, 6), (key892, 2), (key892, 2), (key890, 2), (key914, -2), (key892, -2), (key892, -2), (key959, -6), (key966, 2), (key959, 2), (key959, 2)]

def rawRow2521 : Integer.Sparse Key := [(key715, -2), (key715, -2), (key715, -2), (key713, 6), (key914, 2), (key914, 2), (key914, 2), (key890, -2), (key890, -2), (key890, -2), (key966, -6), (key959, 2), (key959, 2), (key959, 2)]

def rawRow2522 : Integer.Sparse Key := [(key890, -2), (key892, -2), (key892, -2), (key959, 6), (key713, 2), (key715, 2), (key715, 2), (key959, -2), (key959, -2), (key966, -2), (key715, -6), (key892, 2), (key892, 2), (key914, 2)]

def rawRow2523 : Integer.Sparse Key := [(key892, -2), (key890, -2), (key892, -2), (key959, 6), (key715, 2), (key713, 2), (key715, 2), (key959, -2), (key966, -2), (key959, -2), (key715, -6), (key892, 2), (key914, 2), (key892, 2)]

def rawRow2524 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key890, -2), (key959, 6), (key715, 2), (key715, 2), (key713, 2), (key966, -2), (key959, -2), (key959, -2), (key715, -6), (key914, 2), (key892, 2), (key892, 2)]

def rawRow2525 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key959, -2), (key890, 6), (key914, 2), (key914, 2), (key966, 2), (key713, -2), (key890, -2), (key890, -2), (key914, -6), (key715, 2), (key892, 2), (key892, 2)]

def rawRow2526 : Integer.Sparse Key := [(key892, -2), (key959, -2), (key892, -2), (key890, 6), (key914, 2), (key966, 2), (key914, 2), (key890, -2), (key713, -2), (key890, -2), (key914, -6), (key892, 2), (key715, 2), (key892, 2)]

def rawRow2527 : Integer.Sparse Key := [(key959, -2), (key892, -2), (key892, -2), (key890, 6), (key966, 2), (key914, 2), (key914, 2), (key890, -2), (key890, -2), (key713, -2), (key914, -6), (key892, 2), (key892, 2), (key715, 2)]

def rawRow2528 : Integer.Sparse Key := [(key914, -2), (key914, -2), (key914, -2), (key966, 6), (key715, 2), (key715, 2), (key715, 2), (key959, -2), (key959, -2), (key959, -2), (key713, -6), (key890, 2), (key890, 2), (key890, 2)]

def rawRow2529 : Integer.Sparse Key := [(key914, -2), (key914, -2), (key966, -2), (key914, 6), (key892, 2), (key892, 2), (key959, 2), (key715, -2), (key892, -2), (key892, -2), (key890, -6), (key713, 2), (key890, 2), (key890, 2)]

def rawRow2530 : Integer.Sparse Key := [(key914, -2), (key966, -2), (key914, -2), (key914, 6), (key892, 2), (key959, 2), (key892, 2), (key892, -2), (key715, -2), (key892, -2), (key890, -6), (key890, 2), (key713, 2), (key890, 2)]

def rawRow2531 : Integer.Sparse Key := [(key966, -2), (key914, -2), (key914, -2), (key914, 6), (key959, 2), (key892, 2), (key892, 2), (key892, -2), (key892, -2), (key715, -2), (key890, -6), (key890, 2), (key890, 2), (key713, 2)]

def rawRow2532 : Integer.Sparse Key := [(key2098, -6), (key2098, 2), (key2098, 2), (key2099, 2), (key2203, 6), (key2203, -2), (key2203, -2), (key2206, -2), (key2317, -2), (key2317, -2), (key2318, -2), (key2317, 2), (key2317, 2), (key2321, 2)]

def rawRow2533 : Integer.Sparse Key := [(key2098, -6), (key2098, 2), (key2099, 2), (key2098, 2), (key2203, 6), (key2203, -2), (key2206, -2), (key2203, -2), (key2317, -2), (key2318, -2), (key2317, -2), (key2317, 2), (key2321, 2), (key2317, 2)]

def rawRow2534 : Integer.Sparse Key := [(key2098, -6), (key2099, 2), (key2098, 2), (key2098, 2), (key2203, 6), (key2206, -2), (key2203, -2), (key2203, -2), (key2318, -2), (key2317, -2), (key2317, -2), (key2321, 2), (key2317, 2), (key2317, 2)]

def rawRow2535 : Integer.Sparse Key := [(key2099, -6), (key2098, 2), (key2098, 2), (key2098, 2), (key2206, 6), (key2203, -2), (key2203, -2), (key2203, -2), (key2321, -2), (key2321, -2), (key2321, -2), (key2318, 2), (key2318, 2), (key2318, 2)]

def rawRow2536 : Integer.Sparse Key := [(key2203, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2098, 6), (key2317, -2), (key2317, -2), (key2321, -2), (key2098, -2), (key2098, -2), (key2099, -2), (key2203, 2), (key2203, 2), (key2206, 2)]

def rawRow2537 : Integer.Sparse Key := [(key2203, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2098, 6), (key2317, -2), (key2321, -2), (key2317, -2), (key2098, -2), (key2099, -2), (key2098, -2), (key2203, 2), (key2206, 2), (key2203, 2)]

def rawRow2538 : Integer.Sparse Key := [(key2203, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2098, 6), (key2321, -2), (key2317, -2), (key2317, -2), (key2099, -2), (key2098, -2), (key2098, -2), (key2206, 2), (key2203, 2), (key2203, 2)]

def rawRow2539 : Integer.Sparse Key := [(key2318, -6), (key2203, 2), (key2317, 2), (key2317, 2), (key2321, 6), (key2098, -2), (key2317, -2), (key2317, -2), (key2206, -2), (key2321, -2), (key2321, -2), (key2099, 2), (key2318, 2), (key2318, 2)]

def rawRow2540 : Integer.Sparse Key := [(key2318, -6), (key2317, 2), (key2203, 2), (key2317, 2), (key2321, 6), (key2317, -2), (key2098, -2), (key2317, -2), (key2321, -2), (key2206, -2), (key2321, -2), (key2318, 2), (key2099, 2), (key2318, 2)]

def rawRow2541 : Integer.Sparse Key := [(key2318, -6), (key2317, 2), (key2317, 2), (key2203, 2), (key2321, 6), (key2317, -2), (key2317, -2), (key2098, -2), (key2321, -2), (key2321, -2), (key2206, -2), (key2318, 2), (key2318, 2), (key2099, 2)]

def rawRow2542 : Integer.Sparse Key := [(key2206, -6), (key2321, 2), (key2321, 2), (key2321, 2), (key2099, 6), (key2318, -2), (key2318, -2), (key2318, -2), (key2098, -2), (key2098, -2), (key2098, -2), (key2203, 2), (key2203, 2), (key2203, 2)]

def rawRow2543 : Integer.Sparse Key := [(key2321, -6), (key2206, 2), (key2321, 2), (key2321, 2), (key2318, 6), (key2099, -2), (key2318, -2), (key2318, -2), (key2203, -2), (key2317, -2), (key2317, -2), (key2098, 2), (key2317, 2), (key2317, 2)]

def rawRow2544 : Integer.Sparse Key := [(key2321, -6), (key2321, 2), (key2206, 2), (key2321, 2), (key2318, 6), (key2318, -2), (key2099, -2), (key2318, -2), (key2317, -2), (key2203, -2), (key2317, -2), (key2317, 2), (key2098, 2), (key2317, 2)]

def rawRow2545 : Integer.Sparse Key := [(key2321, -6), (key2321, 2), (key2321, 2), (key2206, 2), (key2318, 6), (key2318, -2), (key2318, -2), (key2099, -2), (key2317, -2), (key2317, -2), (key2203, -2), (key2317, 2), (key2317, 2), (key2098, 2)]

def rawRow2546 : Integer.Sparse Key := [(key817, -1), (key818, -1), (key817, -1), (key825, -1), (key818, -1), (key825, -1), (key818, 2), (key818, 2), (key825, 2), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1), (key898, -1), (key902, -1), (key898, -1), (key908, -1), (key902, -1), (key908, -1), (key960, -2), (key960, -2), (key964, -2), (key960, 1), (key962, 1), (key960, 1), (key964, 1), (key962, 1), (key964, 1)]

def rawRow2547 : Integer.Sparse Key := [(key818, -1), (key817, -1), (key825, -1), (key817, -1), (key825, -1), (key818, -1), (key818, 2), (key825, 2), (key818, 2), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1), (key902, -1), (key898, -1), (key908, -1), (key898, -1), (key908, -1), (key902, -1), (key960, -2), (key964, -2), (key960, -2), (key962, 1), (key960, 1), (key964, 1), (key960, 1), (key964, 1), (key962, 1)]

def rawRow2548 : Integer.Sparse Key := [(key825, -1), (key825, -1), (key818, -1), (key818, -1), (key817, -1), (key817, -1), (key825, 2), (key818, 2), (key818, 2), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, -1), (key908, -1), (key902, -1), (key902, -1), (key898, -1), (key898, -1), (key964, -2), (key960, -2), (key960, -2), (key964, 1), (key964, 1), (key962, 1), (key962, 1), (key960, 1), (key960, 1)]

def rawRow2549 : Integer.Sparse Key := [(key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key817, 2), (key817, 2), (key817, 2), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key962, -2), (key962, -2), (key962, -2), (key960, 1), (key960, 1), (key960, 1), (key960, 1), (key960, 1), (key960, 1)]

def rawRow2550 : Integer.Sparse Key := [(key897, -1), (key898, -1), (key897, -1), (key908, -1), (key898, -1), (key908, -1), (key960, 2), (key960, 2), (key964, 2), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1), (key960, -1), (key962, -1), (key960, -1), (key964, -1), (key962, -1), (key964, -1), (key818, -2), (key818, -2), (key825, -2), (key898, 1), (key902, 1), (key898, 1), (key908, 1), (key902, 1), (key908, 1)]

def rawRow2551 : Integer.Sparse Key := [(key898, -1), (key897, -1), (key908, -1), (key897, -1), (key908, -1), (key898, -1), (key960, 2), (key964, 2), (key960, 2), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1), (key962, -1), (key960, -1), (key964, -1), (key960, -1), (key964, -1), (key962, -1), (key818, -2), (key825, -2), (key818, -2), (key902, 1), (key898, 1), (key908, 1), (key898, 1), (key908, 1), (key902, 1)]

def rawRow2552 : Integer.Sparse Key := [(key908, -1), (key908, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key964, 2), (key960, 2), (key960, 2), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1), (key964, -1), (key964, -1), (key962, -1), (key962, -1), (key960, -1), (key960, -1), (key825, -2), (key818, -2), (key818, -2), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1)]

def rawRow2553 : Integer.Sparse Key := [(key738, -1), (key738, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key737, 2), (key897, 2), (key897, 2), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1), (key737, -1), (key737, -1), (key817, -1), (key817, -1), (key897, -1), (key897, -1), (key743, -2), (key902, -2), (key902, -2), (key738, 1), (key738, 1), (key818, 1), (key818, 1), (key898, 1), (key898, 1)]

def rawRow2554 : Integer.Sparse Key := [(key898, -1), (key960, -1), (key738, -1), (key960, -1), (key738, -1), (key898, -1), (key897, 2), (key737, 2), (key897, 2), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1), (key817, -1), (key897, -1), (key737, -1), (key897, -1), (key737, -1), (key817, -1), (key902, -2), (key743, -2), (key902, -2), (key818, 1), (key898, 1), (key738, 1), (key898, 1), (key738, 1), (key818, 1)]

def rawRow2555 : Integer.Sparse Key := [(key960, -1), (key898, -1), (key960, -1), (key738, -1), (key898, -1), (key738, -1), (key897, 2), (key897, 2), (key737, 2), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1), (key897, -1), (key817, -1), (key897, -1), (key737, -1), (key817, -1), (key737, -1), (key902, -2), (key902, -2), (key743, -2), (key898, 1), (key818, 1), (key898, 1), (key738, 1), (key818, 1), (key738, 1)]

def rawRow2556 : Integer.Sparse Key := [(key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key962, 2), (key962, 2), (key962, 2), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key817, -2), (key817, -2), (key817, -2), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1)]

def rawRow2557 : Integer.Sparse Key := [(key743, -1), (key743, -1), (key902, -1), (key902, -1), (key962, -1), (key962, -1), (key743, 2), (key902, 2), (key902, 2), (key738, 1), (key738, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1), (key738, -1), (key738, -1), (key818, -1), (key818, -1), (key898, -1), (key898, -1), (key737, -2), (key897, -2), (key897, -2), (key737, 1), (key737, 1), (key817, 1), (key817, 1), (key897, 1), (key897, 1)]

def rawRow2558 : Integer.Sparse Key := [(key902, -1), (key962, -1), (key743, -1), (key962, -1), (key743, -1), (key902, -1), (key902, 2), (key743, 2), (key902, 2), (key898, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key898, 1), (key818, -1), (key898, -1), (key738, -1), (key898, -1), (key738, -1), (key818, -1), (key897, -2), (key737, -2), (key897, -2), (key817, 1), (key897, 1), (key737, 1), (key897, 1), (key737, 1), (key817, 1)]

def rawRow2559 : Integer.Sparse Key := [(key962, -1), (key902, -1), (key962, -1), (key743, -1), (key902, -1), (key743, -1), (key902, 2), (key902, 2), (key743, 2), (key960, 1), (key898, 1), (key960, 1), (key738, 1), (key898, 1), (key738, 1), (key898, -1), (key818, -1), (key898, -1), (key738, -1), (key818, -1), (key738, -1), (key897, -2), (key897, -2), (key737, -2), (key897, 1), (key817, 1), (key897, 1), (key737, 1), (key817, 1), (key737, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2560 : Integer.Sparse Key := [(key2182, -2), (key2185, -2), (key2185, -2), (key2183, 2), (key2185, 2), (key2185, 2), (key2284, 2), (key2285, 2), (key2285, 2), (key2285, -6), (key2345, -2), (key2346, -2), (key2346, -2), (key2346, 6)]

def rawRow2561 : Integer.Sparse Key := [(key2185, -2), (key2182, -2), (key2185, -2), (key2185, 2), (key2183, 2), (key2185, 2), (key2285, 2), (key2284, 2), (key2285, 2), (key2285, -6), (key2346, -2), (key2345, -2), (key2346, -2), (key2346, 6)]

def rawRow2562 : Integer.Sparse Key := [(key2185, -2), (key2185, -2), (key2182, -2), (key2185, 2), (key2185, 2), (key2183, 2), (key2285, 2), (key2285, 2), (key2284, 2), (key2285, -6), (key2346, -2), (key2346, -2), (key2345, -2), (key2346, 6)]

def rawRow2563 : Integer.Sparse Key := [(key2183, -2), (key2183, -2), (key2183, -2), (key2182, 2), (key2182, 2), (key2182, 2), (key2285, 2), (key2285, 2), (key2285, 2), (key2284, -6), (key2346, -2), (key2346, -2), (key2346, -2), (key2345, 6)]

def rawRow2564 : Integer.Sparse Key := [(key2284, -2), (key2285, -2), (key2285, -2), (key2345, 2), (key2346, 2), (key2346, 2), (key2182, 2), (key2185, 2), (key2185, 2), (key2346, -6), (key2183, -2), (key2185, -2), (key2185, -2), (key2285, 6)]

def rawRow2565 : Integer.Sparse Key := [(key2285, -2), (key2284, -2), (key2285, -2), (key2346, 2), (key2345, 2), (key2346, 2), (key2185, 2), (key2182, 2), (key2185, 2), (key2346, -6), (key2185, -2), (key2183, -2), (key2185, -2), (key2285, 6)]

def rawRow2566 : Integer.Sparse Key := [(key2285, -2), (key2285, -2), (key2284, -2), (key2346, 2), (key2346, 2), (key2345, 2), (key2185, 2), (key2185, 2), (key2182, 2), (key2346, -6), (key2185, -2), (key2185, -2), (key2183, -2), (key2285, 6)]

def rawRow2567 : Integer.Sparse Key := [(key2183, -2), (key2183, -2), (key2345, -2), (key2182, 2), (key2182, 2), (key2284, 2), (key2185, 2), (key2185, 2), (key2346, 2), (key2182, -6), (key2185, -2), (key2185, -2), (key2285, -2), (key2183, 6)]

def rawRow2568 : Integer.Sparse Key := [(key2183, -2), (key2345, -2), (key2183, -2), (key2182, 2), (key2284, 2), (key2182, 2), (key2185, 2), (key2346, 2), (key2185, 2), (key2182, -6), (key2185, -2), (key2285, -2), (key2185, -2), (key2183, 6)]

def rawRow2569 : Integer.Sparse Key := [(key2345, -2), (key2183, -2), (key2183, -2), (key2284, 2), (key2182, 2), (key2182, 2), (key2346, 2), (key2185, 2), (key2185, 2), (key2182, -6), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, 6)]

def rawRow2570 : Integer.Sparse Key := [(key2285, -2), (key2285, -2), (key2285, -2), (key2346, 2), (key2346, 2), (key2346, 2), (key2183, 2), (key2183, 2), (key2183, 2), (key2345, -6), (key2182, -2), (key2182, -2), (key2182, -2), (key2284, 6)]

def rawRow2571 : Integer.Sparse Key := [(key2185, -2), (key2185, -2), (key2346, -2), (key2185, 2), (key2185, 2), (key2285, 2), (key2183, 2), (key2183, 2), (key2345, 2), (key2183, -6), (key2182, -2), (key2182, -2), (key2284, -2), (key2182, 6)]

def rawRow2572 : Integer.Sparse Key := [(key2185, -2), (key2346, -2), (key2185, -2), (key2185, 2), (key2285, 2), (key2185, 2), (key2183, 2), (key2345, 2), (key2183, 2), (key2183, -6), (key2182, -2), (key2284, -2), (key2182, -2), (key2182, 6)]

def rawRow2573 : Integer.Sparse Key := [(key2346, -2), (key2185, -2), (key2185, -2), (key2285, 2), (key2185, 2), (key2185, 2), (key2345, 2), (key2183, 2), (key2183, 2), (key2183, -6), (key2284, -2), (key2182, -2), (key2182, -2), (key2182, 6)]

def rawRow2574 : Integer.Sparse Key := [(key737, -2), (key738, -2), (key738, -2), (key737, 1), (key738, 1), (key737, 1), (key743, 1), (key738, 1), (key743, 1), (key817, 2), (key818, 2), (key818, 2), (key817, -1), (key818, -1), (key817, -1), (key825, -1), (key818, -1), (key825, -1), (key897, -1), (key898, -1), (key897, -1), (key902, -1), (key898, -1), (key902, -1), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1)]

def rawRow2575 : Integer.Sparse Key := [(key738, -2), (key737, -2), (key738, -2), (key738, 1), (key737, 1), (key743, 1), (key737, 1), (key743, 1), (key738, 1), (key818, 2), (key817, 2), (key818, 2), (key818, -1), (key817, -1), (key825, -1), (key817, -1), (key825, -1), (key818, -1), (key898, -1), (key897, -1), (key902, -1), (key897, -1), (key902, -1), (key898, -1), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1)]

def rawRow2576 : Integer.Sparse Key := [(key738, -2), (key738, -2), (key737, -2), (key743, 1), (key743, 1), (key738, 1), (key738, 1), (key737, 1), (key737, 1), (key818, 2), (key818, 2), (key817, 2), (key825, -1), (key825, -1), (key818, -1), (key818, -1), (key817, -1), (key817, -1), (key902, -1), (key902, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1)]

def rawRow2577 : Integer.Sparse Key := [(key743, -2), (key743, -2), (key743, -2), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key825, 2), (key825, 2), (key825, 2), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1)]

def rawRow2578 : Integer.Sparse Key := [(key817, -2), (key818, -2), (key818, -2), (key897, 1), (key898, 1), (key897, 1), (key902, 1), (key898, 1), (key902, 1), (key737, 2), (key738, 2), (key738, 2), (key897, -1), (key898, -1), (key897, -1), (key908, -1), (key898, -1), (key908, -1), (key737, -1), (key738, -1), (key737, -1), (key743, -1), (key738, -1), (key743, -1), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1)]

def rawRow2579 : Integer.Sparse Key := [(key818, -2), (key817, -2), (key818, -2), (key898, 1), (key897, 1), (key902, 1), (key897, 1), (key902, 1), (key898, 1), (key738, 2), (key737, 2), (key738, 2), (key898, -1), (key897, -1), (key908, -1), (key897, -1), (key908, -1), (key898, -1), (key738, -1), (key737, -1), (key743, -1), (key737, -1), (key743, -1), (key738, -1), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1)]

def rawRow2580 : Integer.Sparse Key := [(key818, -2), (key818, -2), (key817, -2), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key738, 2), (key738, 2), (key737, 2), (key908, -1), (key908, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key743, -1), (key743, -1), (key738, -1), (key738, -1), (key737, -1), (key737, -1), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1)]

def rawRow2581 : Integer.Sparse Key := [(key902, -2), (key902, -2), (key962, -2), (key818, 1), (key818, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1), (key908, 2), (key908, 2), (key964, 2), (key738, -1), (key738, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key825, -1), (key825, -1), (key908, -1), (key908, -1), (key964, -1), (key964, -1), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1)]

def rawRow2582 : Integer.Sparse Key := [(key902, -2), (key962, -2), (key902, -2), (key898, 1), (key960, 1), (key818, 1), (key960, 1), (key818, 1), (key898, 1), (key908, 2), (key964, 2), (key908, 2), (key898, -1), (key960, -1), (key738, -1), (key960, -1), (key738, -1), (key898, -1), (key908, -1), (key964, -1), (key825, -1), (key964, -1), (key825, -1), (key908, -1), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1)]

def rawRow2583 : Integer.Sparse Key := [(key962, -2), (key902, -2), (key902, -2), (key960, 1), (key898, 1), (key960, 1), (key818, 1), (key898, 1), (key818, 1), (key964, 2), (key908, 2), (key908, 2), (key960, -1), (key898, -1), (key960, -1), (key738, -1), (key898, -1), (key738, -1), (key964, -1), (key908, -1), (key964, -1), (key825, -1), (key908, -1), (key825, -1), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1)]

def rawRow2584 : Integer.Sparse Key := [(key825, -2), (key825, -2), (key825, -2), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key743, 2), (key743, 2), (key743, 2), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1)]

def rawRow2585 : Integer.Sparse Key := [(key908, -2), (key908, -2), (key964, -2), (key825, 1), (key825, 1), (key908, 1), (key908, 1), (key964, 1), (key964, 1), (key902, 2), (key902, 2), (key962, 2), (key743, -1), (key743, -1), (key902, -1), (key902, -1), (key962, -1), (key962, -1), (key818, -1), (key818, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key738, 1), (key738, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1)]

def rawRow2586 : Integer.Sparse Key := [(key908, -2), (key964, -2), (key908, -2), (key908, 1), (key964, 1), (key825, 1), (key964, 1), (key825, 1), (key908, 1), (key902, 2), (key962, 2), (key902, 2), (key902, -1), (key962, -1), (key743, -1), (key962, -1), (key743, -1), (key902, -1), (key898, -1), (key960, -1), (key818, -1), (key960, -1), (key818, -1), (key898, -1), (key898, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key898, 1)]

def rawRow2587 : Integer.Sparse Key := [(key964, -2), (key908, -2), (key908, -2), (key964, 1), (key908, 1), (key964, 1), (key825, 1), (key908, 1), (key825, 1), (key962, 2), (key902, 2), (key902, 2), (key962, -1), (key902, -1), (key962, -1), (key743, -1), (key902, -1), (key743, -1), (key960, -1), (key898, -1), (key960, -1), (key818, -1), (key898, -1), (key818, -1), (key960, 1), (key898, 1), (key960, 1), (key738, 1), (key898, 1), (key738, 1)]

def rawRow2588 : Integer.Sparse Key := [(key721, -2), (key722, -2), (key722, -2), (key722, 6), (key921, 2), (key922, 2), (key922, 2), (key922, -2), (key922, -2), (key939, -2), (key959, -6), (key959, 2), (key959, 2), (key966, 2)]

def rawRow2589 : Integer.Sparse Key := [(key722, -2), (key721, -2), (key722, -2), (key722, 6), (key922, 2), (key921, 2), (key922, 2), (key922, -2), (key939, -2), (key922, -2), (key959, -6), (key959, 2), (key966, 2), (key959, 2)]

def rawRow2590 : Integer.Sparse Key := [(key722, -2), (key722, -2), (key721, -2), (key722, 6), (key922, 2), (key922, 2), (key921, 2), (key939, -2), (key922, -2), (key922, -2), (key959, -6), (key966, 2), (key959, 2), (key959, 2)]

def rawRow2591 : Integer.Sparse Key := [(key722, -2), (key722, -2), (key722, -2), (key721, 6), (key939, 2), (key939, 2), (key939, 2), (key921, -2), (key921, -2), (key921, -2), (key966, -6), (key959, 2), (key959, 2), (key959, 2)]

def rawRow2592 : Integer.Sparse Key := [(key921, -2), (key922, -2), (key922, -2), (key959, 6), (key721, 2), (key722, 2), (key722, 2), (key959, -2), (key959, -2), (key966, -2), (key722, -6), (key922, 2), (key922, 2), (key939, 2)]

def rawRow2593 : Integer.Sparse Key := [(key922, -2), (key921, -2), (key922, -2), (key959, 6), (key722, 2), (key721, 2), (key722, 2), (key959, -2), (key966, -2), (key959, -2), (key722, -6), (key922, 2), (key939, 2), (key922, 2)]

def rawRow2594 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key921, -2), (key959, 6), (key722, 2), (key722, 2), (key721, 2), (key966, -2), (key959, -2), (key959, -2), (key722, -6), (key939, 2), (key922, 2), (key922, 2)]

def rawRow2595 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key959, -2), (key921, 6), (key939, 2), (key939, 2), (key966, 2), (key721, -2), (key921, -2), (key921, -2), (key939, -6), (key722, 2), (key922, 2), (key922, 2)]

def rawRow2596 : Integer.Sparse Key := [(key922, -2), (key959, -2), (key922, -2), (key921, 6), (key939, 2), (key966, 2), (key939, 2), (key921, -2), (key721, -2), (key921, -2), (key939, -6), (key922, 2), (key722, 2), (key922, 2)]

def rawRow2597 : Integer.Sparse Key := [(key959, -2), (key922, -2), (key922, -2), (key921, 6), (key966, 2), (key939, 2), (key939, 2), (key921, -2), (key921, -2), (key721, -2), (key939, -6), (key922, 2), (key922, 2), (key722, 2)]

def rawRow2598 : Integer.Sparse Key := [(key939, -2), (key939, -2), (key939, -2), (key966, 6), (key722, 2), (key722, 2), (key722, 2), (key959, -2), (key959, -2), (key959, -2), (key721, -6), (key921, 2), (key921, 2), (key921, 2)]

def rawRow2599 : Integer.Sparse Key := [(key939, -2), (key939, -2), (key966, -2), (key939, 6), (key922, 2), (key922, 2), (key959, 2), (key722, -2), (key922, -2), (key922, -2), (key921, -6), (key721, 2), (key921, 2), (key921, 2)]

def rawRow2600 : Integer.Sparse Key := [(key939, -2), (key966, -2), (key939, -2), (key939, 6), (key922, 2), (key959, 2), (key922, 2), (key922, -2), (key722, -2), (key922, -2), (key921, -6), (key921, 2), (key721, 2), (key921, 2)]

def rawRow2601 : Integer.Sparse Key := [(key966, -2), (key939, -2), (key939, -2), (key939, 6), (key959, 2), (key922, 2), (key922, 2), (key922, -2), (key922, -2), (key722, -2), (key921, -6), (key921, 2), (key921, 2), (key721, 2)]

def rawRow2602 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2087, -2), (key2078, 1), (key2082, 1), (key2078, 1), (key2087, 1), (key2082, 1), (key2087, 1), (key2275, 2), (key2275, 2), (key2281, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2327, -1), (key2328, -1), (key2327, -1), (key2330, -1), (key2328, -1), (key2330, -1), (key2327, 1), (key2330, 1), (key2327, 1), (key2333, 1), (key2330, 1), (key2333, 1)]

def rawRow2603 : Integer.Sparse Key := [(key2078, -2), (key2087, -2), (key2078, -2), (key2082, 1), (key2078, 1), (key2087, 1), (key2078, 1), (key2087, 1), (key2082, 1), (key2275, 2), (key2281, 2), (key2275, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2328, -1), (key2327, -1), (key2330, -1), (key2327, -1), (key2330, -1), (key2328, -1), (key2330, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2330, 1)]

def rawRow2604 : Integer.Sparse Key := [(key2087, -2), (key2078, -2), (key2078, -2), (key2087, 1), (key2087, 1), (key2082, 1), (key2082, 1), (key2078, 1), (key2078, 1), (key2281, 2), (key2275, 2), (key2275, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2330, -1), (key2330, -1), (key2328, -1), (key2328, -1), (key2327, -1), (key2327, -1), (key2333, 1), (key2333, 1), (key2330, 1), (key2330, 1), (key2327, 1), (key2327, 1)]

def rawRow2605 : Integer.Sparse Key := [(key2082, -2), (key2082, -2), (key2082, -2), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2289, 2), (key2289, 2), (key2289, 2), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1)]

def rawRow2606 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2281, -2), (key2327, 1), (key2328, 1), (key2327, 1), (key2330, 1), (key2328, 1), (key2330, 1), (key2078, 2), (key2078, 2), (key2087, 2), (key2327, -1), (key2330, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2333, -1), (key2078, -1), (key2082, -1), (key2078, -1), (key2087, -1), (key2082, -1), (key2087, -1), (key2275, 1), (key2281, 1), (key2275, 1), (key2289, 1), (key2281, 1), (key2289, 1)]

def rawRow2607 : Integer.Sparse Key := [(key2275, -2), (key2281, -2), (key2275, -2), (key2328, 1), (key2327, 1), (key2330, 1), (key2327, 1), (key2330, 1), (key2328, 1), (key2078, 2), (key2087, 2), (key2078, 2), (key2330, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2082, -1), (key2078, -1), (key2087, -1), (key2078, -1), (key2087, -1), (key2082, -1), (key2281, 1), (key2275, 1), (key2289, 1), (key2275, 1), (key2289, 1), (key2281, 1)]

def rawRow2608 : Integer.Sparse Key := [(key2281, -2), (key2275, -2), (key2275, -2), (key2330, 1), (key2330, 1), (key2328, 1), (key2328, 1), (key2327, 1), (key2327, 1), (key2087, 2), (key2078, 2), (key2078, 2), (key2333, -1), (key2333, -1), (key2330, -1), (key2330, -1), (key2327, -1), (key2327, -1), (key2087, -1), (key2087, -1), (key2082, -1), (key2082, -1), (key2078, -1), (key2078, -1), (key2289, 1), (key2289, 1), (key2281, 1), (key2281, 1), (key2275, 1), (key2275, 1)]

def rawRow2609 : Integer.Sparse Key := [(key2179, -2), (key2328, -2), (key2328, -2), (key2175, 1), (key2175, 1), (key2275, 1), (key2275, 1), (key2327, 1), (key2327, 1), (key2189, 2), (key2333, 2), (key2333, 2), (key2078, -1), (key2078, -1), (key2175, -1), (key2175, -1), (key2327, -1), (key2327, -1), (key2189, -1), (key2189, -1), (key2289, -1), (key2289, -1), (key2333, -1), (key2333, -1), (key2082, 1), (key2082, 1), (key2179, 1), (key2179, 1), (key2328, 1), (key2328, 1)]

def rawRow2610 : Integer.Sparse Key := [(key2328, -2), (key2179, -2), (key2328, -2), (key2275, 1), (key2327, 1), (key2175, 1), (key2327, 1), (key2175, 1), (key2275, 1), (key2333, 2), (key2189, 2), (key2333, 2), (key2175, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2289, -1), (key2333, -1), (key2189, -1), (key2333, -1), (key2189, -1), (key2289, -1), (key2179, 1), (key2328, 1), (key2082, 1), (key2328, 1), (key2082, 1), (key2179, 1)]

def rawRow2611 : Integer.Sparse Key := [(key2328, -2), (key2328, -2), (key2179, -2), (key2327, 1), (key2275, 1), (key2327, 1), (key2175, 1), (key2275, 1), (key2175, 1), (key2333, 2), (key2333, 2), (key2189, 2), (key2327, -1), (key2175, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2078, -1), (key2333, -1), (key2289, -1), (key2333, -1), (key2189, -1), (key2289, -1), (key2189, -1), (key2328, 1), (key2179, 1), (key2328, 1), (key2082, 1), (key2179, 1), (key2082, 1)]

def rawRow2612 : Integer.Sparse Key := [(key2289, -2), (key2289, -2), (key2289, -2), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2082, 2), (key2082, 2), (key2082, 2), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1)]

def rawRow2613 : Integer.Sparse Key := [(key2189, -2), (key2333, -2), (key2333, -2), (key2189, 1), (key2189, 1), (key2289, 1), (key2289, 1), (key2333, 1), (key2333, 1), (key2179, 2), (key2328, 2), (key2328, 2), (key2082, -1), (key2082, -1), (key2179, -1), (key2179, -1), (key2328, -1), (key2328, -1), (key2175, -1), (key2175, -1), (key2275, -1), (key2275, -1), (key2327, -1), (key2327, -1), (key2078, 1), (key2078, 1), (key2175, 1), (key2175, 1), (key2327, 1), (key2327, 1)]

def rawRow2614 : Integer.Sparse Key := [(key2333, -2), (key2189, -2), (key2333, -2), (key2289, 1), (key2333, 1), (key2189, 1), (key2333, 1), (key2189, 1), (key2289, 1), (key2328, 2), (key2179, 2), (key2328, 2), (key2179, -1), (key2328, -1), (key2082, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2275, -1), (key2327, -1), (key2175, -1), (key2327, -1), (key2175, -1), (key2275, -1), (key2175, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2175, 1)]

def rawRow2615 : Integer.Sparse Key := [(key2333, -2), (key2333, -2), (key2189, -2), (key2333, 1), (key2289, 1), (key2333, 1), (key2189, 1), (key2289, 1), (key2189, 1), (key2328, 2), (key2328, 2), (key2179, 2), (key2328, -1), (key2179, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2082, -1), (key2327, -1), (key2275, -1), (key2327, -1), (key2175, -1), (key2275, -1), (key2175, -1), (key2327, 1), (key2175, 1), (key2327, 1), (key2078, 1), (key2175, 1), (key2078, 1)]

def rawRow2616 : Integer.Sparse Key := [(key1998, -2), (key2000, -2), (key2000, -2), (key2000, 6), (key2267, 2), (key2269, 2), (key2269, 2), (key2269, -2), (key2269, -2), (key2292, -2), (key2340, -6), (key2340, 2), (key2340, 2), (key2349, 2)]

def rawRow2617 : Integer.Sparse Key := [(key2000, -2), (key1998, -2), (key2000, -2), (key2000, 6), (key2269, 2), (key2267, 2), (key2269, 2), (key2269, -2), (key2292, -2), (key2269, -2), (key2340, -6), (key2340, 2), (key2349, 2), (key2340, 2)]

def rawRow2618 : Integer.Sparse Key := [(key2000, -2), (key2000, -2), (key1998, -2), (key2000, 6), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, -2), (key2269, -2), (key2269, -2), (key2340, -6), (key2349, 2), (key2340, 2), (key2340, 2)]

def rawRow2619 : Integer.Sparse Key := [(key2000, -2), (key2000, -2), (key2000, -2), (key1998, 6), (key2292, 2), (key2292, 2), (key2292, 2), (key2267, -2), (key2267, -2), (key2267, -2), (key2349, -6), (key2340, 2), (key2340, 2), (key2340, 2)]

def rawRow2620 : Integer.Sparse Key := [(key2267, -2), (key2269, -2), (key2269, -2), (key2340, 6), (key1998, 2), (key2000, 2), (key2000, 2), (key2340, -2), (key2340, -2), (key2349, -2), (key2000, -6), (key2269, 2), (key2269, 2), (key2292, 2)]

def rawRow2621 : Integer.Sparse Key := [(key2269, -2), (key2267, -2), (key2269, -2), (key2340, 6), (key2000, 2), (key1998, 2), (key2000, 2), (key2340, -2), (key2349, -2), (key2340, -2), (key2000, -6), (key2269, 2), (key2292, 2), (key2269, 2)]

def rawRow2622 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2267, -2), (key2340, 6), (key2000, 2), (key2000, 2), (key1998, 2), (key2349, -2), (key2340, -2), (key2340, -2), (key2000, -6), (key2292, 2), (key2269, 2), (key2269, 2)]

def rawRow2623 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2340, -2), (key2267, 6), (key2292, 2), (key2292, 2), (key2349, 2), (key1998, -2), (key2267, -2), (key2267, -2), (key2292, -6), (key2000, 2), (key2269, 2), (key2269, 2)]

def rawRow2624 : Integer.Sparse Key := [(key2269, -2), (key2340, -2), (key2269, -2), (key2267, 6), (key2292, 2), (key2349, 2), (key2292, 2), (key2267, -2), (key1998, -2), (key2267, -2), (key2292, -6), (key2269, 2), (key2000, 2), (key2269, 2)]

def rawRow2625 : Integer.Sparse Key := [(key2340, -2), (key2269, -2), (key2269, -2), (key2267, 6), (key2349, 2), (key2292, 2), (key2292, 2), (key2267, -2), (key2267, -2), (key1998, -2), (key2292, -6), (key2269, 2), (key2269, 2), (key2000, 2)]

def rawRow2626 : Integer.Sparse Key := [(key2292, -2), (key2292, -2), (key2292, -2), (key2349, 6), (key2000, 2), (key2000, 2), (key2000, 2), (key2340, -2), (key2340, -2), (key2340, -2), (key1998, -6), (key2267, 2), (key2267, 2), (key2267, 2)]

def rawRow2627 : Integer.Sparse Key := [(key2292, -2), (key2292, -2), (key2349, -2), (key2292, 6), (key2269, 2), (key2269, 2), (key2340, 2), (key2000, -2), (key2269, -2), (key2269, -2), (key2267, -6), (key1998, 2), (key2267, 2), (key2267, 2)]

def rawRow2628 : Integer.Sparse Key := [(key2292, -2), (key2349, -2), (key2292, -2), (key2292, 6), (key2269, 2), (key2340, 2), (key2269, 2), (key2269, -2), (key2000, -2), (key2269, -2), (key2267, -6), (key2267, 2), (key1998, 2), (key2267, 2)]

def rawRow2629 : Integer.Sparse Key := [(key2349, -2), (key2292, -2), (key2292, -2), (key2292, 6), (key2340, 2), (key2269, 2), (key2269, 2), (key2269, -2), (key2269, -2), (key2000, -2), (key2267, -6), (key2267, 2), (key2267, 2), (key1998, 2)]

def rawRow2630 : Integer.Sparse Key := [(key2006, -2), (key2007, -2), (key2007, -2), (key2007, 6), (key2299, 2), (key2300, 2), (key2300, 2), (key2300, -2), (key2300, -2), (key2313, -2), (key2340, -6), (key2340, 2), (key2340, 2), (key2349, 2)]

def rawRow2631 : Integer.Sparse Key := [(key2007, -2), (key2006, -2), (key2007, -2), (key2007, 6), (key2300, 2), (key2299, 2), (key2300, 2), (key2300, -2), (key2313, -2), (key2300, -2), (key2340, -6), (key2340, 2), (key2349, 2), (key2340, 2)]

def rawRow2632 : Integer.Sparse Key := [(key2007, -2), (key2007, -2), (key2006, -2), (key2007, 6), (key2300, 2), (key2300, 2), (key2299, 2), (key2313, -2), (key2300, -2), (key2300, -2), (key2340, -6), (key2349, 2), (key2340, 2), (key2340, 2)]

def rawRow2633 : Integer.Sparse Key := [(key2007, -2), (key2007, -2), (key2007, -2), (key2006, 6), (key2313, 2), (key2313, 2), (key2313, 2), (key2299, -2), (key2299, -2), (key2299, -2), (key2349, -6), (key2340, 2), (key2340, 2), (key2340, 2)]

def rawRow2634 : Integer.Sparse Key := [(key2299, -2), (key2300, -2), (key2300, -2), (key2340, 6), (key2006, 2), (key2007, 2), (key2007, 2), (key2340, -2), (key2340, -2), (key2349, -2), (key2007, -6), (key2300, 2), (key2300, 2), (key2313, 2)]

def rawRow2635 : Integer.Sparse Key := [(key2300, -2), (key2299, -2), (key2300, -2), (key2340, 6), (key2007, 2), (key2006, 2), (key2007, 2), (key2340, -2), (key2349, -2), (key2340, -2), (key2007, -6), (key2300, 2), (key2313, 2), (key2300, 2)]

def rawRow2636 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2299, -2), (key2340, 6), (key2007, 2), (key2007, 2), (key2006, 2), (key2349, -2), (key2340, -2), (key2340, -2), (key2007, -6), (key2313, 2), (key2300, 2), (key2300, 2)]

def rawRow2637 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2340, -2), (key2299, 6), (key2313, 2), (key2313, 2), (key2349, 2), (key2006, -2), (key2299, -2), (key2299, -2), (key2313, -6), (key2007, 2), (key2300, 2), (key2300, 2)]

def rawRow2638 : Integer.Sparse Key := [(key2300, -2), (key2340, -2), (key2300, -2), (key2299, 6), (key2313, 2), (key2349, 2), (key2313, 2), (key2299, -2), (key2006, -2), (key2299, -2), (key2313, -6), (key2300, 2), (key2007, 2), (key2300, 2)]

def rawRow2639 : Integer.Sparse Key := [(key2340, -2), (key2300, -2), (key2300, -2), (key2299, 6), (key2349, 2), (key2313, 2), (key2313, 2), (key2299, -2), (key2299, -2), (key2006, -2), (key2313, -6), (key2300, 2), (key2300, 2), (key2007, 2)]

def rawRow2640 : Integer.Sparse Key := [(key2313, -2), (key2313, -2), (key2313, -2), (key2349, 6), (key2007, 2), (key2007, 2), (key2007, 2), (key2340, -2), (key2340, -2), (key2340, -2), (key2006, -6), (key2299, 2), (key2299, 2), (key2299, 2)]

def rawRow2641 : Integer.Sparse Key := [(key2313, -2), (key2313, -2), (key2349, -2), (key2313, 6), (key2300, 2), (key2300, 2), (key2340, 2), (key2007, -2), (key2300, -2), (key2300, -2), (key2299, -6), (key2006, 2), (key2299, 2), (key2299, 2)]

def rawRow2642 : Integer.Sparse Key := [(key2313, -2), (key2349, -2), (key2313, -2), (key2313, 6), (key2300, 2), (key2340, 2), (key2300, 2), (key2300, -2), (key2007, -2), (key2300, -2), (key2299, -6), (key2299, 2), (key2006, 2), (key2299, 2)]

def rawRow2643 : Integer.Sparse Key := [(key2349, -2), (key2313, -2), (key2313, -2), (key2313, 6), (key2340, 2), (key2300, 2), (key2300, 2), (key2300, -2), (key2300, -2), (key2007, -2), (key2299, -6), (key2299, 2), (key2299, 2), (key2006, 2)]

def rawRow2644 : Integer.Sparse Key := [(key2091, -2), (key2092, -2), (key2092, -2), (key2091, 1), (key2092, 1), (key2091, 1), (key2095, 1), (key2092, 1), (key2095, 1), (key2193, 2), (key2194, 2), (key2194, 2), (key2193, -1), (key2194, -1), (key2193, -1), (key2200, -1), (key2194, -1), (key2200, -1), (key2302, -1), (key2303, -1), (key2302, -1), (key2305, -1), (key2303, -1), (key2305, -1), (key2302, 1), (key2303, 1), (key2302, 1), (key2310, 1), (key2303, 1), (key2310, 1)]

def rawRow2645 : Integer.Sparse Key := [(key2092, -2), (key2091, -2), (key2092, -2), (key2092, 1), (key2091, 1), (key2095, 1), (key2091, 1), (key2095, 1), (key2092, 1), (key2194, 2), (key2193, 2), (key2194, 2), (key2194, -1), (key2193, -1), (key2200, -1), (key2193, -1), (key2200, -1), (key2194, -1), (key2303, -1), (key2302, -1), (key2305, -1), (key2302, -1), (key2305, -1), (key2303, -1), (key2303, 1), (key2302, 1), (key2310, 1), (key2302, 1), (key2310, 1), (key2303, 1)]

def rawRow2646 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2091, -2), (key2095, 1), (key2095, 1), (key2092, 1), (key2092, 1), (key2091, 1), (key2091, 1), (key2194, 2), (key2194, 2), (key2193, 2), (key2200, -1), (key2200, -1), (key2194, -1), (key2194, -1), (key2193, -1), (key2193, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1), (key2302, -1), (key2302, -1), (key2310, 1), (key2310, 1), (key2303, 1), (key2303, 1), (key2302, 1), (key2302, 1)]

def rawRow2647 : Integer.Sparse Key := [(key2095, -2), (key2095, -2), (key2095, -2), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2200, 2), (key2200, 2), (key2200, 2), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1)]

def rawRow2648 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2194, -2), (key2302, 1), (key2303, 1), (key2302, 1), (key2305, 1), (key2303, 1), (key2305, 1), (key2091, 2), (key2092, 2), (key2092, 2), (key2302, -1), (key2303, -1), (key2302, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2091, -1), (key2092, -1), (key2091, -1), (key2095, -1), (key2092, -1), (key2095, -1), (key2193, 1), (key2194, 1), (key2193, 1), (key2200, 1), (key2194, 1), (key2200, 1)]

def rawRow2649 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2194, -2), (key2303, 1), (key2302, 1), (key2305, 1), (key2302, 1), (key2305, 1), (key2303, 1), (key2092, 2), (key2091, 2), (key2092, 2), (key2303, -1), (key2302, -1), (key2310, -1), (key2302, -1), (key2310, -1), (key2303, -1), (key2092, -1), (key2091, -1), (key2095, -1), (key2091, -1), (key2095, -1), (key2092, -1), (key2194, 1), (key2193, 1), (key2200, 1), (key2193, 1), (key2200, 1), (key2194, 1)]

def rawRow2650 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2193, -2), (key2305, 1), (key2305, 1), (key2303, 1), (key2303, 1), (key2302, 1), (key2302, 1), (key2092, 2), (key2092, 2), (key2091, 2), (key2310, -1), (key2310, -1), (key2303, -1), (key2303, -1), (key2302, -1), (key2302, -1), (key2095, -1), (key2095, -1), (key2092, -1), (key2092, -1), (key2091, -1), (key2091, -1), (key2200, 1), (key2200, 1), (key2194, 1), (key2194, 1), (key2193, 1), (key2193, 1)]

def rawRow2651 : Integer.Sparse Key := [(key2305, -2), (key2305, -2), (key2343, -2), (key2194, 1), (key2194, 1), (key2303, 1), (key2303, 1), (key2341, 1), (key2341, 1), (key2310, 2), (key2310, 2), (key2347, 2), (key2092, -1), (key2092, -1), (key2303, -1), (key2303, -1), (key2341, -1), (key2341, -1), (key2200, -1), (key2200, -1), (key2310, -1), (key2310, -1), (key2347, -1), (key2347, -1), (key2095, 1), (key2095, 1), (key2305, 1), (key2305, 1), (key2343, 1), (key2343, 1)]

def rawRow2652 : Integer.Sparse Key := [(key2305, -2), (key2343, -2), (key2305, -2), (key2303, 1), (key2341, 1), (key2194, 1), (key2341, 1), (key2194, 1), (key2303, 1), (key2310, 2), (key2347, 2), (key2310, 2), (key2303, -1), (key2341, -1), (key2092, -1), (key2341, -1), (key2092, -1), (key2303, -1), (key2310, -1), (key2347, -1), (key2200, -1), (key2347, -1), (key2200, -1), (key2310, -1), (key2305, 1), (key2343, 1), (key2095, 1), (key2343, 1), (key2095, 1), (key2305, 1)]

def rawRow2653 : Integer.Sparse Key := [(key2343, -2), (key2305, -2), (key2305, -2), (key2341, 1), (key2303, 1), (key2341, 1), (key2194, 1), (key2303, 1), (key2194, 1), (key2347, 2), (key2310, 2), (key2310, 2), (key2341, -1), (key2303, -1), (key2341, -1), (key2092, -1), (key2303, -1), (key2092, -1), (key2347, -1), (key2310, -1), (key2347, -1), (key2200, -1), (key2310, -1), (key2200, -1), (key2343, 1), (key2305, 1), (key2343, 1), (key2095, 1), (key2305, 1), (key2095, 1)]

def rawRow2654 : Integer.Sparse Key := [(key2200, -2), (key2200, -2), (key2200, -2), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2095, 2), (key2095, 2), (key2095, 2), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1)]

def rawRow2655 : Integer.Sparse Key := [(key2310, -2), (key2310, -2), (key2347, -2), (key2200, 1), (key2200, 1), (key2310, 1), (key2310, 1), (key2347, 1), (key2347, 1), (key2305, 2), (key2305, 2), (key2343, 2), (key2095, -1), (key2095, -1), (key2305, -1), (key2305, -1), (key2343, -1), (key2343, -1), (key2194, -1), (key2194, -1), (key2303, -1), (key2303, -1), (key2341, -1), (key2341, -1), (key2092, 1), (key2092, 1), (key2303, 1), (key2303, 1), (key2341, 1), (key2341, 1)]

def rawRow2656 : Integer.Sparse Key := [(key2310, -2), (key2347, -2), (key2310, -2), (key2310, 1), (key2347, 1), (key2200, 1), (key2347, 1), (key2200, 1), (key2310, 1), (key2305, 2), (key2343, 2), (key2305, 2), (key2305, -1), (key2343, -1), (key2095, -1), (key2343, -1), (key2095, -1), (key2305, -1), (key2303, -1), (key2341, -1), (key2194, -1), (key2341, -1), (key2194, -1), (key2303, -1), (key2303, 1), (key2341, 1), (key2092, 1), (key2341, 1), (key2092, 1), (key2303, 1)]

def rawRow2657 : Integer.Sparse Key := [(key2347, -2), (key2310, -2), (key2310, -2), (key2347, 1), (key2310, 1), (key2347, 1), (key2200, 1), (key2310, 1), (key2200, 1), (key2343, 2), (key2305, 2), (key2305, 2), (key2343, -1), (key2305, -1), (key2343, -1), (key2095, -1), (key2305, -1), (key2095, -1), (key2341, -1), (key2303, -1), (key2341, -1), (key2194, -1), (key2303, -1), (key2194, -1), (key2341, 1), (key2303, 1), (key2341, 1), (key2092, 1), (key2303, 1), (key2092, 1)]

def rawRow2658 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key778, -2), (key778, 6), (key801, 2), (key803, 2), (key803, 2), (key803, -2), (key803, -2), (key811, -2), (key836, -6), (key836, 2), (key836, 2), (key839, 2)]

def rawRow2659 : Integer.Sparse Key := [(key778, -2), (key776, -2), (key778, -2), (key778, 6), (key803, 2), (key801, 2), (key803, 2), (key803, -2), (key811, -2), (key803, -2), (key836, -6), (key836, 2), (key839, 2), (key836, 2)]

def rawRow2660 : Integer.Sparse Key := [(key778, -2), (key778, -2), (key776, -2), (key778, 6), (key803, 2), (key803, 2), (key801, 2), (key811, -2), (key803, -2), (key803, -2), (key836, -6), (key839, 2), (key836, 2), (key836, 2)]

def rawRow2661 : Integer.Sparse Key := [(key778, -2), (key778, -2), (key778, -2), (key776, 6), (key811, 2), (key811, 2), (key811, 2), (key801, -2), (key801, -2), (key801, -2), (key839, -6), (key836, 2), (key836, 2), (key836, 2)]

def rawRow2662 : Integer.Sparse Key := [(key801, -2), (key803, -2), (key803, -2), (key811, 6), (key776, 2), (key778, 2), (key778, 2), (key836, -2), (key836, -2), (key839, -2), (key778, -6), (key803, 2), (key803, 2), (key811, 2)]

def rawRow2663 : Integer.Sparse Key := [(key803, -2), (key801, -2), (key803, -2), (key811, 6), (key778, 2), (key776, 2), (key778, 2), (key836, -2), (key839, -2), (key836, -2), (key778, -6), (key803, 2), (key811, 2), (key803, 2)]

def rawRow2664 : Integer.Sparse Key := [(key803, -2), (key803, -2), (key801, -2), (key811, 6), (key778, 2), (key778, 2), (key776, 2), (key839, -2), (key836, -2), (key836, -2), (key778, -6), (key811, 2), (key803, 2), (key803, 2)]

def rawRow2665 : Integer.Sparse Key := [(key803, -2), (key803, -2), (key811, -2), (key801, 6), (key836, 2), (key836, 2), (key839, 2), (key776, -2), (key801, -2), (key801, -2), (key811, -6), (key778, 2), (key803, 2), (key803, 2)]

def rawRow2666 : Integer.Sparse Key := [(key803, -2), (key811, -2), (key803, -2), (key801, 6), (key836, 2), (key839, 2), (key836, 2), (key801, -2), (key776, -2), (key801, -2), (key811, -6), (key803, 2), (key778, 2), (key803, 2)]

def rawRow2667 : Integer.Sparse Key := [(key811, -2), (key803, -2), (key803, -2), (key801, 6), (key839, 2), (key836, 2), (key836, 2), (key801, -2), (key801, -2), (key776, -2), (key811, -6), (key803, 2), (key803, 2), (key778, 2)]

def rawRow2668 : Integer.Sparse Key := [(key836, -2), (key836, -2), (key836, -2), (key839, 6), (key778, 2), (key778, 2), (key778, 2), (key811, -2), (key811, -2), (key811, -2), (key776, -6), (key801, 2), (key801, 2), (key801, 2)]

def rawRow2669 : Integer.Sparse Key := [(key836, -2), (key836, -2), (key839, -2), (key836, 6), (key803, 2), (key803, 2), (key811, 2), (key778, -2), (key803, -2), (key803, -2), (key801, -6), (key776, 2), (key801, 2), (key801, 2)]

def rawRow2670 : Integer.Sparse Key := [(key836, -2), (key839, -2), (key836, -2), (key836, 6), (key803, 2), (key811, 2), (key803, 2), (key803, -2), (key778, -2), (key803, -2), (key801, -6), (key801, 2), (key776, 2), (key801, 2)]

def rawRow2671 : Integer.Sparse Key := [(key839, -2), (key836, -2), (key836, -2), (key836, 6), (key811, 2), (key803, 2), (key803, 2), (key803, -2), (key803, -2), (key778, -2), (key801, -6), (key801, 2), (key801, 2), (key776, 2)]

def rawRow2672 : Integer.Sparse Key := [(key2407, -2), (key2441, -2), (key2441, -2), (key2410, 1), (key2410, 1), (key2441, 1), (key2441, 1), (key2445, 1), (key2445, 1), (key2473, 2), (key2507, 2), (key2507, 2), (key2483, -1), (key2483, -1), (key2507, -1), (key2507, -1), (key2526, -1), (key2526, -1), (key2539, -1), (key2539, -1), (key2555, -1), (key2555, -1), (key2557, -1), (key2557, -1), (key2544, 1), (key2544, 1), (key2555, 1), (key2555, 1), (key2565, 1), (key2565, 1)]

def rawRow2673 : Integer.Sparse Key := [(key2441, -2), (key2407, -2), (key2441, -2), (key2441, 1), (key2445, 1), (key2410, 1), (key2445, 1), (key2410, 1), (key2441, 1), (key2507, 2), (key2473, 2), (key2507, 2), (key2507, -1), (key2526, -1), (key2483, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2555, -1), (key2557, -1), (key2539, -1), (key2557, -1), (key2539, -1), (key2555, -1), (key2555, 1), (key2565, 1), (key2544, 1), (key2565, 1), (key2544, 1), (key2555, 1)]

def rawRow2674 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2407, -2), (key2445, 1), (key2441, 1), (key2445, 1), (key2410, 1), (key2441, 1), (key2410, 1), (key2507, 2), (key2507, 2), (key2473, 2), (key2526, -1), (key2507, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2483, -1), (key2557, -1), (key2555, -1), (key2557, -1), (key2539, -1), (key2555, -1), (key2539, -1), (key2565, 1), (key2555, 1), (key2565, 1), (key2544, 1), (key2555, 1), (key2544, 1)]

def rawRow2675 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2445, -2), (key2407, 1), (key2410, 1), (key2407, 1), (key2441, 1), (key2410, 1), (key2441, 1), (key2483, 2), (key2483, 2), (key2526, 2), (key2473, -1), (key2483, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2507, -1), (key2544, -1), (key2545, -1), (key2544, -1), (key2565, -1), (key2545, -1), (key2565, -1), (key2539, 1), (key2545, 1), (key2539, 1), (key2557, 1), (key2545, 1), (key2557, 1)]

def rawRow2676 : Integer.Sparse Key := [(key2410, -2), (key2445, -2), (key2410, -2), (key2410, 1), (key2407, 1), (key2441, 1), (key2407, 1), (key2441, 1), (key2410, 1), (key2483, 2), (key2526, 2), (key2483, 2), (key2483, -1), (key2473, -1), (key2507, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2545, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2545, -1), (key2545, 1), (key2539, 1), (key2557, 1), (key2539, 1), (key2557, 1), (key2545, 1)]

def rawRow2677 : Integer.Sparse Key := [(key2445, -2), (key2410, -2), (key2410, -2), (key2441, 1), (key2441, 1), (key2410, 1), (key2410, 1), (key2407, 1), (key2407, 1), (key2526, 2), (key2483, 2), (key2483, 2), (key2507, -1), (key2507, -1), (key2483, -1), (key2483, -1), (key2473, -1), (key2473, -1), (key2565, -1), (key2565, -1), (key2545, -1), (key2545, -1), (key2544, -1), (key2544, -1), (key2557, 1), (key2557, 1), (key2545, 1), (key2545, 1), (key2539, 1), (key2539, 1)]

def rawRow2678 : Integer.Sparse Key := [(key2848, -2), (key2970, -2), (key2970, -2), (key2882, 1), (key2882, 1), (key2991, 1), (key2991, 1), (key2993, 1), (key2993, 1), (key2407, 2), (key2441, 2), (key2441, 2), (key2544, -1), (key2544, -1), (key2555, -1), (key2555, -1), (key2565, -1), (key2565, -1), (key2410, -1), (key2410, -1), (key2441, -1), (key2441, -1), (key2445, -1), (key2445, -1), (key2483, 1), (key2483, 1), (key2507, 1), (key2507, 1), (key2526, 1), (key2526, 1)]

def rawRow2679 : Integer.Sparse Key := [(key2970, -2), (key2848, -2), (key2970, -2), (key2991, 1), (key2993, 1), (key2882, 1), (key2993, 1), (key2882, 1), (key2991, 1), (key2441, 2), (key2407, 2), (key2441, 2), (key2555, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2441, -1), (key2445, -1), (key2410, -1), (key2445, -1), (key2410, -1), (key2441, -1), (key2507, 1), (key2526, 1), (key2483, 1), (key2526, 1), (key2483, 1), (key2507, 1)]

def rawRow2680 : Integer.Sparse Key := [(key2970, -2), (key2970, -2), (key2848, -2), (key2993, 1), (key2991, 1), (key2993, 1), (key2882, 1), (key2991, 1), (key2882, 1), (key2441, 2), (key2441, 2), (key2407, 2), (key2565, -1), (key2555, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2544, -1), (key2445, -1), (key2441, -1), (key2445, -1), (key2410, -1), (key2441, -1), (key2410, -1), (key2526, 1), (key2507, 1), (key2526, 1), (key2483, 1), (key2507, 1), (key2483, 1)]

def rawRow2681 : Integer.Sparse Key := [(key2595, -2), (key2882, -2), (key2993, -2), (key2592, 1), (key2595, 1), (key2848, 1), (key2970, 1), (key2882, 1), (key2991, 1), (key2602, 2), (key2912, 2), (key3003, 2), (key2379, -1), (key2393, -1), (key2407, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2395, -1), (key2483, -1), (key2526, -1), (key2545, -1), (key2565, -1), (key2382, 1), (key2395, 1), (key2410, 1), (key2445, 1), (key2545, 1), (key2557, 1)]

def rawRow2682 : Integer.Sparse Key := [(key2595, -2), (key2993, -2), (key2882, -2), (key2595, 1), (key2592, 1), (key2970, 1), (key2848, 1), (key2991, 1), (key2882, 1), (key2602, 2), (key3003, 2), (key2912, 2), (key2393, -1), (key2379, -1), (key2441, -1), (key2407, -1), (key2555, -1), (key2544, -1), (key2395, -1), (key2393, -1), (key2526, -1), (key2483, -1), (key2565, -1), (key2545, -1), (key2395, 1), (key2382, 1), (key2445, 1), (key2410, 1), (key2557, 1), (key2545, 1)]

def rawRow2683 : Integer.Sparse Key := [(key2882, -2), (key2595, -2), (key2993, -2), (key2848, 1), (key2882, 1), (key2592, 1), (key2991, 1), (key2595, 1), (key2970, 1), (key2912, 2), (key2602, 2), (key3003, 2), (key2771, -1), (key2912, -1), (key2592, -1), (key2991, -1), (key2393, -1), (key2441, -1), (key2483, -1), (key2545, -1), (key2393, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2410, 1), (key2545, 1), (key2382, 1), (key2557, 1), (key2395, 1), (key2445, 1)]

def rawRow2684 : Integer.Sparse Key := [(key2882, -2), (key2993, -2), (key2595, -2), (key2882, 1), (key2848, 1), (key2991, 1), (key2592, 1), (key2970, 1), (key2595, 1), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, -1), (key2771, -1), (key2991, -1), (key2592, -1), (key2441, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2526, -1), (key2395, -1), (key2545, 1), (key2410, 1), (key2557, 1), (key2382, 1), (key2445, 1), (key2395, 1)]

def rawRow2685 : Integer.Sparse Key := [(key2993, -2), (key2595, -2), (key2882, -2), (key2970, 1), (key2991, 1), (key2595, 1), (key2882, 1), (key2592, 1), (key2848, 1), (key3003, 2), (key2602, 2), (key2912, 2), (key2933, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2379, -1), (key2407, -1), (key2526, -1), (key2565, -1), (key2395, -1), (key2545, -1), (key2393, -1), (key2483, -1), (key2445, 1), (key2557, 1), (key2395, 1), (key2545, 1), (key2382, 1), (key2410, 1)]

def rawRow2686 : Integer.Sparse Key := [(key2993, -2), (key2882, -2), (key2595, -2), (key2991, 1), (key2970, 1), (key2882, 1), (key2595, 1), (key2848, 1), (key2592, 1), (key3003, 2), (key2912, 2), (key2602, 2), (key2991, -1), (key2933, -1), (key2912, -1), (key2602, -1), (key2771, -1), (key2592, -1), (key2565, -1), (key2526, -1), (key2545, -1), (key2395, -1), (key2483, -1), (key2393, -1), (key2557, 1), (key2445, 1), (key2545, 1), (key2395, 1), (key2410, 1), (key2382, 1)]

def rawRow2687 : Integer.Sparse Key := [(key2891, -2), (key2891, -2), (key2996, -2), (key2912, 1), (key2914, 1), (key2912, 1), (key3003, 1), (key2914, 1), (key3003, 1), (key2774, 2), (key2774, 2), (key2934, 2), (key2882, -1), (key2914, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2993, -1), (key2407, -1), (key2410, -1), (key2407, -1), (key2441, -1), (key2410, -1), (key2441, -1), (key2473, 1), (key2483, 1), (key2473, 1), (key2507, 1), (key2483, 1), (key2507, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2688 : Integer.Sparse Key := [(key2891, -2), (key2996, -2), (key2891, -2), (key2914, 1), (key2912, 1), (key3003, 1), (key2912, 1), (key3003, 1), (key2914, 1), (key2774, 2), (key2934, 2), (key2774, 2), (key2914, -1), (key2882, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2410, -1), (key2407, -1), (key2441, -1), (key2407, -1), (key2441, -1), (key2410, -1), (key2483, 1), (key2473, 1), (key2507, 1), (key2473, 1), (key2507, 1), (key2483, 1)]

def rawRow2689 : Integer.Sparse Key := [(key2996, -2), (key2891, -2), (key2891, -2), (key3003, 1), (key3003, 1), (key2914, 1), (key2914, 1), (key2912, 1), (key2912, 1), (key2934, 2), (key2774, 2), (key2774, 2), (key2993, -1), (key2993, -1), (key2914, -1), (key2914, -1), (key2882, -1), (key2882, -1), (key2441, -1), (key2441, -1), (key2410, -1), (key2410, -1), (key2407, -1), (key2407, -1), (key2507, 1), (key2507, 1), (key2483, 1), (key2483, 1), (key2473, 1), (key2473, 1)]

def rawRow2690 : Integer.Sparse Key := [(key2602, -2), (key2912, -2), (key3003, -2), (key2602, 1), (key2603, 1), (key2891, 1), (key2996, 1), (key2914, 1), (key3003, 1), (key2595, 2), (key2882, 2), (key2993, 2), (key2595, -1), (key2603, -1), (key2774, -1), (key2934, -1), (key2914, -1), (key2993, -1), (key2592, -1), (key2595, -1), (key2848, -1), (key2970, -1), (key2882, -1), (key2991, -1), (key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1)]

def rawRow2691 : Integer.Sparse Key := [(key2602, -2), (key3003, -2), (key2912, -2), (key2603, 1), (key2602, 1), (key2996, 1), (key2891, 1), (key3003, 1), (key2914, 1), (key2595, 2), (key2993, 2), (key2882, 2), (key2603, -1), (key2595, -1), (key2934, -1), (key2774, -1), (key2993, -1), (key2914, -1), (key2595, -1), (key2592, -1), (key2970, -1), (key2848, -1), (key2991, -1), (key2882, -1), (key2393, 1), (key2379, 1), (key2441, 1), (key2407, 1), (key2555, 1), (key2544, 1)]

def rawRow2692 : Integer.Sparse Key := [(key2912, -2), (key2602, -2), (key3003, -2), (key2891, 1), (key2914, 1), (key2602, 1), (key3003, 1), (key2603, 1), (key2996, 1), (key2882, 2), (key2595, 2), (key2993, 2), (key2774, -1), (key2914, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2848, -1), (key2882, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2771, 1), (key2912, 1), (key2592, 1), (key2991, 1), (key2393, 1), (key2441, 1)]

def rawRow2693 : Integer.Sparse Key := [(key2912, -2), (key3003, -2), (key2602, -2), (key2914, 1), (key2891, 1), (key3003, 1), (key2602, 1), (key2996, 1), (key2603, 1), (key2882, 2), (key2993, 2), (key2595, 2), (key2914, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2934, -1), (key2603, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2970, -1), (key2595, -1), (key2912, 1), (key2771, 1), (key2991, 1), (key2592, 1), (key2441, 1), (key2393, 1)]

def rawRow2694 : Integer.Sparse Key := [(key3003, -2), (key2602, -2), (key2912, -2), (key2996, 1), (key3003, 1), (key2603, 1), (key2914, 1), (key2602, 1), (key2891, 1), (key2993, 2), (key2595, 2), (key2882, 2), (key2934, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2595, -1), (key2774, -1), (key2970, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2592, -1), (key2848, -1), (key2933, 1), (key2991, 1), (key2602, 1), (key2912, 1), (key2379, 1), (key2407, 1)]

def rawRow2695 : Integer.Sparse Key := [(key3003, -2), (key2912, -2), (key2602, -2), (key3003, 1), (key2996, 1), (key2914, 1), (key2603, 1), (key2891, 1), (key2602, 1), (key2993, 2), (key2882, 2), (key2595, 2), (key2993, -1), (key2934, -1), (key2914, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2991, -1), (key2970, -1), (key2882, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key2991, 1), (key2933, 1), (key2912, 1), (key2602, 1), (key2771, 1), (key2592, 1)]

def rawRow2696 : Integer.Sparse Key := [(key1254, -6), (key1254, 2), (key1263, 2), (key1263, 2), (key1529, 6), (key1529, -2), (key1763, -2), (key1763, -2), (key1607, -2), (key1646, -2), (key1646, -2), (key1607, 2), (key1804, 2), (key1804, 2)]

def rawRow2697 : Integer.Sparse Key := [(key1254, -6), (key1263, 2), (key1254, 2), (key1263, 2), (key1529, 6), (key1763, -2), (key1529, -2), (key1763, -2), (key1646, -2), (key1607, -2), (key1646, -2), (key1804, 2), (key1607, 2), (key1804, 2)]

def rawRow2698 : Integer.Sparse Key := [(key1254, -6), (key1263, 2), (key1263, 2), (key1254, 2), (key1529, 6), (key1763, -2), (key1763, -2), (key1529, -2), (key1646, -2), (key1646, -2), (key1607, -2), (key1804, 2), (key1804, 2), (key1607, 2)]

def rawRow2699 : Integer.Sparse Key := [(key1263, -6), (key1254, 2), (key1254, 2), (key1263, 2), (key1763, 6), (key1529, -2), (key1529, -2), (key1763, -2), (key1804, -2), (key1804, -2), (key1835, -2), (key1646, 2), (key1646, 2), (key1835, 2)]

def rawRow2700 : Integer.Sparse Key := [(key1263, -6), (key1254, 2), (key1263, 2), (key1254, 2), (key1763, 6), (key1529, -2), (key1763, -2), (key1529, -2), (key1804, -2), (key1835, -2), (key1804, -2), (key1646, 2), (key1835, 2), (key1646, 2)]

def rawRow2701 : Integer.Sparse Key := [(key1263, -6), (key1263, 2), (key1254, 2), (key1254, 2), (key1763, 6), (key1763, -2), (key1529, -2), (key1529, -2), (key1835, -2), (key1804, -2), (key1804, -2), (key1835, 2), (key1646, 2), (key1646, 2)]

def rawRow2702 : Integer.Sparse Key := [(key1529, -6), (key1607, 2), (key1646, 2), (key1646, 2), (key1254, 6), (key1607, -2), (key1804, -2), (key1804, -2), (key1254, -2), (key1263, -2), (key1263, -2), (key1529, 2), (key1763, 2), (key1763, 2)]

def rawRow2703 : Integer.Sparse Key := [(key1529, -6), (key1646, 2), (key1607, 2), (key1646, 2), (key1254, 6), (key1804, -2), (key1607, -2), (key1804, -2), (key1263, -2), (key1254, -2), (key1263, -2), (key1763, 2), (key1529, 2), (key1763, 2)]

def rawRow2704 : Integer.Sparse Key := [(key1529, -6), (key1646, 2), (key1646, 2), (key1607, 2), (key1254, 6), (key1804, -2), (key1804, -2), (key1607, -2), (key1263, -2), (key1263, -2), (key1254, -2), (key1763, 2), (key1763, 2), (key1529, 2)]

def rawRow2705 : Integer.Sparse Key := [(key1646, -6), (key1529, 2), (key1607, 2), (key1646, 2), (key1804, 6), (key1254, -2), (key1607, -2), (key1804, -2), (key1763, -2), (key1804, -2), (key1835, -2), (key1263, 2), (key1646, 2), (key1835, 2)]

def rawRow2706 : Integer.Sparse Key := [(key1646, -6), (key1529, 2), (key1646, 2), (key1607, 2), (key1804, 6), (key1254, -2), (key1804, -2), (key1607, -2), (key1763, -2), (key1835, -2), (key1804, -2), (key1263, 2), (key1835, 2), (key1646, 2)]

def rawRow2707 : Integer.Sparse Key := [(key1646, -6), (key1607, 2), (key1529, 2), (key1646, 2), (key1804, 6), (key1607, -2), (key1254, -2), (key1804, -2), (key1804, -2), (key1763, -2), (key1835, -2), (key1646, 2), (key1263, 2), (key1835, 2)]

def rawRow2708 : Integer.Sparse Key := [(key1646, -6), (key1607, 2), (key1646, 2), (key1529, 2), (key1804, 6), (key1607, -2), (key1804, -2), (key1254, -2), (key1804, -2), (key1835, -2), (key1763, -2), (key1646, 2), (key1835, 2), (key1263, 2)]

def rawRow2709 : Integer.Sparse Key := [(key1646, -6), (key1646, 2), (key1529, 2), (key1607, 2), (key1804, 6), (key1804, -2), (key1254, -2), (key1607, -2), (key1835, -2), (key1763, -2), (key1804, -2), (key1835, 2), (key1263, 2), (key1646, 2)]

def rawRow2710 : Integer.Sparse Key := [(key1646, -6), (key1646, 2), (key1607, 2), (key1529, 2), (key1804, 6), (key1804, -2), (key1607, -2), (key1254, -2), (key1835, -2), (key1804, -2), (key1763, -2), (key1835, 2), (key1646, 2), (key1263, 2)]

def rawRow2711 : Integer.Sparse Key := [(key1763, -6), (key1804, 2), (key1804, 2), (key1835, 2), (key1263, 6), (key1646, -2), (key1646, -2), (key1835, -2), (key1254, -2), (key1254, -2), (key1263, -2), (key1529, 2), (key1529, 2), (key1763, 2)]

def rawRow2712 : Integer.Sparse Key := [(key1763, -6), (key1804, 2), (key1835, 2), (key1804, 2), (key1263, 6), (key1646, -2), (key1835, -2), (key1646, -2), (key1254, -2), (key1263, -2), (key1254, -2), (key1529, 2), (key1763, 2), (key1529, 2)]

def rawRow2713 : Integer.Sparse Key := [(key1763, -6), (key1835, 2), (key1804, 2), (key1804, 2), (key1263, 6), (key1835, -2), (key1646, -2), (key1646, -2), (key1263, -2), (key1254, -2), (key1254, -2), (key1763, 2), (key1529, 2), (key1529, 2)]

def rawRow2714 : Integer.Sparse Key := [(key1804, -6), (key1763, 2), (key1804, 2), (key1835, 2), (key1646, 6), (key1263, -2), (key1646, -2), (key1835, -2), (key1529, -2), (key1607, -2), (key1646, -2), (key1254, 2), (key1607, 2), (key1804, 2)]

def rawRow2715 : Integer.Sparse Key := [(key1804, -6), (key1763, 2), (key1835, 2), (key1804, 2), (key1646, 6), (key1263, -2), (key1835, -2), (key1646, -2), (key1529, -2), (key1646, -2), (key1607, -2), (key1254, 2), (key1804, 2), (key1607, 2)]

def rawRow2716 : Integer.Sparse Key := [(key1804, -6), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 6), (key1646, -2), (key1263, -2), (key1835, -2), (key1607, -2), (key1529, -2), (key1646, -2), (key1607, 2), (key1254, 2), (key1804, 2)]

def rawRow2717 : Integer.Sparse Key := [(key1804, -6), (key1804, 2), (key1835, 2), (key1763, 2), (key1646, 6), (key1646, -2), (key1835, -2), (key1263, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1607, 2), (key1804, 2), (key1254, 2)]

def rawRow2718 : Integer.Sparse Key := [(key1804, -6), (key1835, 2), (key1763, 2), (key1804, 2), (key1646, 6), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1804, 2), (key1254, 2), (key1607, 2)]

def rawRow2719 : Integer.Sparse Key := [(key1804, -6), (key1835, 2), (key1804, 2), (key1763, 2), (key1646, 6), (key1835, -2), (key1646, -2), (key1263, -2), (key1646, -2), (key1607, -2), (key1529, -2), (key1804, 2), (key1607, 2), (key1254, 2)]

def rawRow2720 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2383, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2484, -1), (key2484, -1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1)]

def rawRow2721 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2378, -2), (key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2484, -1), (key2472, -1), (key2484, -1), (key2472, -1), (key2480, -1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1)]

def rawRow2722 : Integer.Sparse Key := [(key2383, -2), (key2378, -2), (key2378, -2), (key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2484, -1), (key2480, -1), (key2484, -1), (key2472, -1), (key2480, -1), (key2472, -1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1)]

def rawRow2723 : Integer.Sparse Key := [(key2390, -2), (key2394, -2), (key2394, -2), (key2378, 1), (key2383, 1), (key2378, 1), (key2394, 1), (key2383, 1), (key2394, 1), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, -1), (key2411, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2443, -1), (key2503, -1), (key2509, -1), (key2503, -1), (key2524, -1), (key2509, -1), (key2524, -1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1)]

def rawRow2724 : Integer.Sparse Key := [(key2394, -2), (key2390, -2), (key2394, -2), (key2383, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2383, 1), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2503, -1), (key2524, -1), (key2503, -1), (key2524, -1), (key2509, -1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1)]

def rawRow2725 : Integer.Sparse Key := [(key2394, -2), (key2394, -2), (key2390, -2), (key2394, 1), (key2394, 1), (key2383, 1), (key2383, 1), (key2378, 1), (key2378, 1), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, -1), (key2443, -1), (key2411, -1), (key2411, -1), (key2406, -1), (key2406, -1), (key2524, -1), (key2524, -1), (key2509, -1), (key2509, -1), (key2503, -1), (key2503, -1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1)]

def rawRow2726 : Integer.Sparse Key := [(key2766, -2), (key2766, -2), (key2772, -2), (key2843, 1), (key2843, 1), (key2887, 1), (key2887, 1), (key2889, 1), (key2889, 1), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2968, -1), (key2968, -1), (key2378, -1), (key2378, -1), (key2390, -1), (key2390, -1), (key2394, -1), (key2394, -1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1)]

def rawRow2727 : Integer.Sparse Key := [(key2766, -2), (key2772, -2), (key2766, -2), (key2887, 1), (key2889, 1), (key2843, 1), (key2889, 1), (key2843, 1), (key2887, 1), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, -1), (key2968, -1), (key2843, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2390, -1), (key2394, -1), (key2378, -1), (key2394, -1), (key2378, -1), (key2390, -1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1)]

def rawRow2728 : Integer.Sparse Key := [(key2772, -2), (key2766, -2), (key2766, -2), (key2889, 1), (key2887, 1), (key2889, 1), (key2843, 1), (key2887, 1), (key2843, 1), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, -1), (key2966, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2843, -1), (key2394, -1), (key2390, -1), (key2394, -1), (key2378, -1), (key2390, -1), (key2378, -1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1)]

def rawRow2729 : Integer.Sparse Key := [(key2887, -2), (key2889, -2), (key2910, -2), (key2766, 1), (key2772, 1), (key2843, 1), (key2889, 1), (key2880, 1), (key2910, 1), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2929, -1), (key2931, -1), (key2966, -1), (key2995, -1), (key2989, -1), (key3002, -1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1)]

def rawRow2730 : Integer.Sparse Key := [(key2889, -2), (key2887, -2), (key2910, -2), (key2772, 1), (key2766, 1), (key2889, 1), (key2843, 1), (key2910, 1), (key2880, 1), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2931, -1), (key2929, -1), (key2995, -1), (key2966, -1), (key3002, -1), (key2989, -1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1)]

def rawRow2731 : Integer.Sparse Key := [(key2887, -2), (key2910, -2), (key2889, -2), (key2843, 1), (key2880, 1), (key2766, 1), (key2910, 1), (key2772, 1), (key2889, 1), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1)]

def rawRow2732 : Integer.Sparse Key := [(key2910, -2), (key2887, -2), (key2889, -2), (key2880, 1), (key2843, 1), (key2910, 1), (key2766, 1), (key2889, 1), (key2772, 1), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2995, -1), (key2931, -1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1)]

def rawRow2733 : Integer.Sparse Key := [(key2889, -2), (key2910, -2), (key2887, -2), (key2889, 1), (key2910, 1), (key2772, 1), (key2880, 1), (key2766, 1), (key2843, 1), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2995, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2929, -1), (key2966, -1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1)]

def rawRow2734 : Integer.Sparse Key := [(key2910, -2), (key2889, -2), (key2887, -2), (key2910, 1), (key2889, 1), (key2880, 1), (key2772, 1), (key2843, 1), (key2766, 1), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key3002, -1), (key2995, -1), (key2989, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1)]

def rawRow2735 : Integer.Sparse Key := [(key2929, -2), (key2931, -2), (key2931, -2), (key2966, 1), (key2968, 1), (key2966, 1), (key2995, 1), (key2968, 1), (key2995, 1), (key2598, 2), (key2600, 2), (key2600, 2), (key2887, -1), (key2889, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2995, -1), (key2587, -1), (key2593, -1), (key2587, -1), (key2600, -1), (key2593, -1), (key2600, -1), (key2766, 1), (key2772, 1), (key2766, 1), (key2931, 1), (key2772, 1), (key2931, 1)]

def rawRow2736 : Integer.Sparse Key := [(key2931, -2), (key2929, -2), (key2931, -2), (key2968, 1), (key2966, 1), (key2995, 1), (key2966, 1), (key2995, 1), (key2968, 1), (key2600, 2), (key2598, 2), (key2600, 2), (key2889, -1), (key2887, -1), (key2995, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2593, -1), (key2587, -1), (key2600, -1), (key2587, -1), (key2600, -1), (key2593, -1), (key2772, 1), (key2766, 1), (key2931, 1), (key2766, 1), (key2931, 1), (key2772, 1)]

def rawRow2737 : Integer.Sparse Key := [(key2931, -2), (key2931, -2), (key2929, -2), (key2995, 1), (key2995, 1), (key2968, 1), (key2968, 1), (key2966, 1), (key2966, 1), (key2600, 2), (key2600, 2), (key2598, 2), (key2995, -1), (key2995, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key2600, -1), (key2600, -1), (key2593, -1), (key2593, -1), (key2587, -1), (key2587, -1), (key2931, 1), (key2931, 1), (key2772, 1), (key2772, 1), (key2766, 1), (key2766, 1)]

def rawRow2738 : Integer.Sparse Key := [(key2966, -2), (key2968, -2), (key2989, -2), (key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2887, 2), (key2889, 2), (key2910, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2766, -1), (key2772, -1), (key2843, -1), (key2889, -1), (key2880, -1), (key2910, -1), (key2587, 1), (key2593, 1), (key2843, 1), (key2968, 1), (key2880, 1), (key2989, 1)]

def rawRow2739 : Integer.Sparse Key := [(key2968, -2), (key2966, -2), (key2989, -2), (key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2889, 2), (key2887, 2), (key2910, 2), (key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2772, -1), (key2766, -1), (key2889, -1), (key2843, -1), (key2910, -1), (key2880, -1), (key2593, 1), (key2587, 1), (key2968, 1), (key2843, 1), (key2989, 1), (key2880, 1)]

def rawRow2740 : Integer.Sparse Key := [(key2966, -2), (key2989, -2), (key2968, -2), (key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 2), (key2910, 2), (key2889, 2), (key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2843, -1), (key2880, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2843, 1), (key2880, 1), (key2587, 1), (key2989, 1), (key2593, 1), (key2968, 1)]

def rawRow2741 : Integer.Sparse Key := [(key2989, -2), (key2966, -2), (key2968, -2), (key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2889, -1), (key2772, -1), (key2880, 1), (key2843, 1), (key2989, 1), (key2587, 1), (key2968, 1), (key2593, 1)]

def rawRow2742 : Integer.Sparse Key := [(key2968, -2), (key2989, -2), (key2966, -2), (key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2889, 2), (key2910, 2), (key2887, 2), (key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2889, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2766, -1), (key2843, -1), (key2968, 1), (key2989, 1), (key2593, 1), (key2880, 1), (key2587, 1), (key2843, 1)]

def rawRow2743 : Integer.Sparse Key := [(key2989, -2), (key2968, -2), (key2966, -2), (key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key2910, 2), (key2889, 2), (key2887, 2), (key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2910, -1), (key2889, -1), (key2880, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2989, 1), (key2968, 1), (key2880, 1), (key2593, 1), (key2843, 1), (key2587, 1)]

def rawRow2744 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key984, -2), (key984, 6), (key1090, 2), (key1090, 2), (key1098, 2), (key1098, -2), (key1183, -2), (key1183, -2), (key1169, -6), (key1169, 2), (key1220, 2), (key1220, 2)]

def rawRow2745 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key976, -2), (key984, 6), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, -2), (key1098, -2), (key1183, -2), (key1169, -6), (key1220, 2), (key1169, 2), (key1220, 2)]

def rawRow2746 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key976, -2), (key984, 6), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1098, -2), (key1169, -6), (key1220, 2), (key1220, 2), (key1169, 2)]

def rawRow2747 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key984, -2), (key976, 6), (key1180, 2), (key1183, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1220, -6), (key1169, 2), (key1169, 2), (key1220, 2)]

def rawRow2748 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key984, -2), (key976, 6), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1220, -6), (key1169, 2), (key1220, 2), (key1169, 2)]

def rawRow2749 : Integer.Sparse Key := [(key984, -2), (key984, -2), (key976, -2), (key976, 6), (key1183, 2), (key1183, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1220, -6), (key1220, 2), (key1169, 2), (key1169, 2)]

def rawRow2750 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1098, -2), (key1169, 6), (key976, 2), (key976, 2), (key984, 2), (key1169, -2), (key1220, -2), (key1220, -2), (key984, -6), (key1098, 2), (key1183, 2), (key1183, 2)]

def rawRow2751 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1090, -2), (key1169, 6), (key976, 2), (key984, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1220, -2), (key984, -6), (key1183, 2), (key1098, 2), (key1183, 2)]

def rawRow2752 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1090, -2), (key1169, 6), (key984, 2), (key976, 2), (key976, 2), (key1220, -2), (key1220, -2), (key1169, -2), (key984, -6), (key1183, 2), (key1183, 2), (key1098, 2)]

def rawRow2753 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1169, -2), (key1090, 6), (key1180, 2), (key1183, 2), (key1220, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1183, -6), (key984, 2), (key1098, 2), (key1183, 2)]

def rawRow2754 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1169, -2), (key1090, 6), (key1183, 2), (key1180, 2), (key1220, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1183, -6), (key984, 2), (key1183, 2), (key1098, 2)]

def rawRow2755 : Integer.Sparse Key := [(key1090, -2), (key1169, -2), (key1098, -2), (key1090, 6), (key1180, 2), (key1220, 2), (key1183, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1183, -6), (key1098, 2), (key984, 2), (key1183, 2)]

def rawRow2756 : Integer.Sparse Key := [(key1169, -2), (key1090, -2), (key1098, -2), (key1090, 6), (key1220, 2), (key1180, 2), (key1183, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1183, -6), (key1098, 2), (key1183, 2), (key984, 2)]

def rawRow2757 : Integer.Sparse Key := [(key1098, -2), (key1169, -2), (key1090, -2), (key1090, 6), (key1183, 2), (key1220, 2), (key1180, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1183, -6), (key1183, 2), (key984, 2), (key1098, 2)]

def rawRow2758 : Integer.Sparse Key := [(key1169, -2), (key1098, -2), (key1090, -2), (key1090, 6), (key1220, 2), (key1183, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1183, -6), (key1183, 2), (key1098, 2), (key984, 2)]

def rawRow2759 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1183, -2), (key1220, 6), (key976, 2), (key984, 2), (key984, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key976, -6), (key1090, 2), (key1090, 2), (key1180, 2)]

def rawRow2760 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1183, -2), (key1220, 6), (key984, 2), (key976, 2), (key984, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key976, -6), (key1090, 2), (key1180, 2), (key1090, 2)]

def rawRow2761 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1180, -2), (key1220, 6), (key984, 2), (key984, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key976, -6), (key1180, 2), (key1090, 2), (key1090, 2)]

def rawRow2762 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1220, -2), (key1183, 6), (key1090, 2), (key1098, 2), (key1169, 2), (key984, -2), (key1098, -2), (key1183, -2), (key1090, -6), (key976, 2), (key1090, 2), (key1180, 2)]

def rawRow2763 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1220, -2), (key1183, 6), (key1098, 2), (key1090, 2), (key1169, 2), (key984, -2), (key1183, -2), (key1098, -2), (key1090, -6), (key976, 2), (key1180, 2), (key1090, 2)]

def rawRow2764 : Integer.Sparse Key := [(key1180, -2), (key1220, -2), (key1183, -2), (key1183, 6), (key1090, 2), (key1169, 2), (key1098, 2), (key1098, -2), (key984, -2), (key1183, -2), (key1090, -6), (key1090, 2), (key976, 2), (key1180, 2)]

def rawRow2765 : Integer.Sparse Key := [(key1220, -2), (key1180, -2), (key1183, -2), (key1183, 6), (key1169, 2), (key1090, 2), (key1098, 2), (key1098, -2), (key1183, -2), (key984, -2), (key1090, -6), (key1090, 2), (key1180, 2), (key976, 2)]

def rawRow2766 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1180, -2), (key1183, 6), (key1098, 2), (key1169, 2), (key1090, 2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -6), (key1180, 2), (key976, 2), (key1090, 2)]

def rawRow2767 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1180, -2), (key1183, 6), (key1169, 2), (key1098, 2), (key1090, 2), (key1183, -2), (key1098, -2), (key984, -2), (key1090, -6), (key1180, 2), (key1090, 2), (key976, 2)]

def rawRow2768 : Integer.Sparse Key := [(key2377, -6), (key2377, 2), (key2389, 2), (key2389, 2), (key2405, 6), (key2405, -2), (key2436, -2), (key2436, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2471, 2), (key2502, 2), (key2502, 2)]

def rawRow2769 : Integer.Sparse Key := [(key2377, -6), (key2389, 2), (key2377, 2), (key2389, 2), (key2405, 6), (key2436, -2), (key2405, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2502, 2), (key2471, 2), (key2502, 2)]

def rawRow2770 : Integer.Sparse Key := [(key2377, -6), (key2389, 2), (key2389, 2), (key2377, 2), (key2405, 6), (key2436, -2), (key2436, -2), (key2405, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, 2), (key2502, 2), (key2471, 2)]

def rawRow2771 : Integer.Sparse Key := [(key2389, -6), (key2377, 2), (key2377, 2), (key2389, 2), (key2436, 6), (key2405, -2), (key2405, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, 2), (key2479, 2), (key2518, 2)]

def rawRow2772 : Integer.Sparse Key := [(key2389, -6), (key2377, 2), (key2389, 2), (key2377, 2), (key2436, 6), (key2405, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2479, 2), (key2518, 2), (key2479, 2)]

def rawRow2773 : Integer.Sparse Key := [(key2389, -6), (key2389, 2), (key2377, 2), (key2377, 2), (key2436, 6), (key2436, -2), (key2405, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, 2), (key2479, 2), (key2479, 2)]

def rawRow2774 : Integer.Sparse Key := [(key2405, -6), (key2471, 2), (key2479, 2), (key2479, 2), (key2377, 6), (key2471, -2), (key2502, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, 2), (key2436, 2), (key2436, 2)]

def rawRow2775 : Integer.Sparse Key := [(key2405, -6), (key2479, 2), (key2471, 2), (key2479, 2), (key2377, 6), (key2502, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2389, -2), (key2436, 2), (key2405, 2), (key2436, 2)]

def rawRow2776 : Integer.Sparse Key := [(key2405, -6), (key2479, 2), (key2479, 2), (key2471, 2), (key2377, 6), (key2502, -2), (key2502, -2), (key2471, -2), (key2389, -2), (key2389, -2), (key2377, -2), (key2436, 2), (key2436, 2), (key2405, 2)]

def rawRow2777 : Integer.Sparse Key := [(key2479, -6), (key2405, 2), (key2471, 2), (key2479, 2), (key2502, 6), (key2377, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, 2), (key2479, 2), (key2518, 2)]

def rawRow2778 : Integer.Sparse Key := [(key2479, -6), (key2405, 2), (key2479, 2), (key2471, 2), (key2502, 6), (key2377, -2), (key2502, -2), (key2471, -2), (key2436, -2), (key2518, -2), (key2502, -2), (key2389, 2), (key2518, 2), (key2479, 2)]

def rawRow2779 : Integer.Sparse Key := [(key2479, -6), (key2471, 2), (key2405, 2), (key2479, 2), (key2502, 6), (key2471, -2), (key2377, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, 2), (key2389, 2), (key2518, 2)]

def rawRow2780 : Integer.Sparse Key := [(key2479, -6), (key2471, 2), (key2479, 2), (key2405, 2), (key2502, 6), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, 2), (key2518, 2), (key2389, 2)]

def rawRow2781 : Integer.Sparse Key := [(key2479, -6), (key2479, 2), (key2405, 2), (key2471, 2), (key2502, 6), (key2502, -2), (key2377, -2), (key2471, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2518, 2), (key2389, 2), (key2479, 2)]

def rawRow2782 : Integer.Sparse Key := [(key2479, -6), (key2479, 2), (key2471, 2), (key2405, 2), (key2502, 6), (key2502, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2502, -2), (key2436, -2), (key2518, 2), (key2479, 2), (key2389, 2)]

def rawRow2783 : Integer.Sparse Key := [(key2436, -6), (key2502, 2), (key2502, 2), (key2518, 2), (key2389, 6), (key2479, -2), (key2479, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, 2), (key2405, 2), (key2436, 2)]

def rawRow2784 : Integer.Sparse Key := [(key2436, -6), (key2502, 2), (key2518, 2), (key2502, 2), (key2389, 6), (key2479, -2), (key2518, -2), (key2479, -2), (key2377, -2), (key2389, -2), (key2377, -2), (key2405, 2), (key2436, 2), (key2405, 2)]

def rawRow2785 : Integer.Sparse Key := [(key2436, -6), (key2518, 2), (key2502, 2), (key2502, 2), (key2389, 6), (key2518, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, 2), (key2405, 2), (key2405, 2)]

def rawRow2786 : Integer.Sparse Key := [(key2502, -6), (key2436, 2), (key2502, 2), (key2518, 2), (key2479, 6), (key2389, -2), (key2479, -2), (key2518, -2), (key2405, -2), (key2471, -2), (key2479, -2), (key2377, 2), (key2471, 2), (key2502, 2)]

def rawRow2787 : Integer.Sparse Key := [(key2502, -6), (key2436, 2), (key2518, 2), (key2502, 2), (key2479, 6), (key2389, -2), (key2518, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, 2), (key2502, 2), (key2471, 2)]

def rawRow2788 : Integer.Sparse Key := [(key2502, -6), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 6), (key2479, -2), (key2389, -2), (key2518, -2), (key2471, -2), (key2405, -2), (key2479, -2), (key2471, 2), (key2377, 2), (key2502, 2)]

def rawRow2789 : Integer.Sparse Key := [(key2502, -6), (key2502, 2), (key2518, 2), (key2436, 2), (key2479, 6), (key2479, -2), (key2518, -2), (key2389, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, 2), (key2502, 2), (key2377, 2)]

def rawRow2790 : Integer.Sparse Key := [(key2502, -6), (key2518, 2), (key2436, 2), (key2502, 2), (key2479, 6), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 2), (key2377, 2), (key2471, 2)]

def rawRow2791 : Integer.Sparse Key := [(key2502, -6), (key2518, 2), (key2502, 2), (key2436, 2), (key2479, 6), (key2518, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, 2), (key2471, 2), (key2377, 2)]

def rawRow2792 : Integer.Sparse Key := [(key1531, -1), (key1531, -1), (key1765, -1), (key1765, -1), (key1768, -1), (key1768, -1), (key1536, 2), (key1768, 2), (key1768, 2), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1), (key1651, -1), (key1651, -1), (key1809, -1), (key1809, -1), (key1837, -1), (key1837, -1), (key1642, -2), (key1832, -2), (key1832, -2), (key1674, 1), (key1674, 1), (key1832, 1), (key1832, 1), (key1848, 1), (key1848, 1)]

def rawRow2793 : Integer.Sparse Key := [(key1765, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1768, 2), (key1536, 2), (key1768, 2), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1809, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1651, -1), (key1809, -1), (key1832, -2), (key1642, -2), (key1832, -2), (key1832, 1), (key1848, 1), (key1674, 1), (key1848, 1), (key1674, 1), (key1832, 1)]

def rawRow2794 : Integer.Sparse Key := [(key1768, -1), (key1765, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1531, -1), (key1768, 2), (key1768, 2), (key1536, 2), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1837, -1), (key1809, -1), (key1837, -1), (key1651, -1), (key1809, -1), (key1651, -1), (key1832, -2), (key1832, -2), (key1642, -2), (key1848, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1832, 1), (key1674, 1)]

def rawRow2795 : Integer.Sparse Key := [(key1531, -1), (key1536, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1768, -1), (key1531, 2), (key1531, 2), (key1765, 2), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1609, -1), (key1648, -1), (key1609, -1), (key1806, -1), (key1648, -1), (key1806, -1), (key1674, -2), (key1674, -2), (key1848, -2), (key1642, 1), (key1674, 1), (key1642, 1), (key1832, 1), (key1674, 1), (key1832, 1)]

def rawRow2796 : Integer.Sparse Key := [(key1536, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1531, 2), (key1765, 2), (key1531, 2), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1648, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1806, -1), (key1648, -1), (key1674, -2), (key1848, -2), (key1674, -2), (key1674, 1), (key1642, 1), (key1832, 1), (key1642, 1), (key1832, 1), (key1674, 1)]

def rawRow2797 : Integer.Sparse Key := [(key1768, -1), (key1768, -1), (key1536, -1), (key1536, -1), (key1531, -1), (key1531, -1), (key1765, 2), (key1531, 2), (key1531, 2), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1), (key1806, -1), (key1806, -1), (key1648, -1), (key1648, -1), (key1609, -1), (key1609, -1), (key1848, -2), (key1674, -2), (key1674, -2), (key1832, 1), (key1832, 1), (key1674, 1), (key1674, 1), (key1642, 1), (key1642, 1)]

def rawRow2798 : Integer.Sparse Key := [(key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1809, -1), (key1809, -1), (key1642, 2), (key1832, 2), (key1832, 2), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1), (key1674, -1), (key1674, -1), (key1832, -1), (key1832, -1), (key1848, -1), (key1848, -1), (key1536, -2), (key1768, -2), (key1768, -2), (key1651, 1), (key1651, 1), (key1809, 1), (key1809, 1), (key1837, 1), (key1837, 1)]

def rawRow2799 : Integer.Sparse Key := [(key1806, -1), (key1809, -1), (key1609, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1832, 2), (key1642, 2), (key1832, 2), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1832, -1), (key1848, -1), (key1674, -1), (key1848, -1), (key1674, -1), (key1832, -1), (key1768, -2), (key1536, -2), (key1768, -2), (key1809, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1651, 1), (key1809, 1)]

def rawRow2800 : Integer.Sparse Key := [(key1809, -1), (key1806, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1832, 2), (key1832, 2), (key1642, 2), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1), (key1848, -1), (key1832, -1), (key1848, -1), (key1674, -1), (key1832, -1), (key1674, -1), (key1768, -2), (key1768, -2), (key1536, -2), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1809, 1), (key1651, 1)]

def rawRow2801 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1609, -1), (key1809, -1), (key1642, -1), (key1832, -1), (key1256, 2), (key1609, 2), (key1806, 2), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1), (key1256, -1), (key1265, -1), (key1531, -1), (key1765, -1), (key1648, -1), (key1806, -1), (key1268, -2), (key1651, -2), (key1837, -2), (key1261, 1), (key1268, 1), (key1536, 1), (key1768, 1), (key1651, 1), (key1809, 1)]

def rawRow2802 : Integer.Sparse Key := [(key1261, -1), (key1256, -1), (key1809, -1), (key1609, -1), (key1832, -1), (key1642, -1), (key1256, 2), (key1806, 2), (key1609, 2), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1), (key1265, -1), (key1256, -1), (key1765, -1), (key1531, -1), (key1806, -1), (key1648, -1), (key1268, -2), (key1837, -2), (key1651, -2), (key1268, 1), (key1261, 1), (key1768, 1), (key1536, 1), (key1809, 1), (key1651, 1)]

def rawRow2803 : Integer.Sparse Key := [(key1609, -1), (key1642, -1), (key1256, -1), (key1832, -1), (key1261, -1), (key1809, -1), (key1609, 2), (key1256, 2), (key1806, 2), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1), (key1531, -1), (key1648, -1), (key1256, -1), (key1806, -1), (key1265, -1), (key1765, -1), (key1651, -2), (key1268, -2), (key1837, -2), (key1536, 1), (key1651, 1), (key1261, 1), (key1809, 1), (key1268, 1), (key1768, 1)]

def rawRow2804 : Integer.Sparse Key := [(key1642, -1), (key1609, -1), (key1832, -1), (key1256, -1), (key1809, -1), (key1261, -1), (key1609, 2), (key1806, 2), (key1256, 2), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1), (key1648, -1), (key1531, -1), (key1806, -1), (key1256, -1), (key1765, -1), (key1265, -1), (key1651, -2), (key1837, -2), (key1268, -2), (key1651, 1), (key1536, 1), (key1809, 1), (key1261, 1), (key1768, 1), (key1268, 1)]

def rawRow2805 : Integer.Sparse Key := [(key1809, -1), (key1832, -1), (key1261, -1), (key1642, -1), (key1256, -1), (key1609, -1), (key1806, 2), (key1256, 2), (key1609, 2), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1), (key1765, -1), (key1806, -1), (key1265, -1), (key1648, -1), (key1256, -1), (key1531, -1), (key1837, -2), (key1268, -2), (key1651, -2), (key1768, 1), (key1809, 1), (key1268, 1), (key1651, 1), (key1261, 1), (key1536, 1)]

def rawRow2806 : Integer.Sparse Key := [(key1832, -1), (key1809, -1), (key1642, -1), (key1261, -1), (key1609, -1), (key1256, -1), (key1806, 2), (key1609, 2), (key1256, 2), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1), (key1806, -1), (key1765, -1), (key1648, -1), (key1265, -1), (key1531, -1), (key1256, -1), (key1837, -2), (key1651, -2), (key1268, -2), (key1809, 1), (key1768, 1), (key1651, 1), (key1268, 1), (key1536, 1), (key1261, 1)]

def rawRow2807 : Integer.Sparse Key := [(key1648, -1), (key1651, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1674, 2), (key1674, 2), (key1848, 2), (key1531, 1), (key1536, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1768, 1), (key1642, -1), (key1674, -1), (key1642, -1), (key1832, -1), (key1674, -1), (key1832, -1), (key1531, -2), (key1531, -2), (key1765, -2), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1648, 1), (key1806, 1)]

def rawRow2808 : Integer.Sparse Key := [(key1651, -1), (key1648, -1), (key1837, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1674, 2), (key1848, 2), (key1674, 2), (key1536, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1674, -1), (key1642, -1), (key1832, -1), (key1642, -1), (key1832, -1), (key1674, -1), (key1531, -2), (key1765, -2), (key1531, -2), (key1648, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1806, 1), (key1648, 1)]

def rawRow2809 : Integer.Sparse Key := [(key1837, -1), (key1837, -1), (key1651, -1), (key1651, -1), (key1648, -1), (key1648, -1), (key1848, 2), (key1674, 2), (key1674, 2), (key1768, 1), (key1768, 1), (key1536, 1), (key1536, 1), (key1531, 1), (key1531, 1), (key1832, -1), (key1832, -1), (key1674, -1), (key1674, -1), (key1642, -1), (key1642, -1), (key1765, -2), (key1531, -2), (key1531, -2), (key1806, 1), (key1806, 1), (key1648, 1), (key1648, 1), (key1609, 1), (key1609, 1)]

def rawRow2810 : Integer.Sparse Key := [(key1265, -1), (key1268, -1), (key1648, -1), (key1837, -1), (key1674, -1), (key1848, -1), (key1268, 2), (key1651, 2), (key1837, 2), (key1256, 1), (key1261, 1), (key1609, 1), (key1809, 1), (key1642, 1), (key1832, 1), (key1261, -1), (key1268, -1), (key1536, -1), (key1768, -1), (key1651, -1), (key1809, -1), (key1256, -2), (key1609, -2), (key1806, -2), (key1256, 1), (key1265, 1), (key1531, 1), (key1765, 1), (key1648, 1), (key1806, 1)]

def rawRow2811 : Integer.Sparse Key := [(key1268, -1), (key1265, -1), (key1837, -1), (key1648, -1), (key1848, -1), (key1674, -1), (key1268, 2), (key1837, 2), (key1651, 2), (key1261, 1), (key1256, 1), (key1809, 1), (key1609, 1), (key1832, 1), (key1642, 1), (key1268, -1), (key1261, -1), (key1768, -1), (key1536, -1), (key1809, -1), (key1651, -1), (key1256, -2), (key1806, -2), (key1609, -2), (key1265, 1), (key1256, 1), (key1765, 1), (key1531, 1), (key1806, 1), (key1648, 1)]

def rawRow2812 : Integer.Sparse Key := [(key1648, -1), (key1674, -1), (key1265, -1), (key1848, -1), (key1268, -1), (key1837, -1), (key1651, 2), (key1268, 2), (key1837, 2), (key1609, 1), (key1642, 1), (key1256, 1), (key1832, 1), (key1261, 1), (key1809, 1), (key1536, -1), (key1651, -1), (key1261, -1), (key1809, -1), (key1268, -1), (key1768, -1), (key1609, -2), (key1256, -2), (key1806, -2), (key1531, 1), (key1648, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1765, 1)]

def rawRow2813 : Integer.Sparse Key := [(key1674, -1), (key1648, -1), (key1848, -1), (key1265, -1), (key1837, -1), (key1268, -1), (key1651, 2), (key1837, 2), (key1268, 2), (key1642, 1), (key1609, 1), (key1832, 1), (key1256, 1), (key1809, 1), (key1261, 1), (key1651, -1), (key1536, -1), (key1809, -1), (key1261, -1), (key1768, -1), (key1268, -1), (key1609, -2), (key1806, -2), (key1256, -2), (key1648, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1765, 1), (key1265, 1)]

def rawRow2814 : Integer.Sparse Key := [(key1837, -1), (key1848, -1), (key1268, -1), (key1674, -1), (key1265, -1), (key1648, -1), (key1837, 2), (key1268, 2), (key1651, 2), (key1809, 1), (key1832, 1), (key1261, 1), (key1642, 1), (key1256, 1), (key1609, 1), (key1768, -1), (key1809, -1), (key1268, -1), (key1651, -1), (key1261, -1), (key1536, -1), (key1806, -2), (key1256, -2), (key1609, -2), (key1765, 1), (key1806, 1), (key1265, 1), (key1648, 1), (key1256, 1), (key1531, 1)]

def rawRow2815 : Integer.Sparse Key := [(key1848, -1), (key1837, -1), (key1674, -1), (key1268, -1), (key1648, -1), (key1265, -1), (key1837, 2), (key1651, 2), (key1268, 2), (key1832, 1), (key1809, 1), (key1642, 1), (key1261, 1), (key1609, 1), (key1256, 1), (key1809, -1), (key1768, -1), (key1651, -1), (key1268, -1), (key1536, -1), (key1261, -1), (key1806, -2), (key1609, -2), (key1256, -2), (key1806, 1), (key1765, 1), (key1648, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2816 : Integer.Sparse Key := [(key2428, -2), (key2428, -2), (key2444, -2), (key2430, 2), (key2430, 2), (key2444, 2), (key2496, 2), (key2496, 2), (key2510, 2), (key2510, -6), (key2574, -2), (key2574, -2), (key2577, -2), (key2577, 6)]

def rawRow2817 : Integer.Sparse Key := [(key2428, -2), (key2444, -2), (key2428, -2), (key2430, 2), (key2444, 2), (key2430, 2), (key2496, 2), (key2510, 2), (key2496, 2), (key2510, -6), (key2574, -2), (key2577, -2), (key2574, -2), (key2577, 6)]

def rawRow2818 : Integer.Sparse Key := [(key2444, -2), (key2428, -2), (key2428, -2), (key2444, 2), (key2430, 2), (key2430, 2), (key2510, 2), (key2496, 2), (key2496, 2), (key2510, -6), (key2577, -2), (key2574, -2), (key2574, -2), (key2577, 6)]

def rawRow2819 : Integer.Sparse Key := [(key2421, -2), (key2430, -2), (key2430, -2), (key2421, 2), (key2428, 2), (key2428, 2), (key2496, 2), (key2510, 2), (key2510, 2), (key2496, -6), (key2574, -2), (key2577, -2), (key2577, -2), (key2574, 6)]

def rawRow2820 : Integer.Sparse Key := [(key2430, -2), (key2421, -2), (key2430, -2), (key2428, 2), (key2421, 2), (key2428, 2), (key2510, 2), (key2496, 2), (key2510, 2), (key2496, -6), (key2577, -2), (key2574, -2), (key2577, -2), (key2574, 6)]

def rawRow2821 : Integer.Sparse Key := [(key2430, -2), (key2430, -2), (key2421, -2), (key2428, 2), (key2428, 2), (key2421, 2), (key2510, 2), (key2510, 2), (key2496, 2), (key2496, -6), (key2577, -2), (key2577, -2), (key2574, -2), (key2574, 6)]

def rawRow2822 : Integer.Sparse Key := [(key3132, -2), (key3132, -2), (key3145, -2), (key3140, 2), (key3140, 2), (key3148, 2), (key2428, 2), (key2428, 2), (key2444, 2), (key2577, -6), (key2430, -2), (key2430, -2), (key2444, -2), (key2510, 6)]

def rawRow2823 : Integer.Sparse Key := [(key3132, -2), (key3145, -2), (key3132, -2), (key3140, 2), (key3148, 2), (key3140, 2), (key2428, 2), (key2444, 2), (key2428, 2), (key2577, -6), (key2430, -2), (key2444, -2), (key2430, -2), (key2510, 6)]

def rawRow2824 : Integer.Sparse Key := [(key3145, -2), (key3132, -2), (key3132, -2), (key3148, 2), (key3140, 2), (key3140, 2), (key2444, 2), (key2428, 2), (key2428, 2), (key2577, -6), (key2444, -2), (key2430, -2), (key2430, -2), (key2510, 6)]

def rawRow2825 : Integer.Sparse Key := [(key3036, -2), (key3042, -2), (key3140, -2), (key3036, 2), (key3040, 2), (key3132, 2), (key3040, 2), (key3044, 2), (key3148, 2), (key2428, -6), (key2430, -2), (key2444, -2), (key2510, -2), (key2430, 6)]

def rawRow2826 : Integer.Sparse Key := [(key3042, -2), (key3036, -2), (key3140, -2), (key3040, 2), (key3036, 2), (key3132, 2), (key3044, 2), (key3040, 2), (key3148, 2), (key2428, -6), (key2444, -2), (key2430, -2), (key2510, -2), (key2430, 6)]

def rawRow2827 : Integer.Sparse Key := [(key3036, -2), (key3140, -2), (key3042, -2), (key3036, 2), (key3132, 2), (key3040, 2), (key3040, 2), (key3148, 2), (key3044, 2), (key2428, -6), (key2430, -2), (key2510, -2), (key2444, -2), (key2430, 6)]

def rawRow2828 : Integer.Sparse Key := [(key3140, -2), (key3036, -2), (key3042, -2), (key3132, 2), (key3036, 2), (key3040, 2), (key3148, 2), (key3040, 2), (key3044, 2), (key2428, -6), (key2510, -2), (key2430, -2), (key2444, -2), (key2430, 6)]

def rawRow2829 : Integer.Sparse Key := [(key3042, -2), (key3140, -2), (key3036, -2), (key3040, 2), (key3132, 2), (key3036, 2), (key3044, 2), (key3148, 2), (key3040, 2), (key2428, -6), (key2444, -2), (key2510, -2), (key2430, -2), (key2430, 6)]

def rawRow2830 : Integer.Sparse Key := [(key3140, -2), (key3042, -2), (key3036, -2), (key3132, 2), (key3040, 2), (key3036, 2), (key3148, 2), (key3044, 2), (key3040, 2), (key2428, -6), (key2510, -2), (key2444, -2), (key2430, -2), (key2430, 6)]

def rawRow2831 : Integer.Sparse Key := [(key3132, -2), (key3145, -2), (key3145, -2), (key3140, 2), (key3148, 2), (key3148, 2), (key3036, 2), (key3042, 2), (key3042, 2), (key3140, -6), (key2421, -2), (key2428, -2), (key2428, -2), (key2496, 6)]

def rawRow2832 : Integer.Sparse Key := [(key3145, -2), (key3132, -2), (key3145, -2), (key3148, 2), (key3140, 2), (key3148, 2), (key3042, 2), (key3036, 2), (key3042, 2), (key3140, -6), (key2428, -2), (key2421, -2), (key2428, -2), (key2496, 6)]

def rawRow2833 : Integer.Sparse Key := [(key3145, -2), (key3145, -2), (key3132, -2), (key3148, 2), (key3148, 2), (key3140, 2), (key3042, 2), (key3042, 2), (key3036, 2), (key3140, -6), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, 6)]

def rawRow2834 : Integer.Sparse Key := [(key3040, -2), (key3044, -2), (key3148, -2), (key3042, 2), (key3044, 2), (key3145, 2), (key3036, 2), (key3042, 2), (key3140, 2), (key3042, -6), (key2421, -2), (key2428, -2), (key2496, -2), (key2428, 6)]

def rawRow2835 : Integer.Sparse Key := [(key3044, -2), (key3040, -2), (key3148, -2), (key3044, 2), (key3042, 2), (key3145, 2), (key3042, 2), (key3036, 2), (key3140, 2), (key3042, -6), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, 6)]

def rawRow2836 : Integer.Sparse Key := [(key3040, -2), (key3148, -2), (key3044, -2), (key3042, 2), (key3145, 2), (key3044, 2), (key3036, 2), (key3140, 2), (key3042, 2), (key3042, -6), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, 6)]

def rawRow2837 : Integer.Sparse Key := [(key3148, -2), (key3040, -2), (key3044, -2), (key3145, 2), (key3042, 2), (key3044, 2), (key3140, 2), (key3036, 2), (key3042, 2), (key3042, -6), (key2496, -2), (key2421, -2), (key2428, -2), (key2428, 6)]

def rawRow2838 : Integer.Sparse Key := [(key3044, -2), (key3148, -2), (key3040, -2), (key3044, 2), (key3145, 2), (key3042, 2), (key3042, 2), (key3140, 2), (key3036, 2), (key3042, -6), (key2428, -2), (key2496, -2), (key2421, -2), (key2428, 6)]

def rawRow2839 : Integer.Sparse Key := [(key3148, -2), (key3044, -2), (key3040, -2), (key3145, 2), (key3044, 2), (key3042, 2), (key3140, 2), (key3042, 2), (key3036, 2), (key3042, -6), (key2496, -2), (key2428, -2), (key2421, -2), (key2428, 6)]

def rawRow2840 : Integer.Sparse Key := [(key1256, -2), (key1256, -2), (key1261, -2), (key1256, 1), (key1256, 1), (key1265, 1), (key1265, 1), (key1268, 1), (key1268, 1), (key1531, 2), (key1531, 2), (key1536, 2), (key1531, -1), (key1531, -1), (key1765, -1), (key1765, -1), (key1768, -1), (key1768, -1), (key1609, -1), (key1609, -1), (key1648, -1), (key1648, -1), (key1651, -1), (key1651, -1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1)]

def rawRow2841 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1256, -2), (key1265, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1531, 2), (key1536, 2), (key1531, 2), (key1765, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1648, -1), (key1651, -1), (key1609, -1), (key1651, -1), (key1609, -1), (key1648, -1), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1)]

def rawRow2842 : Integer.Sparse Key := [(key1261, -2), (key1256, -2), (key1256, -2), (key1268, 1), (key1265, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1256, 1), (key1536, 2), (key1531, 2), (key1531, 2), (key1768, -1), (key1765, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1531, -1), (key1651, -1), (key1648, -1), (key1651, -1), (key1609, -1), (key1648, -1), (key1609, -1), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1)]

def rawRow2843 : Integer.Sparse Key := [(key1265, -2), (key1268, -2), (key1268, -2), (key1256, 1), (key1261, 1), (key1256, 1), (key1268, 1), (key1261, 1), (key1268, 1), (key1765, 2), (key1768, 2), (key1768, 2), (key1531, -1), (key1536, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1768, -1), (key1806, -1), (key1809, -1), (key1806, -1), (key1837, -1), (key1809, -1), (key1837, -1), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1)]

def rawRow2844 : Integer.Sparse Key := [(key1268, -2), (key1265, -2), (key1268, -2), (key1261, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1261, 1), (key1768, 2), (key1765, 2), (key1768, 2), (key1536, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1809, -1), (key1806, -1), (key1837, -1), (key1806, -1), (key1837, -1), (key1809, -1), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1)]

def rawRow2845 : Integer.Sparse Key := [(key1268, -2), (key1268, -2), (key1265, -2), (key1268, 1), (key1268, 1), (key1261, 1), (key1261, 1), (key1256, 1), (key1256, 1), (key1768, 2), (key1768, 2), (key1765, 2), (key1768, -1), (key1768, -1), (key1536, -1), (key1536, -1), (key1531, -1), (key1531, -1), (key1837, -1), (key1837, -1), (key1809, -1), (key1809, -1), (key1806, -1), (key1806, -1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1)]

def rawRow2846 : Integer.Sparse Key := [(key1531, -2), (key1531, -2), (key1536, -2), (key1609, 1), (key1609, 1), (key1648, 1), (key1648, 1), (key1651, 1), (key1651, 1), (key1256, 2), (key1256, 2), (key1261, 2), (key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1809, -1), (key1809, -1), (key1256, -1), (key1256, -1), (key1265, -1), (key1265, -1), (key1268, -1), (key1268, -1), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1)]

def rawRow2847 : Integer.Sparse Key := [(key1531, -2), (key1536, -2), (key1531, -2), (key1648, 1), (key1651, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1256, 2), (key1261, 2), (key1256, 2), (key1806, -1), (key1809, -1), (key1609, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1265, -1), (key1268, -1), (key1256, -1), (key1268, -1), (key1256, -1), (key1265, -1), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1)]

def rawRow2848 : Integer.Sparse Key := [(key1536, -2), (key1531, -2), (key1531, -2), (key1651, 1), (key1648, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1261, 2), (key1256, 2), (key1256, 2), (key1809, -1), (key1806, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1268, -1), (key1265, -1), (key1268, -1), (key1256, -1), (key1265, -1), (key1256, -1), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1)]

def rawRow2849 : Integer.Sparse Key := [(key1648, -2), (key1651, -2), (key1674, -2), (key1531, 1), (key1536, 1), (key1609, 1), (key1651, 1), (key1642, 1), (key1674, 1), (key1806, 2), (key1809, 2), (key1832, 2), (key1256, -1), (key1261, -1), (key1609, -1), (key1809, -1), (key1642, -1), (key1832, -1), (key1765, -1), (key1768, -1), (key1806, -1), (key1837, -1), (key1832, -1), (key1848, -1), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1)]

def rawRow2850 : Integer.Sparse Key := [(key1651, -2), (key1648, -2), (key1674, -2), (key1536, 1), (key1531, 1), (key1651, 1), (key1609, 1), (key1674, 1), (key1642, 1), (key1809, 2), (key1806, 2), (key1832, 2), (key1261, -1), (key1256, -1), (key1809, -1), (key1609, -1), (key1832, -1), (key1642, -1), (key1768, -1), (key1765, -1), (key1837, -1), (key1806, -1), (key1848, -1), (key1832, -1), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1)]

def rawRow2851 : Integer.Sparse Key := [(key1648, -2), (key1674, -2), (key1651, -2), (key1609, 1), (key1642, 1), (key1531, 1), (key1674, 1), (key1536, 1), (key1651, 1), (key1806, 2), (key1832, 2), (key1809, 2), (key1609, -1), (key1642, -1), (key1256, -1), (key1832, -1), (key1261, -1), (key1809, -1), (key1806, -1), (key1832, -1), (key1765, -1), (key1848, -1), (key1768, -1), (key1837, -1), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1)]

def rawRow2852 : Integer.Sparse Key := [(key1674, -2), (key1648, -2), (key1651, -2), (key1642, 1), (key1609, 1), (key1674, 1), (key1531, 1), (key1651, 1), (key1536, 1), (key1832, 2), (key1806, 2), (key1809, 2), (key1642, -1), (key1609, -1), (key1832, -1), (key1256, -1), (key1809, -1), (key1261, -1), (key1832, -1), (key1806, -1), (key1848, -1), (key1765, -1), (key1837, -1), (key1768, -1), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1)]

def rawRow2853 : Integer.Sparse Key := [(key1651, -2), (key1674, -2), (key1648, -2), (key1651, 1), (key1674, 1), (key1536, 1), (key1642, 1), (key1531, 1), (key1609, 1), (key1809, 2), (key1832, 2), (key1806, 2), (key1809, -1), (key1832, -1), (key1261, -1), (key1642, -1), (key1256, -1), (key1609, -1), (key1837, -1), (key1848, -1), (key1768, -1), (key1832, -1), (key1765, -1), (key1806, -1), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1)]

def rawRow2854 : Integer.Sparse Key := [(key1674, -2), (key1651, -2), (key1648, -2), (key1674, 1), (key1651, 1), (key1642, 1), (key1536, 1), (key1609, 1), (key1531, 1), (key1832, 2), (key1809, 2), (key1806, 2), (key1832, -1), (key1809, -1), (key1642, -1), (key1261, -1), (key1609, -1), (key1256, -1), (key1848, -1), (key1837, -1), (key1832, -1), (key1768, -1), (key1806, -1), (key1765, -1), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1)]

def rawRow2855 : Integer.Sparse Key := [(key1765, -2), (key1768, -2), (key1768, -2), (key1806, 1), (key1809, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1265, 2), (key1268, 2), (key1268, 2), (key1648, -1), (key1651, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1256, -1), (key1261, -1), (key1256, -1), (key1268, -1), (key1261, -1), (key1268, -1), (key1531, 1), (key1536, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1768, 1)]

def rawRow2856 : Integer.Sparse Key := [(key1768, -2), (key1765, -2), (key1768, -2), (key1809, 1), (key1806, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1268, 2), (key1265, 2), (key1268, 2), (key1651, -1), (key1648, -1), (key1837, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1261, -1), (key1256, -1), (key1268, -1), (key1256, -1), (key1268, -1), (key1261, -1), (key1536, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1536, 1)]

def rawRow2857 : Integer.Sparse Key := [(key1768, -2), (key1768, -2), (key1765, -2), (key1837, 1), (key1837, 1), (key1809, 1), (key1809, 1), (key1806, 1), (key1806, 1), (key1268, 2), (key1268, 2), (key1265, 2), (key1837, -1), (key1837, -1), (key1651, -1), (key1651, -1), (key1648, -1), (key1648, -1), (key1268, -1), (key1268, -1), (key1261, -1), (key1261, -1), (key1256, -1), (key1256, -1), (key1768, 1), (key1768, 1), (key1536, 1), (key1536, 1), (key1531, 1), (key1531, 1)]

def rawRow2858 : Integer.Sparse Key := [(key1806, -2), (key1809, -2), (key1832, -2), (key1765, 1), (key1768, 1), (key1806, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1648, 2), (key1651, 2), (key1674, 2), (key1265, -1), (key1268, -1), (key1648, -1), (key1837, -1), (key1674, -1), (key1848, -1), (key1531, -1), (key1536, -1), (key1609, -1), (key1651, -1), (key1642, -1), (key1674, -1), (key1256, 1), (key1261, 1), (key1609, 1), (key1809, 1), (key1642, 1), (key1832, 1)]

def rawRow2859 : Integer.Sparse Key := [(key1809, -2), (key1806, -2), (key1832, -2), (key1768, 1), (key1765, 1), (key1837, 1), (key1806, 1), (key1848, 1), (key1832, 1), (key1651, 2), (key1648, 2), (key1674, 2), (key1268, -1), (key1265, -1), (key1837, -1), (key1648, -1), (key1848, -1), (key1674, -1), (key1536, -1), (key1531, -1), (key1651, -1), (key1609, -1), (key1674, -1), (key1642, -1), (key1261, 1), (key1256, 1), (key1809, 1), (key1609, 1), (key1832, 1), (key1642, 1)]

def rawRow2860 : Integer.Sparse Key := [(key1806, -2), (key1832, -2), (key1809, -2), (key1806, 1), (key1832, 1), (key1765, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1648, 2), (key1674, 2), (key1651, 2), (key1648, -1), (key1674, -1), (key1265, -1), (key1848, -1), (key1268, -1), (key1837, -1), (key1609, -1), (key1642, -1), (key1531, -1), (key1674, -1), (key1536, -1), (key1651, -1), (key1609, 1), (key1642, 1), (key1256, 1), (key1832, 1), (key1261, 1), (key1809, 1)]

def rawRow2861 : Integer.Sparse Key := [(key1832, -2), (key1806, -2), (key1809, -2), (key1832, 1), (key1806, 1), (key1848, 1), (key1765, 1), (key1837, 1), (key1768, 1), (key1674, 2), (key1648, 2), (key1651, 2), (key1674, -1), (key1648, -1), (key1848, -1), (key1265, -1), (key1837, -1), (key1268, -1), (key1642, -1), (key1609, -1), (key1674, -1), (key1531, -1), (key1651, -1), (key1536, -1), (key1642, 1), (key1609, 1), (key1832, 1), (key1256, 1), (key1809, 1), (key1261, 1)]

def rawRow2862 : Integer.Sparse Key := [(key1809, -2), (key1832, -2), (key1806, -2), (key1837, 1), (key1848, 1), (key1768, 1), (key1832, 1), (key1765, 1), (key1806, 1), (key1651, 2), (key1674, 2), (key1648, 2), (key1837, -1), (key1848, -1), (key1268, -1), (key1674, -1), (key1265, -1), (key1648, -1), (key1651, -1), (key1674, -1), (key1536, -1), (key1642, -1), (key1531, -1), (key1609, -1), (key1809, 1), (key1832, 1), (key1261, 1), (key1642, 1), (key1256, 1), (key1609, 1)]

def rawRow2863 : Integer.Sparse Key := [(key1832, -2), (key1809, -2), (key1806, -2), (key1848, 1), (key1837, 1), (key1832, 1), (key1768, 1), (key1806, 1), (key1765, 1), (key1674, 2), (key1651, 2), (key1648, 2), (key1848, -1), (key1837, -1), (key1674, -1), (key1268, -1), (key1648, -1), (key1265, -1), (key1674, -1), (key1651, -1), (key1642, -1), (key1536, -1), (key1609, -1), (key1531, -1), (key1832, 1), (key1809, 1), (key1642, 1), (key1261, 1), (key1609, 1), (key1256, 1)]

def rawRow2864 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key983, -2), (key983, 6), (key1090, 2), (key1090, 2), (key1097, 2), (key1097, -2), (key1182, -2), (key1182, -2), (key1168, -6), (key1168, 2), (key1219, 2), (key1219, 2)]

def rawRow2865 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key976, -2), (key983, 6), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, -2), (key1097, -2), (key1182, -2), (key1168, -6), (key1219, 2), (key1168, 2), (key1219, 2)]

def rawRow2866 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key976, -2), (key983, 6), (key1097, 2), (key1090, 2), (key1090, 2), (key1182, -2), (key1182, -2), (key1097, -2), (key1168, -6), (key1219, 2), (key1219, 2), (key1168, 2)]

def rawRow2867 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key983, -2), (key976, 6), (key1180, 2), (key1182, 2), (key1182, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1219, -6), (key1168, 2), (key1168, 2), (key1219, 2)]

def rawRow2868 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key983, -2), (key976, 6), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1219, -6), (key1168, 2), (key1219, 2), (key1168, 2)]

def rawRow2869 : Integer.Sparse Key := [(key983, -2), (key983, -2), (key976, -2), (key976, 6), (key1182, 2), (key1182, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1219, -6), (key1219, 2), (key1168, 2), (key1168, 2)]

def rawRow2870 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1097, -2), (key1168, 6), (key976, 2), (key976, 2), (key983, 2), (key1168, -2), (key1219, -2), (key1219, -2), (key983, -6), (key1097, 2), (key1182, 2), (key1182, 2)]

def rawRow2871 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1090, -2), (key1168, 6), (key976, 2), (key983, 2), (key976, 2), (key1219, -2), (key1168, -2), (key1219, -2), (key983, -6), (key1182, 2), (key1097, 2), (key1182, 2)]

def rawRow2872 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1090, -2), (key1168, 6), (key983, 2), (key976, 2), (key976, 2), (key1219, -2), (key1219, -2), (key1168, -2), (key983, -6), (key1182, 2), (key1182, 2), (key1097, 2)]

def rawRow2873 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1168, -2), (key1090, 6), (key1180, 2), (key1182, 2), (key1219, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1182, -6), (key983, 2), (key1097, 2), (key1182, 2)]

def rawRow2874 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1168, -2), (key1090, 6), (key1182, 2), (key1180, 2), (key1219, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1182, -6), (key983, 2), (key1182, 2), (key1097, 2)]

def rawRow2875 : Integer.Sparse Key := [(key1090, -2), (key1168, -2), (key1097, -2), (key1090, 6), (key1180, 2), (key1219, 2), (key1182, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1182, -6), (key1097, 2), (key983, 2), (key1182, 2)]

def rawRow2876 : Integer.Sparse Key := [(key1168, -2), (key1090, -2), (key1097, -2), (key1090, 6), (key1219, 2), (key1180, 2), (key1182, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1182, -6), (key1097, 2), (key1182, 2), (key983, 2)]

def rawRow2877 : Integer.Sparse Key := [(key1097, -2), (key1168, -2), (key1090, -2), (key1090, 6), (key1182, 2), (key1219, 2), (key1180, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1182, -6), (key1182, 2), (key983, 2), (key1097, 2)]

def rawRow2878 : Integer.Sparse Key := [(key1168, -2), (key1097, -2), (key1090, -2), (key1090, 6), (key1219, 2), (key1182, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1182, -6), (key1182, 2), (key1097, 2), (key983, 2)]

def rawRow2879 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1182, -2), (key1219, 6), (key976, 2), (key983, 2), (key983, 2), (key1168, -2), (key1168, -2), (key1219, -2), (key976, -6), (key1090, 2), (key1090, 2), (key1180, 2)]

def rawRow2880 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1182, -2), (key1219, 6), (key983, 2), (key976, 2), (key983, 2), (key1168, -2), (key1219, -2), (key1168, -2), (key976, -6), (key1090, 2), (key1180, 2), (key1090, 2)]

def rawRow2881 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1180, -2), (key1219, 6), (key983, 2), (key983, 2), (key976, 2), (key1219, -2), (key1168, -2), (key1168, -2), (key976, -6), (key1180, 2), (key1090, 2), (key1090, 2)]

def rawRow2882 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1219, -2), (key1182, 6), (key1090, 2), (key1097, 2), (key1168, 2), (key983, -2), (key1097, -2), (key1182, -2), (key1090, -6), (key976, 2), (key1090, 2), (key1180, 2)]

def rawRow2883 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1219, -2), (key1182, 6), (key1097, 2), (key1090, 2), (key1168, 2), (key983, -2), (key1182, -2), (key1097, -2), (key1090, -6), (key976, 2), (key1180, 2), (key1090, 2)]

def rawRow2884 : Integer.Sparse Key := [(key1180, -2), (key1219, -2), (key1182, -2), (key1182, 6), (key1090, 2), (key1168, 2), (key1097, 2), (key1097, -2), (key983, -2), (key1182, -2), (key1090, -6), (key1090, 2), (key976, 2), (key1180, 2)]

def rawRow2885 : Integer.Sparse Key := [(key1219, -2), (key1180, -2), (key1182, -2), (key1182, 6), (key1168, 2), (key1090, 2), (key1097, 2), (key1097, -2), (key1182, -2), (key983, -2), (key1090, -6), (key1090, 2), (key1180, 2), (key976, 2)]

def rawRow2886 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1180, -2), (key1182, 6), (key1097, 2), (key1168, 2), (key1090, 2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, -6), (key1180, 2), (key976, 2), (key1090, 2)]

def rawRow2887 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1180, -2), (key1182, 6), (key1168, 2), (key1097, 2), (key1090, 2), (key1182, -2), (key1097, -2), (key983, -2), (key1090, -6), (key1180, 2), (key1090, 2), (key976, 2)]

def rawRow2888 : Integer.Sparse Key := [(key2379, -2), (key2393, -2), (key2393, -2), (key2382, 1), (key2382, 1), (key2393, 1), (key2393, 1), (key2395, 1), (key2395, 1), (key2473, 2), (key2483, 2), (key2483, 2), (key2483, -1), (key2483, -1), (key2507, -1), (key2507, -1), (key2526, -1), (key2526, -1), (key2539, -1), (key2539, -1), (key2544, -1), (key2544, -1), (key2545, -1), (key2545, -1), (key2544, 1), (key2544, 1), (key2555, 1), (key2555, 1), (key2565, 1), (key2565, 1)]

def rawRow2889 : Integer.Sparse Key := [(key2393, -2), (key2379, -2), (key2393, -2), (key2393, 1), (key2395, 1), (key2382, 1), (key2395, 1), (key2382, 1), (key2393, 1), (key2483, 2), (key2473, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2483, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2544, -1), (key2545, -1), (key2539, -1), (key2545, -1), (key2539, -1), (key2544, -1), (key2555, 1), (key2565, 1), (key2544, 1), (key2565, 1), (key2544, 1), (key2555, 1)]

def rawRow2890 : Integer.Sparse Key := [(key2393, -2), (key2393, -2), (key2379, -2), (key2395, 1), (key2393, 1), (key2395, 1), (key2382, 1), (key2393, 1), (key2382, 1), (key2483, 2), (key2483, 2), (key2473, 2), (key2526, -1), (key2507, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2483, -1), (key2545, -1), (key2544, -1), (key2545, -1), (key2539, -1), (key2544, -1), (key2539, -1), (key2565, 1), (key2555, 1), (key2565, 1), (key2544, 1), (key2555, 1), (key2544, 1)]

def rawRow2891 : Integer.Sparse Key := [(key2382, -2), (key2382, -2), (key2395, -2), (key2379, 1), (key2382, 1), (key2379, 1), (key2393, 1), (key2382, 1), (key2393, 1), (key2507, 2), (key2507, 2), (key2526, 2), (key2473, -1), (key2483, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2507, -1), (key2555, -1), (key2557, -1), (key2555, -1), (key2565, -1), (key2557, -1), (key2565, -1), (key2539, 1), (key2545, 1), (key2539, 1), (key2557, 1), (key2545, 1), (key2557, 1)]

def rawRow2892 : Integer.Sparse Key := [(key2382, -2), (key2395, -2), (key2382, -2), (key2382, 1), (key2379, 1), (key2393, 1), (key2379, 1), (key2393, 1), (key2382, 1), (key2507, 2), (key2526, 2), (key2507, 2), (key2483, -1), (key2473, -1), (key2507, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2557, -1), (key2555, -1), (key2565, -1), (key2555, -1), (key2565, -1), (key2557, -1), (key2545, 1), (key2539, 1), (key2557, 1), (key2539, 1), (key2557, 1), (key2545, 1)]

def rawRow2893 : Integer.Sparse Key := [(key2395, -2), (key2382, -2), (key2382, -2), (key2393, 1), (key2393, 1), (key2382, 1), (key2382, 1), (key2379, 1), (key2379, 1), (key2526, 2), (key2507, 2), (key2507, 2), (key2507, -1), (key2507, -1), (key2483, -1), (key2483, -1), (key2473, -1), (key2473, -1), (key2565, -1), (key2565, -1), (key2557, -1), (key2557, -1), (key2555, -1), (key2555, -1), (key2557, 1), (key2557, 1), (key2545, 1), (key2545, 1), (key2539, 1), (key2539, 1)]

def rawRow2894 : Integer.Sparse Key := [(key2848, -2), (key2891, -2), (key2891, -2), (key2882, 1), (key2882, 1), (key2912, 1), (key2912, 1), (key2914, 1), (key2914, 1), (key2379, 2), (key2393, 2), (key2393, 2), (key2544, -1), (key2544, -1), (key2555, -1), (key2555, -1), (key2565, -1), (key2565, -1), (key2382, -1), (key2382, -1), (key2393, -1), (key2393, -1), (key2395, -1), (key2395, -1), (key2483, 1), (key2483, 1), (key2507, 1), (key2507, 1), (key2526, 1), (key2526, 1)]

def rawRow2895 : Integer.Sparse Key := [(key2891, -2), (key2848, -2), (key2891, -2), (key2912, 1), (key2914, 1), (key2882, 1), (key2914, 1), (key2882, 1), (key2912, 1), (key2393, 2), (key2379, 2), (key2393, 2), (key2555, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2395, -1), (key2382, -1), (key2395, -1), (key2382, -1), (key2393, -1), (key2507, 1), (key2526, 1), (key2483, 1), (key2526, 1), (key2483, 1), (key2507, 1)]

def rawRow2896 : Integer.Sparse Key := [(key2891, -2), (key2891, -2), (key2848, -2), (key2914, 1), (key2912, 1), (key2914, 1), (key2882, 1), (key2912, 1), (key2882, 1), (key2393, 2), (key2393, 2), (key2379, 2), (key2565, -1), (key2555, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2544, -1), (key2395, -1), (key2393, -1), (key2395, -1), (key2382, -1), (key2393, -1), (key2382, -1), (key2526, 1), (key2507, 1), (key2526, 1), (key2483, 1), (key2507, 1), (key2483, 1)]

def rawRow2897 : Integer.Sparse Key := [(key2774, -2), (key2882, -2), (key2914, -2), (key2771, 1), (key2774, 1), (key2848, 1), (key2891, 1), (key2882, 1), (key2912, 1), (key2933, 2), (key2991, 2), (key3003, 2), (key2379, -1), (key2393, -1), (key2407, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2441, -1), (key2445, -1), (key2507, -1), (key2526, -1), (key2557, -1), (key2565, -1), (key2382, 1), (key2395, 1), (key2410, 1), (key2445, 1), (key2545, 1), (key2557, 1)]

def rawRow2898 : Integer.Sparse Key := [(key2774, -2), (key2914, -2), (key2882, -2), (key2774, 1), (key2771, 1), (key2891, 1), (key2848, 1), (key2912, 1), (key2882, 1), (key2933, 2), (key3003, 2), (key2991, 2), (key2393, -1), (key2379, -1), (key2441, -1), (key2407, -1), (key2555, -1), (key2544, -1), (key2445, -1), (key2441, -1), (key2526, -1), (key2507, -1), (key2565, -1), (key2557, -1), (key2395, 1), (key2382, 1), (key2445, 1), (key2410, 1), (key2557, 1), (key2545, 1)]

def rawRow2899 : Integer.Sparse Key := [(key2882, -2), (key2774, -2), (key2914, -2), (key2848, 1), (key2882, 1), (key2771, 1), (key2912, 1), (key2774, 1), (key2891, 1), (key2991, 2), (key2933, 2), (key3003, 2), (key2771, -1), (key2912, -1), (key2592, -1), (key2991, -1), (key2393, -1), (key2441, -1), (key2507, -1), (key2557, -1), (key2441, -1), (key2565, -1), (key2445, -1), (key2526, -1), (key2410, 1), (key2545, 1), (key2382, 1), (key2557, 1), (key2395, 1), (key2445, 1)]

def rawRow2900 : Integer.Sparse Key := [(key2882, -2), (key2914, -2), (key2774, -2), (key2882, 1), (key2848, 1), (key2912, 1), (key2771, 1), (key2891, 1), (key2774, 1), (key2991, 2), (key3003, 2), (key2933, 2), (key2912, -1), (key2771, -1), (key2991, -1), (key2592, -1), (key2441, -1), (key2393, -1), (key2557, -1), (key2507, -1), (key2565, -1), (key2441, -1), (key2526, -1), (key2445, -1), (key2545, 1), (key2410, 1), (key2557, 1), (key2382, 1), (key2445, 1), (key2395, 1)]

def rawRow2901 : Integer.Sparse Key := [(key2914, -2), (key2774, -2), (key2882, -2), (key2891, 1), (key2912, 1), (key2774, 1), (key2882, 1), (key2771, 1), (key2848, 1), (key3003, 2), (key2933, 2), (key2991, 2), (key2933, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2379, -1), (key2407, -1), (key2526, -1), (key2565, -1), (key2445, -1), (key2557, -1), (key2441, -1), (key2507, -1), (key2445, 1), (key2557, 1), (key2395, 1), (key2545, 1), (key2382, 1), (key2410, 1)]

def rawRow2902 : Integer.Sparse Key := [(key2914, -2), (key2882, -2), (key2774, -2), (key2912, 1), (key2891, 1), (key2882, 1), (key2774, 1), (key2848, 1), (key2771, 1), (key3003, 2), (key2991, 2), (key2933, 2), (key2991, -1), (key2933, -1), (key2912, -1), (key2602, -1), (key2771, -1), (key2592, -1), (key2565, -1), (key2526, -1), (key2557, -1), (key2445, -1), (key2507, -1), (key2441, -1), (key2557, 1), (key2445, 1), (key2545, 1), (key2395, 1), (key2410, 1), (key2382, 1)]

def rawRow2903 : Integer.Sparse Key := [(key2970, -2), (key2970, -2), (key2996, -2), (key2991, 1), (key2993, 1), (key2991, 1), (key3003, 1), (key2993, 1), (key3003, 1), (key2595, 2), (key2595, 2), (key2603, 2), (key2882, -1), (key2914, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2993, -1), (key2379, -1), (key2382, -1), (key2379, -1), (key2393, -1), (key2382, -1), (key2393, -1), (key2473, 1), (key2483, 1), (key2473, 1), (key2507, 1), (key2483, 1), (key2507, 1)]

def rawRow2904 : Integer.Sparse Key := [(key2970, -2), (key2996, -2), (key2970, -2), (key2993, 1), (key2991, 1), (key3003, 1), (key2991, 1), (key3003, 1), (key2993, 1), (key2595, 2), (key2603, 2), (key2595, 2), (key2914, -1), (key2882, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2382, -1), (key2379, -1), (key2393, -1), (key2379, -1), (key2393, -1), (key2382, -1), (key2483, 1), (key2473, 1), (key2507, 1), (key2473, 1), (key2507, 1), (key2483, 1)]

def rawRow2905 : Integer.Sparse Key := [(key2996, -2), (key2970, -2), (key2970, -2), (key3003, 1), (key3003, 1), (key2993, 1), (key2993, 1), (key2991, 1), (key2991, 1), (key2603, 2), (key2595, 2), (key2595, 2), (key2993, -1), (key2993, -1), (key2914, -1), (key2914, -1), (key2882, -1), (key2882, -1), (key2393, -1), (key2393, -1), (key2382, -1), (key2382, -1), (key2379, -1), (key2379, -1), (key2507, 1), (key2507, 1), (key2483, 1), (key2483, 1), (key2473, 1), (key2473, 1)]

def rawRow2906 : Integer.Sparse Key := [(key2933, -2), (key2991, -2), (key3003, -2), (key2933, 1), (key2934, 1), (key2970, 1), (key2996, 1), (key2993, 1), (key3003, 1), (key2774, 2), (key2882, 2), (key2914, 2), (key2595, -1), (key2603, -1), (key2774, -1), (key2934, -1), (key2914, -1), (key2993, -1), (key2771, -1), (key2774, -1), (key2848, -1), (key2891, -1), (key2882, -1), (key2912, -1), (key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1)]

def rawRow2907 : Integer.Sparse Key := [(key2933, -2), (key3003, -2), (key2991, -2), (key2934, 1), (key2933, 1), (key2996, 1), (key2970, 1), (key3003, 1), (key2993, 1), (key2774, 2), (key2914, 2), (key2882, 2), (key2603, -1), (key2595, -1), (key2934, -1), (key2774, -1), (key2993, -1), (key2914, -1), (key2774, -1), (key2771, -1), (key2891, -1), (key2848, -1), (key2912, -1), (key2882, -1), (key2393, 1), (key2379, 1), (key2441, 1), (key2407, 1), (key2555, 1), (key2544, 1)]

def rawRow2908 : Integer.Sparse Key := [(key2991, -2), (key2933, -2), (key3003, -2), (key2970, 1), (key2993, 1), (key2933, 1), (key3003, 1), (key2934, 1), (key2996, 1), (key2882, 2), (key2774, 2), (key2914, 2), (key2774, -1), (key2914, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2848, -1), (key2882, -1), (key2771, -1), (key2912, -1), (key2774, -1), (key2891, -1), (key2771, 1), (key2912, 1), (key2592, 1), (key2991, 1), (key2393, 1), (key2441, 1)]

def rawRow2909 : Integer.Sparse Key := [(key2991, -2), (key3003, -2), (key2933, -2), (key2993, 1), (key2970, 1), (key3003, 1), (key2933, 1), (key2996, 1), (key2934, 1), (key2882, 2), (key2914, 2), (key2774, 2), (key2914, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2934, -1), (key2603, -1), (key2882, -1), (key2848, -1), (key2912, -1), (key2771, -1), (key2891, -1), (key2774, -1), (key2912, 1), (key2771, 1), (key2991, 1), (key2592, 1), (key2441, 1), (key2393, 1)]

def rawRow2910 : Integer.Sparse Key := [(key3003, -2), (key2933, -2), (key2991, -2), (key2996, 1), (key3003, 1), (key2934, 1), (key2993, 1), (key2933, 1), (key2970, 1), (key2914, 2), (key2774, 2), (key2882, 2), (key2934, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2595, -1), (key2774, -1), (key2891, -1), (key2912, -1), (key2774, -1), (key2882, -1), (key2771, -1), (key2848, -1), (key2933, 1), (key2991, 1), (key2602, 1), (key2912, 1), (key2379, 1), (key2407, 1)]

def rawRow2911 : Integer.Sparse Key := [(key3003, -2), (key2991, -2), (key2933, -2), (key3003, 1), (key2996, 1), (key2993, 1), (key2934, 1), (key2970, 1), (key2933, 1), (key2914, 2), (key2882, 2), (key2774, 2), (key2993, -1), (key2934, -1), (key2914, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2912, -1), (key2891, -1), (key2882, -1), (key2774, -1), (key2848, -1), (key2771, -1), (key2991, 1), (key2933, 1), (key2912, 1), (key2602, 1), (key2771, 1), (key2592, 1)]

def rawRow2912 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, -2), (key2366, 6), (key2456, 2), (key2456, 2), (key2461, 2), (key2461, -2), (key2523, -2), (key2523, -2), (key2567, -6), (key2567, 2), (key2579, 2), (key2579, 2)]

def rawRow2913 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2361, -2), (key2366, 6), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, -2), (key2461, -2), (key2523, -2), (key2567, -6), (key2579, 2), (key2567, 2), (key2579, 2)]

def rawRow2914 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2361, -2), (key2366, 6), (key2461, 2), (key2456, 2), (key2456, 2), (key2523, -2), (key2523, -2), (key2461, -2), (key2567, -6), (key2579, 2), (key2579, 2), (key2567, 2)]

def rawRow2915 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2363, -2), (key2361, 6), (key2517, 2), (key2523, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2579, -6), (key2567, 2), (key2567, 2), (key2579, 2)]

def rawRow2916 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2363, -2), (key2361, 6), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2579, -6), (key2567, 2), (key2579, 2), (key2567, 2)]

def rawRow2917 : Integer.Sparse Key := [(key2363, -2), (key2363, -2), (key2357, -2), (key2361, 6), (key2523, 2), (key2523, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2579, -6), (key2579, 2), (key2567, 2), (key2567, 2)]

def rawRow2918 : Integer.Sparse Key := [(key2452, -2), (key2452, -2), (key2458, -2), (key2519, 6), (key2357, 2), (key2361, 2), (key2366, 2), (key2567, -2), (key2579, -2), (key2579, -2), (key2366, -6), (key2461, 2), (key2523, 2), (key2523, 2)]

def rawRow2919 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2452, -2), (key2519, 6), (key2357, 2), (key2363, 2), (key2361, 2), (key2579, -2), (key2567, -2), (key2579, -2), (key2366, -6), (key2523, 2), (key2461, 2), (key2523, 2)]

def rawRow2920 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2452, -2), (key2519, 6), (key2363, 2), (key2357, 2), (key2361, 2), (key2579, -2), (key2579, -2), (key2567, -2), (key2366, -6), (key2523, 2), (key2523, 2), (key2461, 2)]

def rawRow2921 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2519, -2), (key2452, 6), (key2528, 2), (key2530, 2), (key2560, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2523, -6), (key2366, 2), (key2461, 2), (key2523, 2)]

def rawRow2922 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2519, -2), (key2452, 6), (key2530, 2), (key2528, 2), (key2560, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2523, -6), (key2366, 2), (key2523, 2), (key2461, 2)]

def rawRow2923 : Integer.Sparse Key := [(key2452, -2), (key2519, -2), (key2458, -2), (key2452, 6), (key2528, 2), (key2560, 2), (key2530, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2523, -6), (key2461, 2), (key2366, 2), (key2523, 2)]

def rawRow2924 : Integer.Sparse Key := [(key2519, -2), (key2452, -2), (key2458, -2), (key2452, 6), (key2560, 2), (key2528, 2), (key2530, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2523, -6), (key2461, 2), (key2523, 2), (key2366, 2)]

def rawRow2925 : Integer.Sparse Key := [(key2458, -2), (key2519, -2), (key2452, -2), (key2452, 6), (key2530, 2), (key2560, 2), (key2528, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2523, -6), (key2523, 2), (key2366, 2), (key2461, 2)]

def rawRow2926 : Integer.Sparse Key := [(key2519, -2), (key2458, -2), (key2452, -2), (key2452, 6), (key2560, 2), (key2530, 2), (key2528, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2523, -6), (key2523, 2), (key2461, 2), (key2366, 2)]

def rawRow2927 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2530, -2), (key2560, 6), (key2357, 2), (key2363, 2), (key2363, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2361, -6), (key2456, 2), (key2456, 2), (key2517, 2)]

def rawRow2928 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2530, -2), (key2560, 6), (key2363, 2), (key2357, 2), (key2363, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2361, -6), (key2456, 2), (key2517, 2), (key2456, 2)]

def rawRow2929 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2528, -2), (key2560, 6), (key2363, 2), (key2363, 2), (key2357, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2361, -6), (key2517, 2), (key2456, 2), (key2456, 2)]

def rawRow2930 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2560, -2), (key2530, 6), (key2452, 2), (key2458, 2), (key2519, 2), (key2363, -2), (key2458, -2), (key2530, -2), (key2456, -6), (key2361, 2), (key2456, 2), (key2517, 2)]

def rawRow2931 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2560, -2), (key2530, 6), (key2458, 2), (key2452, 2), (key2519, 2), (key2363, -2), (key2530, -2), (key2458, -2), (key2456, -6), (key2361, 2), (key2517, 2), (key2456, 2)]

def rawRow2932 : Integer.Sparse Key := [(key2528, -2), (key2560, -2), (key2530, -2), (key2530, 6), (key2452, 2), (key2519, 2), (key2458, 2), (key2458, -2), (key2363, -2), (key2530, -2), (key2456, -6), (key2456, 2), (key2361, 2), (key2517, 2)]

def rawRow2933 : Integer.Sparse Key := [(key2560, -2), (key2528, -2), (key2530, -2), (key2530, 6), (key2519, 2), (key2452, 2), (key2458, 2), (key2458, -2), (key2530, -2), (key2363, -2), (key2456, -6), (key2456, 2), (key2517, 2), (key2361, 2)]

def rawRow2934 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2528, -2), (key2530, 6), (key2458, 2), (key2519, 2), (key2452, 2), (key2530, -2), (key2363, -2), (key2458, -2), (key2456, -6), (key2517, 2), (key2361, 2), (key2456, 2)]

def rawRow2935 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2528, -2), (key2530, 6), (key2519, 2), (key2458, 2), (key2452, 2), (key2530, -2), (key2458, -2), (key2363, -2), (key2456, -6), (key2517, 2), (key2456, 2), (key2361, 2)]

def rawRow2936 : Integer.Sparse Key := [(key2361, -2), (key2361, -2), (key2364, -2), (key2364, 6), (key2456, 2), (key2456, 2), (key2459, 2), (key2459, -2), (key2520, -2), (key2520, -2), (key2531, -6), (key2531, 2), (key2561, 2), (key2561, 2)]

def rawRow2937 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2361, -2), (key2364, 6), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, -2), (key2459, -2), (key2520, -2), (key2531, -6), (key2561, 2), (key2531, 2), (key2561, 2)]

def rawRow2938 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2361, -2), (key2364, 6), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2459, -2), (key2531, -6), (key2561, 2), (key2561, 2), (key2531, 2)]

def rawRow2939 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2364, -2), (key2361, 6), (key2517, 2), (key2520, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2561, -6), (key2531, 2), (key2531, 2), (key2561, 2)]

def rawRow2940 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2364, -2), (key2361, 6), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2561, -6), (key2531, 2), (key2561, 2), (key2531, 2)]

def rawRow2941 : Integer.Sparse Key := [(key2364, -2), (key2364, -2), (key2361, -2), (key2361, 6), (key2520, 2), (key2520, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2561, -6), (key2561, 2), (key2531, 2), (key2531, 2)]

def rawRow2942 : Integer.Sparse Key := [(key2456, -2), (key2456, -2), (key2459, -2), (key2531, 6), (key2361, 2), (key2361, 2), (key2364, 2), (key2531, -2), (key2561, -2), (key2561, -2), (key2364, -6), (key2459, 2), (key2520, 2), (key2520, 2)]

def rawRow2943 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2456, -2), (key2531, 6), (key2361, 2), (key2364, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2561, -2), (key2364, -6), (key2520, 2), (key2459, 2), (key2520, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2944 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2456, -2), (key2531, 6), (key2364, 2), (key2361, 2), (key2361, 2), (key2561, -2), (key2561, -2), (key2531, -2), (key2364, -6), (key2520, 2), (key2520, 2), (key2459, 2)]

def rawRow2945 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2531, -2), (key2456, 6), (key2517, 2), (key2520, 2), (key2561, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2520, -6), (key2364, 2), (key2459, 2), (key2520, 2)]

def rawRow2946 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2531, -2), (key2456, 6), (key2520, 2), (key2517, 2), (key2561, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2520, -6), (key2364, 2), (key2520, 2), (key2459, 2)]

def rawRow2947 : Integer.Sparse Key := [(key2456, -2), (key2531, -2), (key2459, -2), (key2456, 6), (key2517, 2), (key2561, 2), (key2520, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2520, -6), (key2459, 2), (key2364, 2), (key2520, 2)]

def rawRow2948 : Integer.Sparse Key := [(key2531, -2), (key2456, -2), (key2459, -2), (key2456, 6), (key2561, 2), (key2517, 2), (key2520, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2520, -6), (key2459, 2), (key2520, 2), (key2364, 2)]

def rawRow2949 : Integer.Sparse Key := [(key2459, -2), (key2531, -2), (key2456, -2), (key2456, 6), (key2520, 2), (key2561, 2), (key2517, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2520, -6), (key2520, 2), (key2364, 2), (key2459, 2)]

def rawRow2950 : Integer.Sparse Key := [(key2531, -2), (key2459, -2), (key2456, -2), (key2456, 6), (key2561, 2), (key2520, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2520, -6), (key2520, 2), (key2459, 2), (key2364, 2)]

def rawRow2951 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2520, -2), (key2561, 6), (key2361, 2), (key2364, 2), (key2364, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2361, -6), (key2456, 2), (key2456, 2), (key2517, 2)]

def rawRow2952 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2520, -2), (key2561, 6), (key2364, 2), (key2361, 2), (key2364, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2361, -6), (key2456, 2), (key2517, 2), (key2456, 2)]

def rawRow2953 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2517, -2), (key2561, 6), (key2364, 2), (key2364, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2361, -6), (key2517, 2), (key2456, 2), (key2456, 2)]

def rawRow2954 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2561, -2), (key2520, 6), (key2456, 2), (key2459, 2), (key2531, 2), (key2364, -2), (key2459, -2), (key2520, -2), (key2456, -6), (key2361, 2), (key2456, 2), (key2517, 2)]

def rawRow2955 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2561, -2), (key2520, 6), (key2459, 2), (key2456, 2), (key2531, 2), (key2364, -2), (key2520, -2), (key2459, -2), (key2456, -6), (key2361, 2), (key2517, 2), (key2456, 2)]

def rawRow2956 : Integer.Sparse Key := [(key2517, -2), (key2561, -2), (key2520, -2), (key2520, 6), (key2456, 2), (key2531, 2), (key2459, 2), (key2459, -2), (key2364, -2), (key2520, -2), (key2456, -6), (key2456, 2), (key2361, 2), (key2517, 2)]

def rawRow2957 : Integer.Sparse Key := [(key2561, -2), (key2517, -2), (key2520, -2), (key2520, 6), (key2531, 2), (key2456, 2), (key2459, 2), (key2459, -2), (key2520, -2), (key2364, -2), (key2456, -6), (key2456, 2), (key2517, 2), (key2361, 2)]

def rawRow2958 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2517, -2), (key2520, 6), (key2459, 2), (key2531, 2), (key2456, 2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -6), (key2517, 2), (key2361, 2), (key2456, 2)]

def rawRow2959 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2517, -2), (key2520, 6), (key2531, 2), (key2459, 2), (key2456, 2), (key2520, -2), (key2459, -2), (key2364, -2), (key2456, -6), (key2517, 2), (key2456, 2), (key2361, 2)]

def rawRow2960 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 2), (key2406, 2), (key2409, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2482, -1), (key2482, -1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1)]

def rawRow2961 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2406, 2), (key2409, 2), (key2406, 2), (key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2482, -1), (key2472, -1), (key2482, -1), (key2472, -1), (key2480, -1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1)]

def rawRow2962 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2409, 2), (key2406, 2), (key2406, 2), (key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2482, -1), (key2480, -1), (key2482, -1), (key2472, -1), (key2480, -1), (key2472, -1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1)]

def rawRow2963 : Integer.Sparse Key := [(key2390, -2), (key2392, -2), (key2392, -2), (key2378, 1), (key2381, 1), (key2378, 1), (key2392, 1), (key2381, 1), (key2392, 1), (key2437, 2), (key2440, 2), (key2440, 2), (key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2503, -1), (key2506, -1), (key2503, -1), (key2522, -1), (key2506, -1), (key2522, -1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1)]

def rawRow2964 : Integer.Sparse Key := [(key2392, -2), (key2390, -2), (key2392, -2), (key2381, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2381, 1), (key2440, 2), (key2437, 2), (key2440, 2), (key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2503, -1), (key2522, -1), (key2503, -1), (key2522, -1), (key2506, -1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1)]

def rawRow2965 : Integer.Sparse Key := [(key2392, -2), (key2392, -2), (key2390, -2), (key2392, 1), (key2392, 1), (key2381, 1), (key2381, 1), (key2378, 1), (key2378, 1), (key2440, 2), (key2440, 2), (key2437, 2), (key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2522, -1), (key2522, -1), (key2506, -1), (key2506, -1), (key2503, -1), (key2503, -1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1)]

def rawRow2966 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2378, 2), (key2378, 2), (key2381, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2378, -1), (key2378, -1), (key2390, -1), (key2390, -1), (key2392, -1), (key2392, -1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1)]

def rawRow2967 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2378, 2), (key2381, 2), (key2378, 2), (key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2390, -1), (key2392, -1), (key2378, -1), (key2392, -1), (key2378, -1), (key2390, -1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1)]

def rawRow2968 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2381, 2), (key2378, 2), (key2378, 2), (key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2392, -1), (key2390, -1), (key2392, -1), (key2378, -1), (key2390, -1), (key2378, -1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1)]

def rawRow2969 : Integer.Sparse Key := [(key2480, -2), (key2482, -2), (key2543, -2), (key2406, 1), (key2409, 1), (key2472, 1), (key2482, 1), (key2538, 1), (key2543, 1), (key2503, 2), (key2506, 2), (key2554, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2437, -1), (key2440, -1), (key2503, -1), (key2522, -1), (key2554, -1), (key2563, -1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1)]

def rawRow2970 : Integer.Sparse Key := [(key2482, -2), (key2480, -2), (key2543, -2), (key2409, 1), (key2406, 1), (key2482, 1), (key2472, 1), (key2543, 1), (key2538, 1), (key2506, 2), (key2503, 2), (key2554, 2), (key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2440, -1), (key2437, -1), (key2522, -1), (key2503, -1), (key2563, -1), (key2554, -1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1)]

def rawRow2971 : Integer.Sparse Key := [(key2480, -2), (key2543, -2), (key2482, -2), (key2472, 1), (key2538, 1), (key2406, 1), (key2543, 1), (key2409, 1), (key2482, 1), (key2503, 2), (key2554, 2), (key2506, 2), (key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2503, -1), (key2554, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1)]

def rawRow2972 : Integer.Sparse Key := [(key2543, -2), (key2480, -2), (key2482, -2), (key2538, 1), (key2472, 1), (key2543, 1), (key2406, 1), (key2482, 1), (key2409, 1), (key2554, 2), (key2503, 2), (key2506, 2), (key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2522, -1), (key2440, -1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1)]

def rawRow2973 : Integer.Sparse Key := [(key2482, -2), (key2543, -2), (key2480, -2), (key2482, 1), (key2543, 1), (key2409, 1), (key2538, 1), (key2406, 1), (key2472, 1), (key2506, 2), (key2554, 2), (key2503, 2), (key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2522, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2437, -1), (key2503, -1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1)]

def rawRow2974 : Integer.Sparse Key := [(key2543, -2), (key2482, -2), (key2480, -2), (key2543, 1), (key2482, 1), (key2538, 1), (key2409, 1), (key2472, 1), (key2406, 1), (key2554, 2), (key2506, 2), (key2503, 2), (key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2563, -1), (key2522, -1), (key2554, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1)]

def rawRow2975 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2440, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2390, 2), (key2392, 2), (key2392, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2378, -1), (key2381, -1), (key2378, -1), (key2392, -1), (key2381, -1), (key2392, -1), (key2406, 1), (key2409, 1), (key2406, 1), (key2440, 1), (key2409, 1), (key2440, 1)]

def rawRow2976 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2440, -2), (key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2392, 2), (key2390, 2), (key2392, 2), (key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2381, -1), (key2378, -1), (key2392, -1), (key2378, -1), (key2392, -1), (key2381, -1), (key2409, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2409, 1)]

def rawRow2977 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2437, -2), (key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2392, 2), (key2392, 2), (key2390, 2), (key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2392, -1), (key2392, -1), (key2381, -1), (key2381, -1), (key2378, -1), (key2378, -1), (key2440, 1), (key2440, 1), (key2409, 1), (key2409, 1), (key2406, 1), (key2406, 1)]

def rawRow2978 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2554, -2), (key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2480, 2), (key2482, 2), (key2543, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2406, -1), (key2409, -1), (key2472, -1), (key2482, -1), (key2538, -1), (key2543, -1), (key2378, 1), (key2381, 1), (key2472, 1), (key2506, 1), (key2538, 1), (key2554, 1)]

def rawRow2979 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2554, -2), (key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2482, 2), (key2480, 2), (key2543, 2), (key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2409, -1), (key2406, -1), (key2482, -1), (key2472, -1), (key2543, -1), (key2538, -1), (key2381, 1), (key2378, 1), (key2506, 1), (key2472, 1), (key2554, 1), (key2538, 1)]

def rawRow2980 : Integer.Sparse Key := [(key2503, -2), (key2554, -2), (key2506, -2), (key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 2), (key2543, 2), (key2482, 2), (key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2472, -1), (key2538, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2472, 1), (key2538, 1), (key2378, 1), (key2554, 1), (key2381, 1), (key2506, 1)]

def rawRow2981 : Integer.Sparse Key := [(key2554, -2), (key2503, -2), (key2506, -2), (key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 2), (key2480, 2), (key2482, 2), (key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2482, -1), (key2409, -1), (key2538, 1), (key2472, 1), (key2554, 1), (key2378, 1), (key2506, 1), (key2381, 1)]

def rawRow2982 : Integer.Sparse Key := [(key2506, -2), (key2554, -2), (key2503, -2), (key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2482, 2), (key2543, 2), (key2480, 2), (key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2482, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2406, -1), (key2472, -1), (key2506, 1), (key2554, 1), (key2381, 1), (key2538, 1), (key2378, 1), (key2472, 1)]

def rawRow2983 : Integer.Sparse Key := [(key2554, -2), (key2506, -2), (key2503, -2), (key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2543, 2), (key2482, 2), (key2480, 2), (key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2543, -1), (key2482, -1), (key2538, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2554, 1), (key2506, 1), (key2538, 1), (key2381, 1), (key2472, 1), (key2378, 1)]

def rawRow2984 : Integer.Sparse Key := [(key1999, -2), (key1999, -2), (key2003, -2), (key2003, 6), (key2268, 2), (key2268, 2), (key2272, 2), (key2272, -2), (key2324, -2), (key2324, -2), (key2294, -6), (key2294, 2), (key2336, 2), (key2336, 2)]

def rawRow2985 : Integer.Sparse Key := [(key1999, -2), (key2003, -2), (key1999, -2), (key2003, 6), (key2268, 2), (key2272, 2), (key2268, 2), (key2324, -2), (key2272, -2), (key2324, -2), (key2294, -6), (key2336, 2), (key2294, 2), (key2336, 2)]

def rawRow2986 : Integer.Sparse Key := [(key2003, -2), (key1999, -2), (key1999, -2), (key2003, 6), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, -2), (key2324, -2), (key2272, -2), (key2294, -6), (key2336, 2), (key2336, 2), (key2294, 2)]

def rawRow2987 : Integer.Sparse Key := [(key1999, -2), (key2003, -2), (key2003, -2), (key1999, 6), (key2323, 2), (key2324, 2), (key2324, 2), (key2268, -2), (key2268, -2), (key2323, -2), (key2336, -6), (key2294, 2), (key2294, 2), (key2336, 2)]

def rawRow2988 : Integer.Sparse Key := [(key2003, -2), (key1999, -2), (key2003, -2), (key1999, 6), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, -2), (key2323, -2), (key2268, -2), (key2336, -6), (key2294, 2), (key2336, 2), (key2294, 2)]

def rawRow2989 : Integer.Sparse Key := [(key2003, -2), (key2003, -2), (key1999, -2), (key1999, 6), (key2324, 2), (key2324, 2), (key2323, 2), (key2323, -2), (key2268, -2), (key2268, -2), (key2336, -6), (key2336, 2), (key2294, 2), (key2294, 2)]

def rawRow2990 : Integer.Sparse Key := [(key2268, -2), (key2268, -2), (key2272, -2), (key2294, 6), (key1999, 2), (key1999, 2), (key2003, 2), (key2294, -2), (key2336, -2), (key2336, -2), (key2003, -6), (key2272, 2), (key2324, 2), (key2324, 2)]

def rawRow2991 : Integer.Sparse Key := [(key2268, -2), (key2272, -2), (key2268, -2), (key2294, 6), (key1999, 2), (key2003, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2336, -2), (key2003, -6), (key2324, 2), (key2272, 2), (key2324, 2)]

def rawRow2992 : Integer.Sparse Key := [(key2272, -2), (key2268, -2), (key2268, -2), (key2294, 6), (key2003, 2), (key1999, 2), (key1999, 2), (key2336, -2), (key2336, -2), (key2294, -2), (key2003, -6), (key2324, 2), (key2324, 2), (key2272, 2)]

def rawRow2993 : Integer.Sparse Key := [(key2268, -2), (key2272, -2), (key2294, -2), (key2268, 6), (key2323, 2), (key2324, 2), (key2336, 2), (key1999, -2), (key2268, -2), (key2323, -2), (key2324, -6), (key2003, 2), (key2272, 2), (key2324, 2)]

def rawRow2994 : Integer.Sparse Key := [(key2272, -2), (key2268, -2), (key2294, -2), (key2268, 6), (key2324, 2), (key2323, 2), (key2336, 2), (key1999, -2), (key2323, -2), (key2268, -2), (key2324, -6), (key2003, 2), (key2324, 2), (key2272, 2)]

def rawRow2995 : Integer.Sparse Key := [(key2268, -2), (key2294, -2), (key2272, -2), (key2268, 6), (key2323, 2), (key2336, 2), (key2324, 2), (key2268, -2), (key1999, -2), (key2323, -2), (key2324, -6), (key2272, 2), (key2003, 2), (key2324, 2)]

def rawRow2996 : Integer.Sparse Key := [(key2294, -2), (key2268, -2), (key2272, -2), (key2268, 6), (key2336, 2), (key2323, 2), (key2324, 2), (key2268, -2), (key2323, -2), (key1999, -2), (key2324, -6), (key2272, 2), (key2324, 2), (key2003, 2)]

def rawRow2997 : Integer.Sparse Key := [(key2272, -2), (key2294, -2), (key2268, -2), (key2268, 6), (key2324, 2), (key2336, 2), (key2323, 2), (key2323, -2), (key1999, -2), (key2268, -2), (key2324, -6), (key2324, 2), (key2003, 2), (key2272, 2)]

def rawRow2998 : Integer.Sparse Key := [(key2294, -2), (key2272, -2), (key2268, -2), (key2268, 6), (key2336, 2), (key2324, 2), (key2323, 2), (key2323, -2), (key2268, -2), (key1999, -2), (key2324, -6), (key2324, 2), (key2272, 2), (key2003, 2)]

def rawRow2999 : Integer.Sparse Key := [(key2323, -2), (key2324, -2), (key2324, -2), (key2336, 6), (key1999, 2), (key2003, 2), (key2003, 2), (key2294, -2), (key2294, -2), (key2336, -2), (key1999, -6), (key2268, 2), (key2268, 2), (key2323, 2)]

def rawRow3000 : Integer.Sparse Key := [(key2324, -2), (key2323, -2), (key2324, -2), (key2336, 6), (key2003, 2), (key1999, 2), (key2003, 2), (key2294, -2), (key2336, -2), (key2294, -2), (key1999, -6), (key2268, 2), (key2323, 2), (key2268, 2)]

def rawRow3001 : Integer.Sparse Key := [(key2324, -2), (key2324, -2), (key2323, -2), (key2336, 6), (key2003, 2), (key2003, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2294, -2), (key1999, -6), (key2323, 2), (key2268, 2), (key2268, 2)]

def rawRow3002 : Integer.Sparse Key := [(key2323, -2), (key2324, -2), (key2336, -2), (key2324, 6), (key2268, 2), (key2272, 2), (key2294, 2), (key2003, -2), (key2272, -2), (key2324, -2), (key2268, -6), (key1999, 2), (key2268, 2), (key2323, 2)]

def rawRow3003 : Integer.Sparse Key := [(key2324, -2), (key2323, -2), (key2336, -2), (key2324, 6), (key2272, 2), (key2268, 2), (key2294, 2), (key2003, -2), (key2324, -2), (key2272, -2), (key2268, -6), (key1999, 2), (key2323, 2), (key2268, 2)]

def rawRow3004 : Integer.Sparse Key := [(key2323, -2), (key2336, -2), (key2324, -2), (key2324, 6), (key2268, 2), (key2294, 2), (key2272, 2), (key2272, -2), (key2003, -2), (key2324, -2), (key2268, -6), (key2268, 2), (key1999, 2), (key2323, 2)]

def rawRow3005 : Integer.Sparse Key := [(key2336, -2), (key2323, -2), (key2324, -2), (key2324, 6), (key2294, 2), (key2268, 2), (key2272, 2), (key2272, -2), (key2324, -2), (key2003, -2), (key2268, -6), (key2268, 2), (key2323, 2), (key1999, 2)]

def rawRow3006 : Integer.Sparse Key := [(key2324, -2), (key2336, -2), (key2323, -2), (key2324, 6), (key2272, 2), (key2294, 2), (key2268, 2), (key2324, -2), (key2003, -2), (key2272, -2), (key2268, -6), (key2323, 2), (key1999, 2), (key2268, 2)]

def rawRow3007 : Integer.Sparse Key := [(key2336, -2), (key2324, -2), (key2323, -2), (key2324, 6), (key2294, 2), (key2272, 2), (key2268, 2), (key2324, -2), (key2272, -2), (key2003, -2), (key2268, -6), (key2323, 2), (key2268, 2), (key1999, 2)]

def rawRow3008 : Integer.Sparse Key := [(key2362, -2), (key2365, -2), (key2365, -2), (key2365, 2), (key2365, 2), (key2367, 2), (key2457, 2), (key2460, 2), (key2460, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, 1), (key2532, 1), (key2562, 1), (key2562, 1), (key2564, 1), (key2564, 1)]

def rawRow3009 : Integer.Sparse Key := [(key2365, -2), (key2362, -2), (key2365, -2), (key2365, 2), (key2367, 2), (key2365, 2), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, 1), (key2564, 1), (key2532, 1), (key2564, 1), (key2532, 1), (key2562, 1)]

def rawRow3010 : Integer.Sparse Key := [(key2365, -2), (key2365, -2), (key2362, -2), (key2367, 2), (key2365, 2), (key2365, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, 1), (key2562, 1), (key2564, 1), (key2532, 1), (key2562, 1), (key2532, 1)]

def rawRow3011 : Integer.Sparse Key := [(key2365, -2), (key2365, -2), (key2367, -2), (key2362, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, 1), (key2533, 1), (key2532, 1), (key2564, 1), (key2533, 1), (key2564, 1)]

def rawRow3012 : Integer.Sparse Key := [(key2365, -2), (key2367, -2), (key2365, -2), (key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, 1), (key2532, 1), (key2564, 1), (key2532, 1), (key2564, 1), (key2533, 1)]

def rawRow3013 : Integer.Sparse Key := [(key2367, -2), (key2365, -2), (key2365, -2), (key2365, 2), (key2365, 2), (key2362, 2), (key2525, 2), (key2521, 2), (key2521, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, 1), (key2564, 1), (key2533, 1), (key2533, 1), (key2532, 1), (key2532, 1)]

def rawRow3014 : Integer.Sparse Key := [(key2457, -2), (key2460, -2), (key2460, -2), (key2521, 2), (key2521, 2), (key2525, 2), (key2362, 2), (key2365, 2), (key2365, 2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, 1), (key2460, 1), (key2521, 1), (key2521, 1), (key2525, 1), (key2525, 1)]

def rawRow3015 : Integer.Sparse Key := [(key2460, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2365, 2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, 1), (key2525, 1), (key2460, 1), (key2525, 1), (key2460, 1), (key2521, 1)]

def rawRow3016 : Integer.Sparse Key := [(key2460, -2), (key2460, -2), (key2457, -2), (key2525, 2), (key2521, 2), (key2521, 2), (key2365, 2), (key2365, 2), (key2362, 2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, 1), (key2521, 1), (key2525, 1), (key2460, 1), (key2521, 1), (key2460, 1)]

def rawRow3017 : Integer.Sparse Key := [(key2460, -2), (key2521, -2), (key2525, -2), (key2457, 2), (key2460, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, 1), (key2367, 1), (key2460, 1), (key2525, 1), (key2533, 1), (key2564, 1)]

def rawRow3018 : Integer.Sparse Key := [(key2460, -2), (key2525, -2), (key2521, -2), (key2460, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, 1), (key2365, 1), (key2525, 1), (key2460, 1), (key2564, 1), (key2533, 1)]

def rawRow3019 : Integer.Sparse Key := [(key2521, -2), (key2460, -2), (key2525, -2), (key2457, 2), (key2521, 2), (key2460, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, 1), (key2533, 1), (key2365, 1), (key2564, 1), (key2367, 1), (key2525, 1)]

def rawRow3020 : Integer.Sparse Key := [(key2521, -2), (key2525, -2), (key2460, -2), (key2521, 2), (key2457, 2), (key2460, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, 1), (key2460, 1), (key2564, 1), (key2365, 1), (key2525, 1), (key2367, 1)]

def rawRow3021 : Integer.Sparse Key := [(key2525, -2), (key2460, -2), (key2521, -2), (key2460, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, 1), (key2564, 1), (key2367, 1), (key2533, 1), (key2365, 1), (key2460, 1)]

def rawRow3022 : Integer.Sparse Key := [(key2525, -2), (key2521, -2), (key2460, -2), (key2521, 2), (key2460, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, 1), (key2525, 1), (key2533, 1), (key2367, 1), (key2460, 1), (key2365, 1)]

def rawRow3023 : Integer.Sparse Key := [(key2532, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2), (key2564, 2), (key2365, 2), (key2365, 2), (key2367, 2), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2564, -1), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, 1), (key2460, 1), (key2457, 1), (key2521, 1), (key2460, 1), (key2521, 1)]

def rawRow3024 : Integer.Sparse Key := [(key2532, -2), (key2533, -2), (key2532, -2), (key2564, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2367, 2), (key2365, 2), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, 1), (key2457, 1), (key2521, 1), (key2457, 1), (key2521, 1), (key2460, 1)]

def rawRow3025 : Integer.Sparse Key := [(key2533, -2), (key2532, -2), (key2532, -2), (key2564, 2), (key2564, 2), (key2562, 2), (key2367, 2), (key2365, 2), (key2365, 2), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, -1), (key2521, -1), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, 1), (key2521, 1), (key2460, 1), (key2460, 1), (key2457, 1), (key2457, 1)]

def rawRow3026 : Integer.Sparse Key := [(key2532, -2), (key2562, -2), (key2564, -2), (key2532, 2), (key2533, 2), (key2564, 2), (key2460, 2), (key2521, 2), (key2525, 2), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, -1), (key2564, -1), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, 1), (key2365, 1), (key2457, 1), (key2521, 1), (key2532, 1), (key2562, 1)]

def rawRow3027 : Integer.Sparse Key := [(key2532, -2), (key2564, -2), (key2562, -2), (key2533, 2), (key2532, 2), (key2564, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, -1), (key2525, -1), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, 1), (key2362, 1), (key2521, 1), (key2457, 1), (key2562, 1), (key2532, 1)]

def rawRow3028 : Integer.Sparse Key := [(key2562, -2), (key2532, -2), (key2564, -2), (key2532, 2), (key2564, 2), (key2533, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, 1), (key2521, 1), (key2362, 1), (key2562, 1), (key2365, 1), (key2521, 1)]

def rawRow3029 : Integer.Sparse Key := [(key2562, -2), (key2564, -2), (key2532, -2), (key2564, 2), (key2532, 2), (key2533, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, -1), (key2367, -1), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, 1), (key2457, 1), (key2562, 1), (key2362, 1), (key2521, 1), (key2365, 1)]

def rawRow3030 : Integer.Sparse Key := [(key2564, -2), (key2532, -2), (key2562, -2), (key2533, 2), (key2564, 2), (key2532, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, -1), (key2460, -1), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, 1), (key2562, 1), (key2365, 1), (key2521, 1), (key2362, 1), (key2457, 1)]

def rawRow3031 : Integer.Sparse Key := [(key2564, -2), (key2562, -2), (key2532, -2), (key2564, 2), (key2533, 2), (key2532, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, 1), (key2532, 1), (key2521, 1), (key2365, 1), (key2457, 1), (key2362, 1)]

def rawRow3032 : Integer.Sparse Key := [(key2621, -2), (key2835, -2), (key2835, -2), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2641, 2), (key2976, 2), (key2976, 2), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2653, -1), (key2653, -1), (key2897, -1), (key2897, -1), (key2998, -1), (key2998, -1), (key2648, 1), (key2648, 1), (key2737, 1), (key2737, 1), (key2997, 1), (key2997, 1)]

def rawRow3033 : Integer.Sparse Key := [(key2835, -2), (key2621, -2), (key2835, -2), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2976, 2), (key2641, 2), (key2976, 2), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2897, -1), (key2998, -1), (key2653, -1), (key2998, -1), (key2653, -1), (key2897, -1), (key2737, 1), (key2997, 1), (key2648, 1), (key2997, 1), (key2648, 1), (key2737, 1)]

def rawRow3034 : Integer.Sparse Key := [(key2835, -2), (key2835, -2), (key2621, -2), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2616, 1), (key2976, 2), (key2976, 2), (key2641, 2), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2628, -1), (key2998, -1), (key2897, -1), (key2998, -1), (key2653, -1), (key2897, -1), (key2653, -1), (key2997, 1), (key2737, 1), (key2997, 1), (key2648, 1), (key2737, 1), (key2648, 1)]

def rawRow3035 : Integer.Sparse Key := [(key2644, -2), (key2732, -2), (key2885, -2), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, 1), (key2870, 1), (key2660, 2), (key2758, 2), (key2927, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2641, -1), (key2653, -1), (key2795, -1), (key2897, -1), (key2943, -1), (key2976, -1), (key2618, 1), (key2648, 1), (key2673, 1), (key2737, 1), (key2938, 1), (key2950, 1)]

def rawRow3036 : Integer.Sparse Key := [(key2644, -2), (key2885, -2), (key2732, -2), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2726, 1), (key2660, 2), (key2927, 2), (key2758, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2653, -1), (key2641, -1), (key2897, -1), (key2795, -1), (key2976, -1), (key2943, -1), (key2648, 1), (key2618, 1), (key2737, 1), (key2673, 1), (key2950, 1), (key2938, 1)]

def rawRow3037 : Integer.Sparse Key := [(key2732, -2), (key2644, -2), (key2885, -2), (key2706, 1), (key2726, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2758, 2), (key2660, 2), (key2927, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2795, -1), (key2943, -1), (key2641, -1), (key2976, -1), (key2653, -1), (key2897, -1), (key2673, 1), (key2938, 1), (key2618, 1), (key2950, 1), (key2648, 1), (key2737, 1)]

def rawRow3038 : Integer.Sparse Key := [(key2732, -2), (key2885, -2), (key2644, -2), (key2726, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2860, 1), (key2640, 1), (key2758, 2), (key2927, 2), (key2660, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2943, -1), (key2795, -1), (key2976, -1), (key2641, -1), (key2897, -1), (key2653, -1), (key2938, 1), (key2673, 1), (key2950, 1), (key2618, 1), (key2737, 1), (key2648, 1)]

def rawRow3039 : Integer.Sparse Key := [(key2885, -2), (key2644, -2), (key2732, -2), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, 1), (key2706, 1), (key2927, 2), (key2660, 2), (key2758, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2897, -1), (key2976, -1), (key2653, -1), (key2943, -1), (key2641, -1), (key2795, -1), (key2737, 1), (key2950, 1), (key2648, 1), (key2938, 1), (key2618, 1), (key2673, 1)]

def rawRow3040 : Integer.Sparse Key := [(key2885, -2), (key2732, -2), (key2644, -2), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2927, 2), (key2758, 2), (key2660, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2976, -1), (key2897, -1), (key2943, -1), (key2653, -1), (key2795, -1), (key2641, -1), (key2950, 1), (key2737, 1), (key2938, 1), (key2648, 1), (key2673, 1), (key2618, 1)]

def rawRow3041 : Integer.Sparse Key := [(key2658, -2), (key2923, -2), (key2923, -2), (key2660, 1), (key2660, 1), (key2920, 1), (key2920, 1), (key2927, 1), (key2927, 1), (key2621, 2), (key2835, 2), (key2835, 2), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, -1), (key2885, -1), (key2616, -1), (key2616, -1), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3042 : Integer.Sparse Key := [(key2923, -2), (key2658, -2), (key2923, -2), (key2920, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2920, 1), (key2835, 2), (key2621, 2), (key2835, 2), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3043 : Integer.Sparse Key := [(key2923, -2), (key2923, -2), (key2658, -2), (key2927, 1), (key2920, 1), (key2927, 1), (key2660, 1), (key2920, 1), (key2660, 1), (key2835, 2), (key2835, 2), (key2621, 2), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2644, -1), (key2829, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2616, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3044 : Integer.Sparse Key := [(key2660, -2), (key2758, -2), (key2927, -2), (key2658, 1), (key2660, 1), (key2753, 1), (key2920, 1), (key2758, 1), (key2923, 1), (key2644, 2), (key2732, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2860, -1), (key2726, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow3045 : Integer.Sparse Key := [(key2660, -2), (key2927, -2), (key2758, -2), (key2660, 1), (key2658, 1), (key2920, 1), (key2753, 1), (key2923, 1), (key2758, 1), (key2644, 2), (key2885, 2), (key2732, 2), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2732, -1), (key2640, -1), (key2632, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2726, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow3046 : Integer.Sparse Key := [(key2758, -2), (key2660, -2), (key2927, -2), (key2753, 1), (key2758, 1), (key2658, 1), (key2923, 1), (key2660, 1), (key2920, 1), (key2732, 2), (key2644, 2), (key2885, 2), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2706, -1), (key2726, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow3047 : Integer.Sparse Key := [(key2758, -2), (key2927, -2), (key2660, -2), (key2758, 1), (key2753, 1), (key2923, 1), (key2658, 1), (key2920, 1), (key2660, 1), (key2732, 2), (key2885, 2), (key2644, 2), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, -1), (key2644, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2860, -1), (key2640, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow3048 : Integer.Sparse Key := [(key2927, -2), (key2660, -2), (key2758, -2), (key2920, 1), (key2923, 1), (key2660, 1), (key2758, 1), (key2658, 1), (key2753, 1), (key2885, 2), (key2644, 2), (key2732, 2), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, -1), (key2676, -1), (key2860, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2632, -1), (key2706, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow3049 : Integer.Sparse Key := [(key2927, -2), (key2758, -2), (key2660, -2), (key2923, 1), (key2920, 1), (key2758, 1), (key2660, 1), (key2753, 1), (key2658, 1), (key2885, 2), (key2732, 2), (key2644, 2), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, -1), (key2621, -1), (key2870, -1), (key2860, -1), (key2726, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow3050 : Integer.Sparse Key := [(key1471, -6), (key1384, 2), (key1417, 2), (key1417, 2), (key1902, 6), (key1289, -2), (key1566, -2), (key1566, -2), (key1895, -2), (key1917, -2), (key1917, -2), (key1350, 2), (key1680, 2), (key1680, 2)]

def rawRow3051 : Integer.Sparse Key := [(key1471, -6), (key1417, 2), (key1384, 2), (key1417, 2), (key1902, 6), (key1566, -2), (key1289, -2), (key1566, -2), (key1917, -2), (key1895, -2), (key1917, -2), (key1680, 2), (key1350, 2), (key1680, 2)]

def rawRow3052 : Integer.Sparse Key := [(key1471, -6), (key1417, 2), (key1417, 2), (key1384, 2), (key1902, 6), (key1566, -2), (key1566, -2), (key1289, -2), (key1917, -2), (key1917, -2), (key1895, -2), (key1680, 2), (key1680, 2), (key1350, 2)]

def rawRow3053 : Integer.Sparse Key := [(key1680, -6), (key1539, 2), (key1566, 2), (key1615, 2), (key1917, 6), (key1309, -2), (key1417, -2), (key1615, -2), (key1895, -2), (key1902, -2), (key1917, -2), (key1350, 2), (key1471, 2), (key1680, 2)]

def rawRow3054 : Integer.Sparse Key := [(key1680, -6), (key1539, 2), (key1615, 2), (key1566, 2), (key1917, 6), (key1309, -2), (key1615, -2), (key1417, -2), (key1895, -2), (key1917, -2), (key1902, -2), (key1350, 2), (key1680, 2), (key1471, 2)]

def rawRow3055 : Integer.Sparse Key := [(key1680, -6), (key1566, 2), (key1539, 2), (key1615, 2), (key1917, 6), (key1417, -2), (key1309, -2), (key1615, -2), (key1902, -2), (key1895, -2), (key1917, -2), (key1471, 2), (key1350, 2), (key1680, 2)]

def rawRow3056 : Integer.Sparse Key := [(key1680, -6), (key1566, 2), (key1615, 2), (key1539, 2), (key1917, 6), (key1417, -2), (key1615, -2), (key1309, -2), (key1902, -2), (key1917, -2), (key1895, -2), (key1471, 2), (key1680, 2), (key1350, 2)]

def rawRow3057 : Integer.Sparse Key := [(key1680, -6), (key1615, 2), (key1539, 2), (key1566, 2), (key1917, 6), (key1615, -2), (key1309, -2), (key1417, -2), (key1917, -2), (key1895, -2), (key1902, -2), (key1680, 2), (key1350, 2), (key1471, 2)]

def rawRow3058 : Integer.Sparse Key := [(key1680, -6), (key1615, 2), (key1566, 2), (key1539, 2), (key1917, 6), (key1615, -2), (key1417, -2), (key1309, -2), (key1917, -2), (key1902, -2), (key1895, -2), (key1680, 2), (key1471, 2), (key1350, 2)]

def rawRow3059 : Integer.Sparse Key := [(key1902, -6), (key1895, 2), (key1917, 2), (key1917, 2), (key1471, 6), (key1350, -2), (key1680, -2), (key1680, -2), (key1384, -2), (key1417, -2), (key1417, -2), (key1289, 2), (key1566, 2), (key1566, 2)]

def rawRow3060 : Integer.Sparse Key := [(key1902, -6), (key1917, 2), (key1895, 2), (key1917, 2), (key1471, 6), (key1680, -2), (key1350, -2), (key1680, -2), (key1417, -2), (key1384, -2), (key1417, -2), (key1566, 2), (key1289, 2), (key1566, 2)]

def rawRow3061 : Integer.Sparse Key := [(key1902, -6), (key1917, 2), (key1917, 2), (key1895, 2), (key1471, 6), (key1680, -2), (key1680, -2), (key1350, -2), (key1417, -2), (key1417, -2), (key1384, -2), (key1566, 2), (key1566, 2), (key1289, 2)]

def rawRow3062 : Integer.Sparse Key := [(key1917, -6), (key1895, 2), (key1902, 2), (key1917, 2), (key1680, 6), (key1350, -2), (key1471, -2), (key1680, -2), (key1539, -2), (key1566, -2), (key1615, -2), (key1309, 2), (key1417, 2), (key1615, 2)]

def rawRow3063 : Integer.Sparse Key := [(key1917, -6), (key1895, 2), (key1917, 2), (key1902, 2), (key1680, 6), (key1350, -2), (key1680, -2), (key1471, -2), (key1539, -2), (key1615, -2), (key1566, -2), (key1309, 2), (key1615, 2), (key1417, 2)]

def rawRow3064 : Integer.Sparse Key := [(key1917, -6), (key1902, 2), (key1895, 2), (key1917, 2), (key1680, 6), (key1471, -2), (key1350, -2), (key1680, -2), (key1566, -2), (key1539, -2), (key1615, -2), (key1417, 2), (key1309, 2), (key1615, 2)]

def rawRow3065 : Integer.Sparse Key := [(key1917, -6), (key1902, 2), (key1917, 2), (key1895, 2), (key1680, 6), (key1471, -2), (key1680, -2), (key1350, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1417, 2), (key1615, 2), (key1309, 2)]

def rawRow3066 : Integer.Sparse Key := [(key1917, -6), (key1917, 2), (key1895, 2), (key1902, 2), (key1680, 6), (key1680, -2), (key1350, -2), (key1471, -2), (key1615, -2), (key1539, -2), (key1566, -2), (key1615, 2), (key1309, 2), (key1417, 2)]

def rawRow3067 : Integer.Sparse Key := [(key1917, -6), (key1917, 2), (key1902, 2), (key1895, 2), (key1680, 6), (key1680, -2), (key1471, -2), (key1350, -2), (key1615, -2), (key1566, -2), (key1539, -2), (key1615, 2), (key1417, 2), (key1309, 2)]

def rawRow3068 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1)]

def rawRow3069 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1)]

def rawRow3070 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1)]

def rawRow3071 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3022, -1), (key3016, -1), (key3025, -1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3072 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key3009, -1), (key3007, -1), (key3022, -1), (key3011, -1), (key3025, -1), (key3016, -1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1)]

def rawRow3073 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key3011, -1), (key3016, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1)]

def rawRow3074 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3022, -1), (key3009, -1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1)]

def rawRow3075 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key3022, -1), (key3025, -1), (key3009, -1), (key3016, -1), (key3007, -1), (key3011, -1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1)]

def rawRow3076 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key3025, -1), (key3022, -1), (key3016, -1), (key3009, -1), (key3011, -1), (key3007, -1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

def rawRow3077 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key3007, 1), (key3007, 1), (key3021, 1), (key3021, 1), (key3025, 1), (key3025, 1), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1)]

def rawRow3078 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key3021, 1), (key3025, 1), (key3007, 1), (key3025, 1), (key3007, 1), (key3021, 1), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1)]

def rawRow3079 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key3025, 1), (key3021, 1), (key3025, 1), (key3007, 1), (key3021, 1), (key3007, 1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1)]

def rawRow3080 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2858, -1), (key2827, -1), (key2868, -1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1)]

def rawRow3081 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2792, -1), (key2784, -1), (key2858, -1), (key2807, -1), (key2868, -1), (key2827, -1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1)]

def rawRow3082 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2807, -1), (key2827, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1)]

def rawRow3083 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2858, -1), (key2792, -1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1)]

def rawRow3084 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2858, -1), (key2868, -1), (key2792, -1), (key2827, -1), (key2784, -1), (key2807, -1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1)]

def rawRow3085 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2868, -1), (key2858, -1), (key2827, -1), (key2792, -1), (key2807, -1), (key2784, -1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

def rawRow3086 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1071, -2), (key1036, 6), (key1106, 2), (key1114, 2), (key1150, 2), (key1001, -2), (key1114, -2), (key1232, -2), (key1123, -6), (key1015, 2), (key1123, 2), (key1235, 2)]

def rawRow3087 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1071, -2), (key1036, 6), (key1114, 2), (key1106, 2), (key1150, 2), (key1001, -2), (key1232, -2), (key1114, -2), (key1123, -6), (key1015, 2), (key1235, 2), (key1123, 2)]

def rawRow3088 : Integer.Sparse Key := [(key1028, -2), (key1071, -2), (key1036, -2), (key1036, 6), (key1106, 2), (key1150, 2), (key1114, 2), (key1114, -2), (key1001, -2), (key1232, -2), (key1123, -6), (key1123, 2), (key1015, 2), (key1235, 2)]

def rawRow3089 : Integer.Sparse Key := [(key1071, -2), (key1028, -2), (key1036, -2), (key1036, 6), (key1150, 2), (key1106, 2), (key1114, 2), (key1114, -2), (key1232, -2), (key1001, -2), (key1123, -6), (key1123, 2), (key1235, 2), (key1015, 2)]

def rawRow3090 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1028, -2), (key1036, 6), (key1114, 2), (key1150, 2), (key1106, 2), (key1232, -2), (key1001, -2), (key1114, -2), (key1123, -6), (key1235, 2), (key1015, 2), (key1123, 2)]

def rawRow3091 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1028, -2), (key1036, 6), (key1150, 2), (key1114, 2), (key1106, 2), (key1232, -2), (key1114, -2), (key1001, -2), (key1123, -6), (key1235, 2), (key1123, 2), (key1015, 2)]

def rawRow3092 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1071, -2), (key1028, 6), (key1232, 2), (key1232, 2), (key1242, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1235, -6), (key1015, 2), (key1123, 2), (key1123, 2)]

def rawRow3093 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1036, -2), (key1028, 6), (key1232, 2), (key1242, 2), (key1232, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1235, -6), (key1123, 2), (key1015, 2), (key1123, 2)]

def rawRow3094 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1036, -2), (key1028, 6), (key1242, 2), (key1232, 2), (key1232, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1235, -6), (key1123, 2), (key1123, 2), (key1015, 2)]

def rawRow3095 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1150, -2), (key1123, 6), (key1028, 2), (key1036, 2), (key1071, 2), (key1015, -2), (key1123, -2), (key1235, -2), (key1036, -6), (key1001, 2), (key1114, 2), (key1232, 2)]

def rawRow3096 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1150, -2), (key1123, 6), (key1036, 2), (key1028, 2), (key1071, 2), (key1015, -2), (key1235, -2), (key1123, -2), (key1036, -6), (key1001, 2), (key1232, 2), (key1114, 2)]

def rawRow3097 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1114, -2), (key1123, 6), (key1028, 2), (key1071, 2), (key1036, 2), (key1123, -2), (key1015, -2), (key1235, -2), (key1036, -6), (key1114, 2), (key1001, 2), (key1232, 2)]

def rawRow3098 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1114, -2), (key1123, 6), (key1071, 2), (key1028, 2), (key1036, 2), (key1123, -2), (key1235, -2), (key1015, -2), (key1036, -6), (key1114, 2), (key1232, 2), (key1001, 2)]

def rawRow3099 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1106, -2), (key1123, 6), (key1036, 2), (key1071, 2), (key1028, 2), (key1235, -2), (key1015, -2), (key1123, -2), (key1036, -6), (key1232, 2), (key1001, 2), (key1114, 2)]

def rawRow3100 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1106, -2), (key1123, 6), (key1071, 2), (key1036, 2), (key1028, 2), (key1235, -2), (key1123, -2), (key1015, -2), (key1036, -6), (key1232, 2), (key1114, 2), (key1001, 2)]

def rawRow3101 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1150, -2), (key1106, 6), (key1232, 2), (key1235, 2), (key1242, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1232, -6), (key1001, 2), (key1036, 2), (key1114, 2)]

def rawRow3102 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1150, -2), (key1106, 6), (key1235, 2), (key1232, 2), (key1242, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1232, -6), (key1001, 2), (key1114, 2), (key1036, 2)]

def rawRow3103 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1123, -2), (key1106, 6), (key1232, 2), (key1242, 2), (key1235, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1232, -6), (key1036, 2), (key1001, 2), (key1114, 2)]

def rawRow3104 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1123, -2), (key1106, 6), (key1242, 2), (key1232, 2), (key1235, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1232, -6), (key1036, 2), (key1114, 2), (key1001, 2)]

def rawRow3105 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1114, -2), (key1106, 6), (key1235, 2), (key1242, 2), (key1232, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1232, -6), (key1114, 2), (key1001, 2), (key1036, 2)]

def rawRow3106 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1114, -2), (key1106, 6), (key1242, 2), (key1235, 2), (key1232, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1232, -6), (key1114, 2), (key1036, 2), (key1001, 2)]

def rawRow3107 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1242, -2), (key1235, 6), (key1036, 2), (key1036, 2), (key1071, 2), (key1015, -2), (key1123, -2), (key1123, -2), (key1028, -6), (key993, 2), (key1106, 2), (key1106, 2)]

def rawRow3108 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1232, -2), (key1235, 6), (key1036, 2), (key1071, 2), (key1036, 2), (key1123, -2), (key1015, -2), (key1123, -2), (key1028, -6), (key1106, 2), (key993, 2), (key1106, 2)]

def rawRow3109 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1232, -2), (key1235, 6), (key1071, 2), (key1036, 2), (key1036, 2), (key1123, -2), (key1123, -2), (key1015, -2), (key1028, -6), (key1106, 2), (key1106, 2), (key993, 2)]

def rawRow3110 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1242, -2), (key1232, 6), (key1114, 2), (key1123, 2), (key1150, 2), (key1001, -2), (key1036, -2), (key1114, -2), (key1106, -6), (key993, 2), (key1028, 2), (key1106, 2)]

def rawRow3111 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1242, -2), (key1232, 6), (key1123, 2), (key1114, 2), (key1150, 2), (key1001, -2), (key1114, -2), (key1036, -2), (key1106, -6), (key993, 2), (key1106, 2), (key1028, 2)]

def rawRow3112 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1235, -2), (key1232, 6), (key1114, 2), (key1150, 2), (key1123, 2), (key1036, -2), (key1001, -2), (key1114, -2), (key1106, -6), (key1028, 2), (key993, 2), (key1106, 2)]

def rawRow3113 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1235, -2), (key1232, 6), (key1150, 2), (key1114, 2), (key1123, 2), (key1036, -2), (key1114, -2), (key1001, -2), (key1106, -6), (key1028, 2), (key1106, 2), (key993, 2)]

def rawRow3114 : Integer.Sparse Key := [(key1235, -2), (key1242, -2), (key1232, -2), (key1232, 6), (key1123, 2), (key1150, 2), (key1114, 2), (key1114, -2), (key1001, -2), (key1036, -2), (key1106, -6), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow3115 : Integer.Sparse Key := [(key1242, -2), (key1235, -2), (key1232, -2), (key1232, 6), (key1150, 2), (key1123, 2), (key1114, 2), (key1114, -2), (key1036, -2), (key1001, -2), (key1106, -6), (key1106, 2), (key1028, 2), (key993, 2)]

def rawRow3116 : Integer.Sparse Key := [(key2780, -6), (key2665, 2), (key2780, 2), (key2789, 2), (key2803, 6), (key2610, -2), (key2803, -2), (key2824, -2), (key2700, -2), (key2853, -2), (key2855, -2), (key2626, 2), (key2853, 2), (key2865, 2)]

def rawRow3117 : Integer.Sparse Key := [(key2780, -6), (key2665, 2), (key2789, 2), (key2780, 2), (key2803, 6), (key2610, -2), (key2824, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, 2), (key2865, 2), (key2853, 2)]

def rawRow3118 : Integer.Sparse Key := [(key2780, -6), (key2780, 2), (key2665, 2), (key2789, 2), (key2803, 6), (key2803, -2), (key2610, -2), (key2824, -2), (key2853, -2), (key2700, -2), (key2855, -2), (key2853, 2), (key2626, 2), (key2865, 2)]

def rawRow3119 : Integer.Sparse Key := [(key2780, -6), (key2780, 2), (key2789, 2), (key2665, 2), (key2803, 6), (key2803, -2), (key2824, -2), (key2610, -2), (key2853, -2), (key2855, -2), (key2700, -2), (key2853, 2), (key2865, 2), (key2626, 2)]

def rawRow3120 : Integer.Sparse Key := [(key2780, -6), (key2789, 2), (key2665, 2), (key2780, 2), (key2803, 6), (key2824, -2), (key2610, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, 2), (key2626, 2), (key2853, 2)]

def rawRow3121 : Integer.Sparse Key := [(key2780, -6), (key2789, 2), (key2780, 2), (key2665, 2), (key2803, 6), (key2824, -2), (key2803, -2), (key2610, -2), (key2855, -2), (key2853, -2), (key2700, -2), (key2865, 2), (key2853, 2), (key2626, 2)]

def rawRow3122 : Integer.Sparse Key := [(key2789, -6), (key2665, 2), (key2780, 2), (key2780, 2), (key2824, 6), (key2610, -2), (key2803, -2), (key2803, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2635, 2), (key2855, 2), (key2855, 2)]

def rawRow3123 : Integer.Sparse Key := [(key2789, -6), (key2780, 2), (key2665, 2), (key2780, 2), (key2824, 6), (key2803, -2), (key2610, -2), (key2803, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2855, 2), (key2635, 2), (key2855, 2)]

def rawRow3124 : Integer.Sparse Key := [(key2789, -6), (key2780, 2), (key2780, 2), (key2665, 2), (key2824, 6), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2855, 2), (key2855, 2), (key2635, 2)]

def rawRow3125 : Integer.Sparse Key := [(key2803, -6), (key2700, 2), (key2853, 2), (key2855, 2), (key2780, 6), (key2626, -2), (key2853, -2), (key2865, -2), (key2665, -2), (key2780, -2), (key2789, -2), (key2610, 2), (key2803, 2), (key2824, 2)]

def rawRow3126 : Integer.Sparse Key := [(key2803, -6), (key2700, 2), (key2855, 2), (key2853, 2), (key2780, 6), (key2626, -2), (key2865, -2), (key2853, -2), (key2665, -2), (key2789, -2), (key2780, -2), (key2610, 2), (key2824, 2), (key2803, 2)]

def rawRow3127 : Integer.Sparse Key := [(key2803, -6), (key2853, 2), (key2700, 2), (key2855, 2), (key2780, 6), (key2853, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, 2), (key2610, 2), (key2824, 2)]

def rawRow3128 : Integer.Sparse Key := [(key2803, -6), (key2853, 2), (key2855, 2), (key2700, 2), (key2780, 6), (key2853, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, 2), (key2824, 2), (key2610, 2)]

def rawRow3129 : Integer.Sparse Key := [(key2803, -6), (key2855, 2), (key2700, 2), (key2853, 2), (key2780, 6), (key2865, -2), (key2626, -2), (key2853, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2824, 2), (key2610, 2), (key2803, 2)]

def rawRow3130 : Integer.Sparse Key := [(key2803, -6), (key2855, 2), (key2853, 2), (key2700, 2), (key2780, 6), (key2865, -2), (key2853, -2), (key2626, -2), (key2789, -2), (key2780, -2), (key2665, -2), (key2824, 2), (key2803, 2), (key2610, 2)]

def rawRow3131 : Integer.Sparse Key := [(key2855, -6), (key2700, 2), (key2803, 2), (key2853, 2), (key2865, 6), (key2626, -2), (key2780, -2), (key2853, -2), (key2721, -2), (key2824, -2), (key2865, -2), (key2635, 2), (key2789, 2), (key2855, 2)]

def rawRow3132 : Integer.Sparse Key := [(key2855, -6), (key2700, 2), (key2853, 2), (key2803, 2), (key2865, 6), (key2626, -2), (key2853, -2), (key2780, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2635, 2), (key2855, 2), (key2789, 2)]

def rawRow3133 : Integer.Sparse Key := [(key2855, -6), (key2803, 2), (key2700, 2), (key2853, 2), (key2865, 6), (key2780, -2), (key2626, -2), (key2853, -2), (key2824, -2), (key2721, -2), (key2865, -2), (key2789, 2), (key2635, 2), (key2855, 2)]

def rawRow3134 : Integer.Sparse Key := [(key2855, -6), (key2803, 2), (key2853, 2), (key2700, 2), (key2865, 6), (key2780, -2), (key2853, -2), (key2626, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2789, 2), (key2855, 2), (key2635, 2)]

def rawRow3135 : Integer.Sparse Key := [(key2855, -6), (key2853, 2), (key2700, 2), (key2803, 2), (key2865, 6), (key2853, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, 2), (key2635, 2), (key2789, 2)]

def rawRow3136 : Integer.Sparse Key := [(key2855, -6), (key2853, 2), (key2803, 2), (key2700, 2), (key2865, 6), (key2853, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, 2), (key2789, 2), (key2635, 2)]

def rawRow3137 : Integer.Sparse Key := [(key2824, -6), (key2721, 2), (key2865, 2), (key2865, 2), (key2789, 6), (key2635, -2), (key2855, -2), (key2855, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2610, 2), (key2803, 2), (key2803, 2)]

def rawRow3138 : Integer.Sparse Key := [(key2824, -6), (key2865, 2), (key2721, 2), (key2865, 2), (key2789, 6), (key2855, -2), (key2635, -2), (key2855, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2803, 2), (key2610, 2), (key2803, 2)]

def rawRow3139 : Integer.Sparse Key := [(key2824, -6), (key2865, 2), (key2865, 2), (key2721, 2), (key2789, 6), (key2855, -2), (key2855, -2), (key2635, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2803, 2), (key2803, 2), (key2610, 2)]

def rawRow3140 : Integer.Sparse Key := [(key2865, -6), (key2721, 2), (key2824, 2), (key2865, 2), (key2855, 6), (key2635, -2), (key2789, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, 2), (key2780, 2), (key2853, 2)]

def rawRow3141 : Integer.Sparse Key := [(key2865, -6), (key2721, 2), (key2865, 2), (key2824, 2), (key2855, 6), (key2635, -2), (key2855, -2), (key2789, -2), (key2700, -2), (key2853, -2), (key2803, -2), (key2626, 2), (key2853, 2), (key2780, 2)]

def rawRow3142 : Integer.Sparse Key := [(key2865, -6), (key2824, 2), (key2721, 2), (key2865, 2), (key2855, 6), (key2789, -2), (key2635, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, 2), (key2626, 2), (key2853, 2)]

def rawRow3143 : Integer.Sparse Key := [(key2865, -6), (key2824, 2), (key2865, 2), (key2721, 2), (key2855, 6), (key2789, -2), (key2855, -2), (key2635, -2), (key2803, -2), (key2853, -2), (key2700, -2), (key2780, 2), (key2853, 2), (key2626, 2)]

def rawRow3144 : Integer.Sparse Key := [(key2865, -6), (key2865, 2), (key2721, 2), (key2824, 2), (key2855, 6), (key2855, -2), (key2635, -2), (key2789, -2), (key2853, -2), (key2700, -2), (key2803, -2), (key2853, 2), (key2626, 2), (key2780, 2)]

def rawRow3145 : Integer.Sparse Key := [(key2865, -6), (key2865, 2), (key2824, 2), (key2721, 2), (key2855, 6), (key2855, -2), (key2789, -2), (key2635, -2), (key2853, -2), (key2803, -2), (key2700, -2), (key2853, 2), (key2780, 2), (key2626, 2)]

def rawRow3146 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1568, -1), (key1904, -1), (key1594, -1), (key1912, -1), (key1299, 2), (key1576, 2), (key1904, 2), (key1311, 1), (key1319, 1), (key1617, 1), (key1919, 1), (key1634, 1), (key1927, 1), (key1319, -1), (key1352, -1), (key1549, -1), (key1897, -1), (key1682, -1), (key1919, -1), (key1327, -2), (key1625, -2), (key1921, -2), (key1327, 1), (key1355, 1), (key1557, 1), (key1900, 1), (key1684, 1), (key1921, 1)]

def rawRow3147 : Integer.Sparse Key := [(key1299, -1), (key1291, -1), (key1904, -1), (key1568, -1), (key1912, -1), (key1594, -1), (key1299, 2), (key1904, 2), (key1576, 2), (key1319, 1), (key1311, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1634, 1), (key1352, -1), (key1319, -1), (key1897, -1), (key1549, -1), (key1919, -1), (key1682, -1), (key1327, -2), (key1921, -2), (key1625, -2), (key1355, 1), (key1327, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1684, 1)]

def rawRow3148 : Integer.Sparse Key := [(key1568, -1), (key1594, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1576, 2), (key1299, 2), (key1904, 2), (key1617, 1), (key1634, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1549, -1), (key1682, -1), (key1319, -1), (key1919, -1), (key1352, -1), (key1897, -1), (key1625, -2), (key1327, -2), (key1921, -2), (key1557, 1), (key1684, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1900, 1)]

def rawRow3149 : Integer.Sparse Key := [(key1594, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1904, -1), (key1299, -1), (key1576, 2), (key1904, 2), (key1299, 2), (key1634, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1919, 1), (key1319, 1), (key1682, -1), (key1549, -1), (key1919, -1), (key1319, -1), (key1897, -1), (key1352, -1), (key1625, -2), (key1921, -2), (key1327, -2), (key1684, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1900, 1), (key1355, 1)]

def rawRow3150 : Integer.Sparse Key := [(key1904, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1291, -1), (key1568, -1), (key1904, 2), (key1299, 2), (key1576, 2), (key1919, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1311, 1), (key1617, 1), (key1897, -1), (key1919, -1), (key1352, -1), (key1682, -1), (key1319, -1), (key1549, -1), (key1921, -2), (key1327, -2), (key1625, -2), (key1900, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1327, 1), (key1557, 1)]

def rawRow3151 : Integer.Sparse Key := [(key1912, -1), (key1904, -1), (key1594, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1904, 2), (key1576, 2), (key1299, 2), (key1927, 1), (key1919, 1), (key1634, 1), (key1319, 1), (key1617, 1), (key1311, 1), (key1919, -1), (key1897, -1), (key1682, -1), (key1352, -1), (key1549, -1), (key1319, -1), (key1921, -2), (key1625, -2), (key1327, -2), (key1921, 1), (key1900, 1), (key1684, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

def rawRow3152 : Integer.Sparse Key := [(key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1594, -1), (key1594, -1), (key1291, 2), (key1568, 2), (key1568, 2), (key1352, 1), (key1352, 1), (key1682, 1), (key1682, 1), (key1690, 1), (key1690, 1), (key1311, -1), (key1311, -1), (key1541, -1), (key1541, -1), (key1617, -1), (key1617, -1), (key1355, -2), (key1684, -2), (key1684, -2), (key1327, 1), (key1327, 1), (key1557, 1), (key1557, 1), (key1625, 1), (key1625, 1)]

def rawRow3153 : Integer.Sparse Key := [(key1576, -1), (key1594, -1), (key1299, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1568, 2), (key1291, 2), (key1568, 2), (key1682, 1), (key1690, 1), (key1352, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1541, -1), (key1617, -1), (key1311, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1684, -2), (key1355, -2), (key1684, -2), (key1557, 1), (key1625, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1557, 1)]

def rawRow3154 : Integer.Sparse Key := [(key1594, -1), (key1576, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1568, 2), (key1568, 2), (key1291, 2), (key1690, 1), (key1682, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1352, 1), (key1617, -1), (key1541, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1311, -1), (key1684, -2), (key1684, -2), (key1355, -2), (key1625, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1557, 1), (key1327, 1)]

def rawRow3155 : Integer.Sparse Key := [(key1311, -1), (key1319, -1), (key1617, -1), (key1919, -1), (key1634, -1), (key1927, -1), (key1327, 2), (key1625, 2), (key1921, 2), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1), (key1327, -1), (key1355, -1), (key1557, -1), (key1900, -1), (key1684, -1), (key1921, -1), (key1299, -2), (key1576, -2), (key1904, -2), (key1319, 1), (key1352, 1), (key1549, 1), (key1897, 1), (key1682, 1), (key1919, 1)]

def rawRow3156 : Integer.Sparse Key := [(key1319, -1), (key1311, -1), (key1919, -1), (key1617, -1), (key1927, -1), (key1634, -1), (key1327, 2), (key1921, 2), (key1625, 2), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1), (key1355, -1), (key1327, -1), (key1900, -1), (key1557, -1), (key1921, -1), (key1684, -1), (key1299, -2), (key1904, -2), (key1576, -2), (key1352, 1), (key1319, 1), (key1897, 1), (key1549, 1), (key1919, 1), (key1682, 1)]

def rawRow3157 : Integer.Sparse Key := [(key1617, -1), (key1634, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1625, 2), (key1327, 2), (key1921, 2), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1557, -1), (key1684, -1), (key1327, -1), (key1921, -1), (key1355, -1), (key1900, -1), (key1576, -2), (key1299, -2), (key1904, -2), (key1549, 1), (key1682, 1), (key1319, 1), (key1919, 1), (key1352, 1), (key1897, 1)]

def rawRow3158 : Integer.Sparse Key := [(key1634, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1919, -1), (key1319, -1), (key1625, 2), (key1921, 2), (key1327, 2), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1), (key1684, -1), (key1557, -1), (key1921, -1), (key1327, -1), (key1900, -1), (key1355, -1), (key1576, -2), (key1904, -2), (key1299, -2), (key1682, 1), (key1549, 1), (key1919, 1), (key1319, 1), (key1897, 1), (key1352, 1)]

def rawRow3159 : Integer.Sparse Key := [(key1919, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1311, -1), (key1617, -1), (key1921, 2), (key1327, 2), (key1625, 2), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1), (key1900, -1), (key1921, -1), (key1355, -1), (key1684, -1), (key1327, -1), (key1557, -1), (key1904, -2), (key1299, -2), (key1576, -2), (key1897, 1), (key1919, 1), (key1352, 1), (key1682, 1), (key1319, 1), (key1549, 1)]

def rawRow3160 : Integer.Sparse Key := [(key1927, -1), (key1919, -1), (key1634, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1921, 2), (key1625, 2), (key1327, 2), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1921, -1), (key1900, -1), (key1684, -1), (key1355, -1), (key1557, -1), (key1327, -1), (key1904, -2), (key1576, -2), (key1299, -2), (key1919, 1), (key1897, 1), (key1682, 1), (key1352, 1), (key1549, 1), (key1319, 1)]

def rawRow3161 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1427, -1), (key1625, -1), (key1445, -1), (key1634, -1), (key1311, 2), (key1419, 2), (key1617, 2), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1), (key1291, -1), (key1311, -1), (key1386, -1), (key1541, -1), (key1419, -1), (key1568, -1), (key1352, -2), (key1473, -2), (key1682, -2), (key1299, 1), (key1319, 1), (key1394, 1), (key1549, 1), (key1427, 1), (key1576, 1)]

def rawRow3162 : Integer.Sparse Key := [(key1327, -1), (key1319, -1), (key1625, -1), (key1427, -1), (key1634, -1), (key1445, -1), (key1311, 2), (key1617, 2), (key1419, 2), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1), (key1311, -1), (key1291, -1), (key1541, -1), (key1386, -1), (key1568, -1), (key1419, -1), (key1352, -2), (key1682, -2), (key1473, -2), (key1319, 1), (key1299, 1), (key1549, 1), (key1394, 1), (key1576, 1), (key1427, 1)]

def rawRow3163 : Integer.Sparse Key := [(key1427, -1), (key1445, -1), (key1319, -1), (key1634, -1), (key1327, -1), (key1625, -1), (key1419, 2), (key1311, 2), (key1617, 2), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1386, -1), (key1419, -1), (key1291, -1), (key1568, -1), (key1311, -1), (key1541, -1), (key1473, -2), (key1352, -2), (key1682, -2), (key1394, 1), (key1427, 1), (key1299, 1), (key1576, 1), (key1319, 1), (key1549, 1)]

def rawRow3164 : Integer.Sparse Key := [(key1445, -1), (key1427, -1), (key1634, -1), (key1319, -1), (key1625, -1), (key1327, -1), (key1419, 2), (key1617, 2), (key1311, 2), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1), (key1419, -1), (key1386, -1), (key1568, -1), (key1291, -1), (key1541, -1), (key1311, -1), (key1473, -2), (key1682, -2), (key1352, -2), (key1427, 1), (key1394, 1), (key1576, 1), (key1299, 1), (key1549, 1), (key1319, 1)]

def rawRow3165 : Integer.Sparse Key := [(key1625, -1), (key1634, -1), (key1327, -1), (key1445, -1), (key1319, -1), (key1427, -1), (key1617, 2), (key1311, 2), (key1419, 2), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1), (key1541, -1), (key1568, -1), (key1311, -1), (key1419, -1), (key1291, -1), (key1386, -1), (key1682, -2), (key1352, -2), (key1473, -2), (key1549, 1), (key1576, 1), (key1319, 1), (key1427, 1), (key1299, 1), (key1394, 1)]

def rawRow3166 : Integer.Sparse Key := [(key1634, -1), (key1625, -1), (key1445, -1), (key1327, -1), (key1427, -1), (key1319, -1), (key1617, 2), (key1419, 2), (key1311, 2), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1), (key1568, -1), (key1541, -1), (key1419, -1), (key1311, -1), (key1386, -1), (key1291, -1), (key1682, -2), (key1473, -2), (key1352, -2), (key1576, 1), (key1549, 1), (key1427, 1), (key1319, 1), (key1394, 1), (key1299, 1)]

def rawRow3167 : Integer.Sparse Key := [(key1352, -1), (key1352, -1), (key1682, -1), (key1682, -1), (key1690, -1), (key1690, -1), (key1355, 2), (key1684, 2), (key1684, 2), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1), (key1327, -1), (key1327, -1), (key1557, -1), (key1557, -1), (key1625, -1), (key1625, -1), (key1291, -2), (key1568, -2), (key1568, -2), (key1311, 1), (key1311, 1), (key1541, 1), (key1541, 1), (key1617, 1), (key1617, 1)]

def rawRow3168 : Integer.Sparse Key := [(key1682, -1), (key1690, -1), (key1352, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1684, 2), (key1355, 2), (key1684, 2), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1557, -1), (key1625, -1), (key1327, -1), (key1625, -1), (key1327, -1), (key1557, -1), (key1568, -2), (key1291, -2), (key1568, -2), (key1541, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1541, 1)]

def rawRow3169 : Integer.Sparse Key := [(key1690, -1), (key1682, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1352, -1), (key1684, 2), (key1684, 2), (key1355, 2), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1), (key1625, -1), (key1557, -1), (key1625, -1), (key1327, -1), (key1557, -1), (key1327, -1), (key1568, -2), (key1568, -2), (key1291, -2), (key1617, 1), (key1541, 1), (key1617, 1), (key1311, 1), (key1541, 1), (key1311, 1)]

def rawRow3170 : Integer.Sparse Key := [(key1352, -1), (key1355, -1), (key1473, -1), (key1684, -1), (key1481, -1), (key1690, -1), (key1352, 2), (key1473, 2), (key1682, 2), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1), (key1299, -1), (key1319, -1), (key1394, -1), (key1549, -1), (key1427, -1), (key1576, -1), (key1311, -2), (key1419, -2), (key1617, -2), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

def rawRow3171 : Integer.Sparse Key := [(key1355, -1), (key1352, -1), (key1684, -1), (key1473, -1), (key1690, -1), (key1481, -1), (key1352, 2), (key1682, 2), (key1473, 2), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1), (key1319, -1), (key1299, -1), (key1549, -1), (key1394, -1), (key1576, -1), (key1427, -1), (key1311, -2), (key1617, -2), (key1419, -2), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

def rawRow3172 : Integer.Sparse Key := [(key1473, -1), (key1481, -1), (key1352, -1), (key1690, -1), (key1355, -1), (key1684, -1), (key1473, 2), (key1352, 2), (key1682, 2), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1394, -1), (key1427, -1), (key1299, -1), (key1576, -1), (key1319, -1), (key1549, -1), (key1419, -2), (key1311, -2), (key1617, -2), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

def rawRow3173 : Integer.Sparse Key := [(key1481, -1), (key1473, -1), (key1690, -1), (key1352, -1), (key1684, -1), (key1355, -1), (key1473, 2), (key1682, 2), (key1352, 2), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1), (key1427, -1), (key1394, -1), (key1576, -1), (key1299, -1), (key1549, -1), (key1319, -1), (key1419, -2), (key1617, -2), (key1311, -2), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

def rawRow3174 : Integer.Sparse Key := [(key1684, -1), (key1690, -1), (key1355, -1), (key1481, -1), (key1352, -1), (key1473, -1), (key1682, 2), (key1352, 2), (key1473, 2), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1), (key1549, -1), (key1576, -1), (key1319, -1), (key1427, -1), (key1299, -1), (key1394, -1), (key1617, -2), (key1311, -2), (key1419, -2), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

def rawRow3175 : Integer.Sparse Key := [(key1690, -1), (key1684, -1), (key1481, -1), (key1355, -1), (key1473, -1), (key1352, -1), (key1682, 2), (key1473, 2), (key1352, 2), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1), (key1576, -1), (key1549, -1), (key1427, -1), (key1319, -1), (key1394, -1), (key1299, -1), (key1617, -2), (key1419, -2), (key1311, -2), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow3176 : Integer.Sparse Key := [(key2679, -2), (key2691, -2), (key3014, -2), (key2684, 2), (key2691, 2), (key2820, 2), (key2710, 2), (key2717, 2), (key3024, 2), (key2717, -6), (key2754, -2), (key2755, -2), (key2921, -2), (key2755, 6)]

def rawRow3177 : Integer.Sparse Key := [(key2691, -2), (key2679, -2), (key3014, -2), (key2691, 2), (key2684, 2), (key2820, 2), (key2717, 2), (key2710, 2), (key3024, 2), (key2717, -6), (key2755, -2), (key2754, -2), (key2921, -2), (key2755, 6)]

def rawRow3178 : Integer.Sparse Key := [(key3047, -2), (key3115, -2), (key2691, -2), (key2684, 2), (key2820, 2), (key2691, 2), (key2710, 2), (key3024, 2), (key2717, 2), (key2717, -6), (key2754, -2), (key2921, -2), (key2755, -2), (key2755, 6)]

def rawRow3179 : Integer.Sparse Key := [(key3115, -2), (key3047, -2), (key2691, -2), (key2820, 2), (key2684, 2), (key2691, 2), (key3024, 2), (key2710, 2), (key2717, 2), (key2717, -6), (key2921, -2), (key2754, -2), (key2755, -2), (key2755, 6)]

def rawRow3180 : Integer.Sparse Key := [(key3058, -2), (key3115, -2), (key2679, -2), (key2691, 2), (key2820, 2), (key2684, 2), (key2717, 2), (key3024, 2), (key2710, 2), (key2717, -6), (key2755, -2), (key2921, -2), (key2754, -2), (key2755, 6)]

def rawRow3181 : Integer.Sparse Key := [(key3115, -2), (key3058, -2), (key3047, -2), (key2820, 2), (key2691, 2), (key2684, 2), (key3024, 2), (key2717, 2), (key2710, 2), (key2717, -6), (key2921, -2), (key2755, -2), (key2754, -2), (key2755, 6)]

def rawRow3182 : Integer.Sparse Key := [(key3053, -2), (key3053, -2), (key3105, -2), (key2679, 2), (key2679, 2), (key2813, 2), (key2717, 2), (key2717, 2), (key3024, 2), (key2710, -6), (key2755, -2), (key2755, -2), (key2921, -2), (key2754, 6)]

def rawRow3183 : Integer.Sparse Key := [(key3053, -2), (key3105, -2), (key3053, -2), (key3047, 2), (key3096, 2), (key2679, 2), (key2717, 2), (key3024, 2), (key2717, 2), (key2710, -6), (key2755, -2), (key2921, -2), (key2755, -2), (key2754, 6)]

def rawRow3184 : Integer.Sparse Key := [(key3105, -2), (key3053, -2), (key3053, -2), (key3096, 2), (key3047, 2), (key3047, 2), (key3024, 2), (key2717, 2), (key2717, 2), (key2710, -6), (key2921, -2), (key2755, -2), (key2755, -2), (key2754, 6)]

def rawRow3185 : Integer.Sparse Key := [(key3061, -2), (key3075, -2), (key3143, -2), (key3068, 2), (key3076, 2), (key3142, 2), (key2679, 2), (key2691, 2), (key3014, 2), (key2755, -6), (key2684, -2), (key2691, -2), (key2820, -2), (key2717, 6)]

def rawRow3186 : Integer.Sparse Key := [(key3075, -2), (key3061, -2), (key3143, -2), (key3076, 2), (key3068, 2), (key3142, 2), (key2691, 2), (key2679, 2), (key3014, 2), (key2755, -6), (key2691, -2), (key2684, -2), (key2820, -2), (key2717, 6)]

def rawRow3187 : Integer.Sparse Key := [(key3061, -2), (key3143, -2), (key3075, -2), (key3068, 2), (key3142, 2), (key3076, 2), (key3047, 2), (key3115, 2), (key2691, 2), (key2755, -6), (key2684, -2), (key2820, -2), (key2691, -2), (key2717, 6)]

def rawRow3188 : Integer.Sparse Key := [(key3143, -2), (key3061, -2), (key3075, -2), (key3142, 2), (key3068, 2), (key3076, 2), (key3115, 2), (key3047, 2), (key2691, 2), (key2755, -6), (key2820, -2), (key2684, -2), (key2691, -2), (key2717, 6)]

def rawRow3189 : Integer.Sparse Key := [(key3075, -2), (key3143, -2), (key3061, -2), (key3076, 2), (key3142, 2), (key3068, 2), (key3058, 2), (key3115, 2), (key2679, 2), (key2755, -6), (key2691, -2), (key2820, -2), (key2684, -2), (key2717, 6)]

def rawRow3190 : Integer.Sparse Key := [(key3143, -2), (key3075, -2), (key3061, -2), (key3142, 2), (key3076, 2), (key3068, 2), (key3115, 2), (key3058, 2), (key3047, 2), (key2755, -6), (key2820, -2), (key2691, -2), (key2684, -2), (key2717, 6)]

def rawRow3191 : Integer.Sparse Key := [(key3053, -2), (key3068, -2), (key3105, -2), (key3047, 2), (key3061, 2), (key3096, 2), (key3058, 2), (key3076, 2), (key3115, 2), (key2679, -6), (key2691, -2), (key2717, -2), (key2820, -2), (key2684, 6)]

def rawRow3192 : Integer.Sparse Key := [(key3068, -2), (key3053, -2), (key3105, -2), (key3061, 2), (key3047, 2), (key3096, 2), (key3076, 2), (key3058, 2), (key3115, 2), (key2679, -6), (key2717, -2), (key2691, -2), (key2820, -2), (key2684, 6)]

def rawRow3193 : Integer.Sparse Key := [(key3053, -2), (key3105, -2), (key3068, -2), (key3047, 2), (key3096, 2), (key3061, 2), (key3058, 2), (key3115, 2), (key3076, 2), (key2679, -6), (key2691, -2), (key2820, -2), (key2717, -2), (key2684, 6)]

def rawRow3194 : Integer.Sparse Key := [(key3105, -2), (key3053, -2), (key3068, -2), (key3096, 2), (key3047, 2), (key3061, 2), (key3115, 2), (key3058, 2), (key3076, 2), (key3047, -6), (key2820, -2), (key2691, -2), (key2717, -2), (key2684, 6)]

def rawRow3195 : Integer.Sparse Key := [(key3068, -2), (key3105, -2), (key3053, -2), (key3061, 2), (key3096, 2), (key3047, 2), (key3076, 2), (key3115, 2), (key3058, 2), (key3047, -6), (key2717, -2), (key2820, -2), (key2691, -2), (key2684, 6)]

def rawRow3196 : Integer.Sparse Key := [(key3105, -2), (key3068, -2), (key3053, -2), (key3096, 2), (key3061, 2), (key3047, 2), (key3115, 2), (key3076, 2), (key3058, 2), (key3047, -6), (key2820, -2), (key2717, -2), (key2691, -2), (key2684, 6)]

def rawRow3197 : Integer.Sparse Key := [(key3075, -2), (key3075, -2), (key3143, -2), (key3076, 2), (key3076, 2), (key3142, 2), (key3053, 2), (key3053, 2), (key3105, 2), (key3068, -6), (key2679, -2), (key2679, -2), (key2813, -2), (key2710, 6)]

def rawRow3198 : Integer.Sparse Key := [(key3075, -2), (key3143, -2), (key3075, -2), (key3076, 2), (key3142, 2), (key3076, 2), (key3053, 2), (key3105, 2), (key3053, 2), (key3068, -6), (key3047, -2), (key3096, -2), (key2679, -2), (key2710, 6)]

def rawRow3199 : Integer.Sparse Key := [(key3143, -2), (key3075, -2), (key3075, -2), (key3142, 2), (key3076, 2), (key3076, 2), (key3105, 2), (key3053, 2), (key3053, 2), (key3068, -6), (key3096, -2), (key3047, -2), (key3047, -2), (key2710, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3200 : Integer.Sparse Key := [(key3058, -2), (key3076, -2), (key3115, -2), (key3058, 2), (key3075, 2), (key3113, 2), (key3053, 2), (key3068, 2), (key3105, 2), (key3053, -6), (key3047, -2), (key3061, -2), (key3096, -2), (key2679, 6)]

def rawRow3201 : Integer.Sparse Key := [(key3076, -2), (key3058, -2), (key3115, -2), (key3075, 2), (key3058, 2), (key3113, 2), (key3068, 2), (key3053, 2), (key3105, 2), (key3053, -6), (key3061, -2), (key3047, -2), (key3096, -2), (key2679, 6)]

def rawRow3202 : Integer.Sparse Key := [(key3058, -2), (key3115, -2), (key3076, -2), (key3058, 2), (key3113, 2), (key3075, 2), (key3053, 2), (key3105, 2), (key3068, 2), (key3053, -6), (key3047, -2), (key3096, -2), (key3061, -2), (key2679, 6)]

def rawRow3203 : Integer.Sparse Key := [(key3115, -2), (key3058, -2), (key3076, -2), (key3113, 2), (key3058, 2), (key3075, 2), (key3105, 2), (key3053, 2), (key3068, 2), (key3053, -6), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, 6)]

def rawRow3204 : Integer.Sparse Key := [(key3076, -2), (key3115, -2), (key3058, -2), (key3075, 2), (key3113, 2), (key3058, 2), (key3068, 2), (key3105, 2), (key3053, 2), (key3053, -6), (key3061, -2), (key3096, -2), (key3047, -2), (key3047, 6)]

def rawRow3205 : Integer.Sparse Key := [(key3115, -2), (key3076, -2), (key3058, -2), (key3113, 2), (key3075, 2), (key3058, 2), (key3105, 2), (key3068, 2), (key3053, 2), (key3053, -6), (key3096, -2), (key3061, -2), (key3047, -2), (key3047, 6)]

def rawRow3206 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1445, -2), (key1386, 1), (key1394, 1), (key1419, 1), (key1473, 1), (key1445, 1), (key1481, 1), (key1568, 2), (key1576, 2), (key1594, 2), (key1291, -1), (key1299, -1), (key1568, -1), (key1904, -1), (key1594, -1), (key1912, -1), (key1541, -1), (key1549, -1), (key1617, -1), (key1682, -1), (key1634, -1), (key1690, -1), (key1311, 1), (key1319, 1), (key1617, 1), (key1919, 1), (key1634, 1), (key1927, 1)]

def rawRow3207 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1445, -2), (key1394, 1), (key1386, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1445, 1), (key1576, 2), (key1568, 2), (key1594, 2), (key1299, -1), (key1291, -1), (key1904, -1), (key1568, -1), (key1912, -1), (key1594, -1), (key1549, -1), (key1541, -1), (key1682, -1), (key1617, -1), (key1690, -1), (key1634, -1), (key1319, 1), (key1311, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1634, 1)]

def rawRow3208 : Integer.Sparse Key := [(key1419, -2), (key1445, -2), (key1427, -2), (key1419, 1), (key1445, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1568, 2), (key1594, 2), (key1576, 2), (key1568, -1), (key1594, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1617, -1), (key1634, -1), (key1541, -1), (key1690, -1), (key1549, -1), (key1682, -1), (key1617, 1), (key1634, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1919, 1)]

def rawRow3209 : Integer.Sparse Key := [(key1445, -2), (key1419, -2), (key1427, -2), (key1445, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1473, 1), (key1394, 1), (key1594, 2), (key1568, 2), (key1576, 2), (key1594, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1904, -1), (key1299, -1), (key1634, -1), (key1617, -1), (key1690, -1), (key1541, -1), (key1682, -1), (key1549, -1), (key1634, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1919, 1), (key1319, 1)]

def rawRow3210 : Integer.Sparse Key := [(key1427, -2), (key1445, -2), (key1419, -2), (key1473, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1386, 1), (key1419, 1), (key1576, 2), (key1594, 2), (key1568, 2), (key1904, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1291, -1), (key1568, -1), (key1682, -1), (key1690, -1), (key1549, -1), (key1634, -1), (key1541, -1), (key1617, -1), (key1919, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1311, 1), (key1617, 1)]

def rawRow3211 : Integer.Sparse Key := [(key1445, -2), (key1427, -2), (key1419, -2), (key1481, 1), (key1473, 1), (key1445, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1594, 2), (key1576, 2), (key1568, 2), (key1912, -1), (key1904, -1), (key1594, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1690, -1), (key1682, -1), (key1634, -1), (key1549, -1), (key1617, -1), (key1541, -1), (key1927, 1), (key1919, 1), (key1634, 1), (key1319, 1), (key1617, 1), (key1311, 1)]

def rawRow3212 : Integer.Sparse Key := [(key1473, -2), (key1473, -2), (key1481, -2), (key1394, 1), (key1394, 1), (key1427, 1), (key1427, 1), (key1445, 1), (key1445, 1), (key1904, 2), (key1904, 2), (key1912, 2), (key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1594, -1), (key1594, -1), (key1897, -1), (key1897, -1), (key1919, -1), (key1919, -1), (key1927, -1), (key1927, -1), (key1352, 1), (key1352, 1), (key1682, 1), (key1682, 1), (key1690, 1), (key1690, 1)]

def rawRow3213 : Integer.Sparse Key := [(key1473, -2), (key1481, -2), (key1473, -2), (key1427, 1), (key1445, 1), (key1394, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1904, 2), (key1912, 2), (key1904, 2), (key1576, -1), (key1594, -1), (key1299, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1919, -1), (key1927, -1), (key1897, -1), (key1927, -1), (key1897, -1), (key1919, -1), (key1682, 1), (key1690, 1), (key1352, 1), (key1690, 1), (key1352, 1), (key1682, 1)]

def rawRow3214 : Integer.Sparse Key := [(key1481, -2), (key1473, -2), (key1473, -2), (key1445, 1), (key1427, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1394, 1), (key1912, 2), (key1904, 2), (key1904, 2), (key1594, -1), (key1576, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1927, -1), (key1919, -1), (key1927, -1), (key1897, -1), (key1919, -1), (key1897, -1), (key1690, 1), (key1682, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1352, 1)]

def rawRow3215 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1594, -2), (key1541, 1), (key1549, 1), (key1617, 1), (key1682, 1), (key1634, 1), (key1690, 1), (key1419, 2), (key1427, 2), (key1445, 2), (key1311, -1), (key1319, -1), (key1617, -1), (key1919, -1), (key1634, -1), (key1927, -1), (key1386, -1), (key1394, -1), (key1419, -1), (key1473, -1), (key1445, -1), (key1481, -1), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1)]

def rawRow3216 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1594, -2), (key1549, 1), (key1541, 1), (key1682, 1), (key1617, 1), (key1690, 1), (key1634, 1), (key1427, 2), (key1419, 2), (key1445, 2), (key1319, -1), (key1311, -1), (key1919, -1), (key1617, -1), (key1927, -1), (key1634, -1), (key1394, -1), (key1386, -1), (key1473, -1), (key1419, -1), (key1481, -1), (key1445, -1), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1)]

def rawRow3217 : Integer.Sparse Key := [(key1568, -2), (key1594, -2), (key1576, -2), (key1617, 1), (key1634, 1), (key1541, 1), (key1690, 1), (key1549, 1), (key1682, 1), (key1419, 2), (key1445, 2), (key1427, 2), (key1617, -1), (key1634, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1419, -1), (key1445, -1), (key1386, -1), (key1481, -1), (key1394, -1), (key1473, -1), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1)]

def rawRow3218 : Integer.Sparse Key := [(key1594, -2), (key1568, -2), (key1576, -2), (key1634, 1), (key1617, 1), (key1690, 1), (key1541, 1), (key1682, 1), (key1549, 1), (key1445, 2), (key1419, 2), (key1427, 2), (key1634, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1919, -1), (key1319, -1), (key1445, -1), (key1419, -1), (key1481, -1), (key1386, -1), (key1473, -1), (key1394, -1), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1)]

def rawRow3219 : Integer.Sparse Key := [(key1576, -2), (key1594, -2), (key1568, -2), (key1682, 1), (key1690, 1), (key1549, 1), (key1634, 1), (key1541, 1), (key1617, 1), (key1427, 2), (key1445, 2), (key1419, 2), (key1919, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1311, -1), (key1617, -1), (key1473, -1), (key1481, -1), (key1394, -1), (key1445, -1), (key1386, -1), (key1419, -1), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1)]

def rawRow3220 : Integer.Sparse Key := [(key1594, -2), (key1576, -2), (key1568, -2), (key1690, 1), (key1682, 1), (key1634, 1), (key1549, 1), (key1617, 1), (key1541, 1), (key1445, 2), (key1427, 2), (key1419, 2), (key1927, -1), (key1919, -1), (key1634, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1481, -1), (key1473, -1), (key1445, -1), (key1394, -1), (key1419, -1), (key1386, -1), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1)]

def rawRow3221 : Integer.Sparse Key := [(key1682, -2), (key1684, -2), (key1690, -2), (key1549, 1), (key1557, 1), (key1576, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1919, 2), (key1921, 2), (key1927, 2), (key1319, -1), (key1327, -1), (key1427, -1), (key1625, -1), (key1445, -1), (key1634, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1921, -1), (key1912, -1), (key1927, -1), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1)]

def rawRow3222 : Integer.Sparse Key := [(key1684, -2), (key1682, -2), (key1690, -2), (key1557, 1), (key1549, 1), (key1625, 1), (key1576, 1), (key1634, 1), (key1594, 1), (key1921, 2), (key1919, 2), (key1927, 2), (key1327, -1), (key1319, -1), (key1625, -1), (key1427, -1), (key1634, -1), (key1445, -1), (key1900, -1), (key1897, -1), (key1921, -1), (key1904, -1), (key1927, -1), (key1912, -1), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1)]

def rawRow3223 : Integer.Sparse Key := [(key1682, -2), (key1690, -2), (key1684, -2), (key1576, 1), (key1594, 1), (key1549, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1919, 2), (key1927, 2), (key1921, 2), (key1427, -1), (key1445, -1), (key1319, -1), (key1634, -1), (key1327, -1), (key1625, -1), (key1904, -1), (key1912, -1), (key1897, -1), (key1927, -1), (key1900, -1), (key1921, -1), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1)]

def rawRow3224 : Integer.Sparse Key := [(key1690, -2), (key1682, -2), (key1684, -2), (key1594, 1), (key1576, 1), (key1634, 1), (key1549, 1), (key1625, 1), (key1557, 1), (key1927, 2), (key1919, 2), (key1921, 2), (key1445, -1), (key1427, -1), (key1634, -1), (key1319, -1), (key1625, -1), (key1327, -1), (key1912, -1), (key1904, -1), (key1927, -1), (key1897, -1), (key1921, -1), (key1900, -1), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1)]

def rawRow3225 : Integer.Sparse Key := [(key1684, -2), (key1690, -2), (key1682, -2), (key1625, 1), (key1634, 1), (key1557, 1), (key1594, 1), (key1549, 1), (key1576, 1), (key1921, 2), (key1927, 2), (key1919, 2), (key1625, -1), (key1634, -1), (key1327, -1), (key1445, -1), (key1319, -1), (key1427, -1), (key1921, -1), (key1927, -1), (key1900, -1), (key1912, -1), (key1897, -1), (key1904, -1), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1)]

def rawRow3226 : Integer.Sparse Key := [(key1690, -2), (key1684, -2), (key1682, -2), (key1634, 1), (key1625, 1), (key1594, 1), (key1557, 1), (key1576, 1), (key1549, 1), (key1927, 2), (key1921, 2), (key1919, 2), (key1634, -1), (key1625, -1), (key1445, -1), (key1327, -1), (key1427, -1), (key1319, -1), (key1927, -1), (key1921, -1), (key1912, -1), (key1900, -1), (key1904, -1), (key1897, -1), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1)]

def rawRow3227 : Integer.Sparse Key := [(key1904, -2), (key1904, -2), (key1912, -2), (key1897, 1), (key1897, 1), (key1919, 1), (key1919, 1), (key1927, 1), (key1927, 1), (key1473, 2), (key1473, 2), (key1481, 2), (key1352, -1), (key1352, -1), (key1682, -1), (key1682, -1), (key1690, -1), (key1690, -1), (key1394, -1), (key1394, -1), (key1427, -1), (key1427, -1), (key1445, -1), (key1445, -1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1)]

def rawRow3228 : Integer.Sparse Key := [(key1904, -2), (key1912, -2), (key1904, -2), (key1919, 1), (key1927, 1), (key1897, 1), (key1927, 1), (key1897, 1), (key1919, 1), (key1473, 2), (key1481, 2), (key1473, 2), (key1682, -1), (key1690, -1), (key1352, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1427, -1), (key1445, -1), (key1394, -1), (key1445, -1), (key1394, -1), (key1427, -1), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1)]

def rawRow3229 : Integer.Sparse Key := [(key1912, -2), (key1904, -2), (key1904, -2), (key1927, 1), (key1919, 1), (key1927, 1), (key1897, 1), (key1919, 1), (key1897, 1), (key1481, 2), (key1473, 2), (key1473, 2), (key1690, -1), (key1682, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1352, -1), (key1445, -1), (key1427, -1), (key1445, -1), (key1394, -1), (key1427, -1), (key1394, -1), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1)]

def rawRow3230 : Integer.Sparse Key := [(key1919, -2), (key1921, -2), (key1927, -2), (key1897, 1), (key1900, 1), (key1904, 1), (key1921, 1), (key1912, 1), (key1927, 1), (key1682, 2), (key1684, 2), (key1690, 2), (key1352, -1), (key1355, -1), (key1473, -1), (key1684, -1), (key1481, -1), (key1690, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1625, -1), (key1594, -1), (key1634, -1), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1)]

def rawRow3231 : Integer.Sparse Key := [(key1921, -2), (key1919, -2), (key1927, -2), (key1900, 1), (key1897, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1912, 1), (key1684, 2), (key1682, 2), (key1690, 2), (key1355, -1), (key1352, -1), (key1684, -1), (key1473, -1), (key1690, -1), (key1481, -1), (key1557, -1), (key1549, -1), (key1625, -1), (key1576, -1), (key1634, -1), (key1594, -1), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1)]

def rawRow3232 : Integer.Sparse Key := [(key1919, -2), (key1927, -2), (key1921, -2), (key1904, 1), (key1912, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1682, 2), (key1690, 2), (key1684, 2), (key1473, -1), (key1481, -1), (key1352, -1), (key1690, -1), (key1355, -1), (key1684, -1), (key1576, -1), (key1594, -1), (key1549, -1), (key1634, -1), (key1557, -1), (key1625, -1), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1)]

def rawRow3233 : Integer.Sparse Key := [(key1927, -2), (key1919, -2), (key1921, -2), (key1912, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1921, 1), (key1900, 1), (key1690, 2), (key1682, 2), (key1684, 2), (key1481, -1), (key1473, -1), (key1690, -1), (key1352, -1), (key1684, -1), (key1355, -1), (key1594, -1), (key1576, -1), (key1634, -1), (key1549, -1), (key1625, -1), (key1557, -1), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1)]

def rawRow3234 : Integer.Sparse Key := [(key1921, -2), (key1927, -2), (key1919, -2), (key1921, 1), (key1927, 1), (key1900, 1), (key1912, 1), (key1897, 1), (key1904, 1), (key1684, 2), (key1690, 2), (key1682, 2), (key1684, -1), (key1690, -1), (key1355, -1), (key1481, -1), (key1352, -1), (key1473, -1), (key1625, -1), (key1634, -1), (key1557, -1), (key1594, -1), (key1549, -1), (key1576, -1), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1)]

def rawRow3235 : Integer.Sparse Key := [(key1927, -2), (key1921, -2), (key1919, -2), (key1927, 1), (key1921, 1), (key1912, 1), (key1900, 1), (key1904, 1), (key1897, 1), (key1690, 2), (key1684, 2), (key1682, 2), (key1690, -1), (key1684, -1), (key1481, -1), (key1355, -1), (key1473, -1), (key1352, -1), (key1634, -1), (key1625, -1), (key1594, -1), (key1557, -1), (key1576, -1), (key1549, -1), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1)]

def rawRow3236 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1070, -2), (key1035, 6), (key1107, 2), (key1113, 2), (key1149, 2), (key1000, -2), (key1113, -2), (key1231, -2), (key1122, -6), (key1014, 2), (key1122, 2), (key1234, 2)]

def rawRow3237 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1070, -2), (key1035, 6), (key1113, 2), (key1107, 2), (key1149, 2), (key1000, -2), (key1231, -2), (key1113, -2), (key1122, -6), (key1014, 2), (key1234, 2), (key1122, 2)]

def rawRow3238 : Integer.Sparse Key := [(key1029, -2), (key1070, -2), (key1035, -2), (key1035, 6), (key1107, 2), (key1149, 2), (key1113, 2), (key1113, -2), (key1000, -2), (key1231, -2), (key1122, -6), (key1122, 2), (key1014, 2), (key1234, 2)]

def rawRow3239 : Integer.Sparse Key := [(key1070, -2), (key1029, -2), (key1035, -2), (key1035, 6), (key1149, 2), (key1107, 2), (key1113, 2), (key1113, -2), (key1231, -2), (key1000, -2), (key1122, -6), (key1122, 2), (key1234, 2), (key1014, 2)]

def rawRow3240 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1029, -2), (key1035, 6), (key1113, 2), (key1149, 2), (key1107, 2), (key1231, -2), (key1000, -2), (key1113, -2), (key1122, -6), (key1234, 2), (key1014, 2), (key1122, 2)]

def rawRow3241 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1029, -2), (key1035, 6), (key1149, 2), (key1113, 2), (key1107, 2), (key1231, -2), (key1113, -2), (key1000, -2), (key1122, -6), (key1234, 2), (key1122, 2), (key1014, 2)]

def rawRow3242 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1070, -2), (key1029, 6), (key1231, 2), (key1231, 2), (key1241, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1234, -6), (key1014, 2), (key1122, 2), (key1122, 2)]

def rawRow3243 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1035, -2), (key1029, 6), (key1231, 2), (key1241, 2), (key1231, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1234, -6), (key1122, 2), (key1014, 2), (key1122, 2)]

def rawRow3244 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1035, -2), (key1029, 6), (key1241, 2), (key1231, 2), (key1231, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1234, -6), (key1122, 2), (key1122, 2), (key1014, 2)]

def rawRow3245 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1149, -2), (key1122, 6), (key1029, 2), (key1035, 2), (key1070, 2), (key1014, -2), (key1122, -2), (key1234, -2), (key1035, -6), (key1000, 2), (key1113, 2), (key1231, 2)]

def rawRow3246 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1149, -2), (key1122, 6), (key1035, 2), (key1029, 2), (key1070, 2), (key1014, -2), (key1234, -2), (key1122, -2), (key1035, -6), (key1000, 2), (key1231, 2), (key1113, 2)]

def rawRow3247 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1113, -2), (key1122, 6), (key1029, 2), (key1070, 2), (key1035, 2), (key1122, -2), (key1014, -2), (key1234, -2), (key1035, -6), (key1113, 2), (key1000, 2), (key1231, 2)]

def rawRow3248 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1113, -2), (key1122, 6), (key1070, 2), (key1029, 2), (key1035, 2), (key1122, -2), (key1234, -2), (key1014, -2), (key1035, -6), (key1113, 2), (key1231, 2), (key1000, 2)]

def rawRow3249 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1107, -2), (key1122, 6), (key1035, 2), (key1070, 2), (key1029, 2), (key1234, -2), (key1014, -2), (key1122, -2), (key1035, -6), (key1231, 2), (key1000, 2), (key1113, 2)]

def rawRow3250 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1107, -2), (key1122, 6), (key1070, 2), (key1035, 2), (key1029, 2), (key1234, -2), (key1122, -2), (key1014, -2), (key1035, -6), (key1231, 2), (key1113, 2), (key1000, 2)]

def rawRow3251 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1149, -2), (key1107, 6), (key1231, 2), (key1234, 2), (key1241, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1231, -6), (key1000, 2), (key1035, 2), (key1113, 2)]

def rawRow3252 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1149, -2), (key1107, 6), (key1234, 2), (key1231, 2), (key1241, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1231, -6), (key1000, 2), (key1113, 2), (key1035, 2)]

def rawRow3253 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1122, -2), (key1107, 6), (key1231, 2), (key1241, 2), (key1234, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1231, -6), (key1035, 2), (key1000, 2), (key1113, 2)]

def rawRow3254 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1122, -2), (key1107, 6), (key1241, 2), (key1231, 2), (key1234, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1231, -6), (key1035, 2), (key1113, 2), (key1000, 2)]

def rawRow3255 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1113, -2), (key1107, 6), (key1234, 2), (key1241, 2), (key1231, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1231, -6), (key1113, 2), (key1000, 2), (key1035, 2)]

def rawRow3256 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1113, -2), (key1107, 6), (key1241, 2), (key1234, 2), (key1231, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1231, -6), (key1113, 2), (key1035, 2), (key1000, 2)]

def rawRow3257 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1241, -2), (key1234, 6), (key1035, 2), (key1035, 2), (key1070, 2), (key1014, -2), (key1122, -2), (key1122, -2), (key1029, -6), (key994, 2), (key1107, 2), (key1107, 2)]

def rawRow3258 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1231, -2), (key1234, 6), (key1035, 2), (key1070, 2), (key1035, 2), (key1122, -2), (key1014, -2), (key1122, -2), (key1029, -6), (key1107, 2), (key994, 2), (key1107, 2)]

def rawRow3259 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1231, -2), (key1234, 6), (key1070, 2), (key1035, 2), (key1035, 2), (key1122, -2), (key1122, -2), (key1014, -2), (key1029, -6), (key1107, 2), (key1107, 2), (key994, 2)]

def rawRow3260 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1241, -2), (key1231, 6), (key1113, 2), (key1122, 2), (key1149, 2), (key1000, -2), (key1035, -2), (key1113, -2), (key1107, -6), (key994, 2), (key1029, 2), (key1107, 2)]

def rawRow3261 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1241, -2), (key1231, 6), (key1122, 2), (key1113, 2), (key1149, 2), (key1000, -2), (key1113, -2), (key1035, -2), (key1107, -6), (key994, 2), (key1107, 2), (key1029, 2)]

def rawRow3262 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1234, -2), (key1231, 6), (key1113, 2), (key1149, 2), (key1122, 2), (key1035, -2), (key1000, -2), (key1113, -2), (key1107, -6), (key1029, 2), (key994, 2), (key1107, 2)]

def rawRow3263 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1234, -2), (key1231, 6), (key1149, 2), (key1113, 2), (key1122, 2), (key1035, -2), (key1113, -2), (key1000, -2), (key1107, -6), (key1029, 2), (key1107, 2), (key994, 2)]

def rawRow3264 : Integer.Sparse Key := [(key1234, -2), (key1241, -2), (key1231, -2), (key1231, 6), (key1122, 2), (key1149, 2), (key1113, 2), (key1113, -2), (key1000, -2), (key1035, -2), (key1107, -6), (key1107, 2), (key994, 2), (key1029, 2)]

def rawRow3265 : Integer.Sparse Key := [(key1241, -2), (key1234, -2), (key1231, -2), (key1231, 6), (key1149, 2), (key1122, 2), (key1113, 2), (key1113, -2), (key1035, -2), (key1000, -2), (key1107, -6), (key1107, 2), (key1029, 2), (key994, 2)]

def rawRow3266 : Integer.Sparse Key := [(key2671, -2), (key2726, -2), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, 1), (key2753, 1), (key2732, 1), (key2758, 1), (key2702, 2), (key2972, 2), (key2976, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2728, -1), (key2976, -1), (key2983, -1), (key2735, -1), (key2737, -1), (key2893, -1), (key2897, -1), (key2997, -1), (key2998, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2747, 1), (key2998, 1), (key3000, 1)]

def rawRow3267 : Integer.Sparse Key := [(key2671, -2), (key2758, -2), (key2726, -2), (key2676, 1), (key2671, 1), (key2753, 1), (key2706, 1), (key2758, 1), (key2732, 1), (key2702, 2), (key2976, 2), (key2972, 2), (key2641, -1), (key2628, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2976, -1), (key2737, -1), (key2735, -1), (key2897, -1), (key2893, -1), (key2998, -1), (key2997, -1), (key2653, 1), (key2646, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2998, 1)]

def rawRow3268 : Integer.Sparse Key := [(key2726, -2), (key2671, -2), (key2758, -2), (key2706, 1), (key2732, 1), (key2671, 1), (key2758, 1), (key2676, 1), (key2753, 1), (key2972, 2), (key2702, 2), (key2976, 2), (key2702, -1), (key2976, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2893, -1), (key2997, -1), (key2735, -1), (key2998, -1), (key2737, -1), (key2897, -1), (key2735, 1), (key2998, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2747, 1)]

def rawRow3269 : Integer.Sparse Key := [(key2726, -2), (key2758, -2), (key2671, -2), (key2732, 1), (key2706, 1), (key2758, 1), (key2671, 1), (key2753, 1), (key2676, 1), (key2972, 2), (key2976, 2), (key2702, 2), (key2976, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2728, -1), (key2641, -1), (key2997, -1), (key2893, -1), (key2998, -1), (key2735, -1), (key2897, -1), (key2737, -1), (key2998, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2747, 1), (key2653, 1)]

def rawRow3270 : Integer.Sparse Key := [(key2758, -2), (key2671, -2), (key2726, -2), (key2753, 1), (key2758, 1), (key2676, 1), (key2732, 1), (key2671, 1), (key2706, 1), (key2976, 2), (key2702, 2), (key2972, 2), (key2728, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2628, -1), (key2702, -1), (key2897, -1), (key2998, -1), (key2737, -1), (key2997, -1), (key2735, -1), (key2893, -1), (key2747, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2646, 1), (key2735, 1)]

def rawRow3271 : Integer.Sparse Key := [(key2758, -2), (key2726, -2), (key2671, -2), (key2758, 1), (key2753, 1), (key2732, 1), (key2676, 1), (key2706, 1), (key2671, 1), (key2976, 2), (key2972, 2), (key2702, 2), (key2983, -1), (key2728, -1), (key2976, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2998, -1), (key2897, -1), (key2997, -1), (key2737, -1), (key2893, -1), (key2735, -1), (key3000, 1), (key2747, 1), (key2998, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

def rawRow3272 : Integer.Sparse Key := [(key2676, -2), (key2732, -2), (key2732, -2), (key2671, 1), (key2671, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2728, 2), (key2983, 2), (key2983, 2), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2747, -1), (key2747, -1), (key2904, -1), (key2904, -1), (key3000, -1), (key3000, -1), (key2648, 1), (key2648, 1), (key2737, 1), (key2737, 1), (key2997, 1), (key2997, 1)]

def rawRow3273 : Integer.Sparse Key := [(key2732, -2), (key2676, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2983, 2), (key2728, 2), (key2983, 2), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2904, -1), (key3000, -1), (key2747, -1), (key3000, -1), (key2747, -1), (key2904, -1), (key2737, 1), (key2997, 1), (key2648, 1), (key2997, 1), (key2648, 1), (key2737, 1)]

def rawRow3274 : Integer.Sparse Key := [(key2732, -2), (key2732, -2), (key2676, -2), (key2726, 1), (key2706, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2671, 1), (key2983, 2), (key2983, 2), (key2728, 2), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2904, -1), (key3000, -1), (key2747, -1), (key2904, -1), (key2747, -1), (key2997, 1), (key2737, 1), (key2997, 1), (key2648, 1), (key2737, 1), (key2648, 1)]

def rawRow3275 : Integer.Sparse Key := [(key2786, -2), (key2870, -2), (key2923, -2), (key2794, 1), (key2798, 1), (key2860, 1), (key2920, 1), (key2885, 1), (key2927, 1), (key2671, 2), (key2726, 2), (key2758, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2747, -1), (key2998, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2782, -1), (key2795, -1), (key2938, -1), (key2943, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2728, 1), (key2976, 1), (key2983, 1)]

def rawRow3276 : Integer.Sparse Key := [(key2786, -2), (key2923, -2), (key2870, -2), (key2798, 1), (key2794, 1), (key2920, 1), (key2860, 1), (key2927, 1), (key2885, 1), (key2671, 2), (key2758, 2), (key2726, 2), (key2653, -1), (key2646, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2998, -1), (key2673, -1), (key2667, -1), (key2795, -1), (key2782, -1), (key2943, -1), (key2938, -1), (key2641, 1), (key2628, 1), (key2728, 1), (key2702, 1), (key2983, 1), (key2976, 1)]

def rawRow3277 : Integer.Sparse Key := [(key2870, -2), (key2786, -2), (key2923, -2), (key2860, 1), (key2885, 1), (key2794, 1), (key2927, 1), (key2798, 1), (key2920, 1), (key2726, 2), (key2671, 2), (key2758, 2), (key2735, -1), (key2998, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2782, -1), (key2938, -1), (key2667, -1), (key2943, -1), (key2673, -1), (key2795, -1), (key2702, 1), (key2976, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2728, 1)]

def rawRow3278 : Integer.Sparse Key := [(key2870, -2), (key2923, -2), (key2786, -2), (key2885, 1), (key2860, 1), (key2927, 1), (key2794, 1), (key2920, 1), (key2798, 1), (key2726, 2), (key2758, 2), (key2671, 2), (key2998, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2747, -1), (key2653, -1), (key2938, -1), (key2782, -1), (key2943, -1), (key2667, -1), (key2795, -1), (key2673, -1), (key2976, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2728, 1), (key2641, 1)]

def rawRow3279 : Integer.Sparse Key := [(key2923, -2), (key2786, -2), (key2870, -2), (key2920, 1), (key2927, 1), (key2798, 1), (key2885, 1), (key2794, 1), (key2860, 1), (key2758, 2), (key2671, 2), (key2726, 2), (key2747, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2646, -1), (key2735, -1), (key2795, -1), (key2943, -1), (key2673, -1), (key2938, -1), (key2667, -1), (key2782, -1), (key2728, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2628, 1), (key2702, 1)]

def rawRow3280 : Integer.Sparse Key := [(key2923, -2), (key2870, -2), (key2786, -2), (key2927, 1), (key2920, 1), (key2885, 1), (key2798, 1), (key2860, 1), (key2794, 1), (key2758, 2), (key2726, 2), (key2671, 2), (key3000, -1), (key2747, -1), (key2998, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2943, -1), (key2795, -1), (key2938, -1), (key2673, -1), (key2782, -1), (key2667, -1), (key2983, 1), (key2728, 1), (key2976, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

def rawRow3281 : Integer.Sparse Key := [(key2798, -2), (key2835, -2), (key2885, -2), (key2786, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2829, 1), (key2870, 1), (key3010, 2), (key3017, 2), (key3030, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2728, -1), (key2747, -1), (key2831, -1), (key2904, -1), (key2960, -1), (key2983, -1), (key2618, 1), (key2648, 1), (key2673, 1), (key2737, 1), (key2938, 1), (key2950, 1)]

def rawRow3282 : Integer.Sparse Key := [(key2798, -2), (key2885, -2), (key2835, -2), (key2794, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, 1), (key2829, 1), (key3010, 2), (key3030, 2), (key3017, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2747, -1), (key2728, -1), (key2904, -1), (key2831, -1), (key2983, -1), (key2960, -1), (key2648, 1), (key2618, 1), (key2737, 1), (key2673, 1), (key2950, 1), (key2938, 1)]

def rawRow3283 : Integer.Sparse Key := [(key2835, -2), (key2798, -2), (key2885, -2), (key2809, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2794, 1), (key2860, 1), (key3017, 2), (key3010, 2), (key3030, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2831, -1), (key2960, -1), (key2728, -1), (key2983, -1), (key2747, -1), (key2904, -1), (key2673, 1), (key2938, 1), (key2618, 1), (key2950, 1), (key2648, 1), (key2737, 1)]

def rawRow3284 : Integer.Sparse Key := [(key2835, -2), (key2885, -2), (key2798, -2), (key2829, 1), (key2809, 1), (key2870, 1), (key2786, 1), (key2860, 1), (key2794, 1), (key3017, 2), (key3030, 2), (key3010, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2960, -1), (key2831, -1), (key2983, -1), (key2728, -1), (key2904, -1), (key2747, -1), (key2938, 1), (key2673, 1), (key2950, 1), (key2618, 1), (key2737, 1), (key2648, 1)]

def rawRow3285 : Integer.Sparse Key := [(key2885, -2), (key2798, -2), (key2835, -2), (key2860, 1), (key2870, 1), (key2794, 1), (key2829, 1), (key2786, 1), (key2809, 1), (key3030, 2), (key3010, 2), (key3017, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2904, -1), (key2983, -1), (key2747, -1), (key2960, -1), (key2728, -1), (key2831, -1), (key2737, 1), (key2950, 1), (key2648, 1), (key2938, 1), (key2618, 1), (key2673, 1)]

def rawRow3286 : Integer.Sparse Key := [(key2885, -2), (key2835, -2), (key2798, -2), (key2870, 1), (key2860, 1), (key2829, 1), (key2794, 1), (key2809, 1), (key2786, 1), (key3030, 2), (key3017, 2), (key3010, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2983, -1), (key2904, -1), (key2960, -1), (key2747, -1), (key2831, -1), (key2728, -1), (key2950, 1), (key2737, 1), (key2938, 1), (key2648, 1), (key2673, 1), (key2618, 1)]

def rawRow3287 : Integer.Sparse Key := [(key3008, -2), (key3026, -2), (key3026, -2), (key3010, 1), (key3010, 1), (key3023, 1), (key3023, 1), (key3030, 1), (key3030, 1), (key2676, 2), (key2732, 2), (key2732, 2), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, -1), (key2885, -1), (key2671, -1), (key2671, -1), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3288 : Integer.Sparse Key := [(key3026, -2), (key3008, -2), (key3026, -2), (key3023, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3023, 1), (key2732, 2), (key2676, 2), (key2732, 2), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3289 : Integer.Sparse Key := [(key3026, -2), (key3026, -2), (key3008, -2), (key3030, 1), (key3023, 1), (key3030, 1), (key3010, 1), (key3023, 1), (key3010, 1), (key2732, 2), (key2732, 2), (key2676, 2), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2644, -1), (key2726, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2671, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3290 : Integer.Sparse Key := [(key3010, -2), (key3017, -2), (key3030, -2), (key3008, 1), (key3010, 1), (key3012, 1), (key3023, 1), (key3017, 1), (key3026, 1), (key2798, 2), (key2835, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2860, -1), (key2829, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow3291 : Integer.Sparse Key := [(key3010, -2), (key3030, -2), (key3017, -2), (key3010, 1), (key3008, 1), (key3023, 1), (key3012, 1), (key3026, 1), (key3017, 1), (key2798, 2), (key2885, 2), (key2835, 2), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2732, -1), (key2794, -1), (key2786, -1), (key2860, -1), (key2809, -1), (key2870, -1), (key2829, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow3292 : Integer.Sparse Key := [(key3017, -2), (key3010, -2), (key3030, -2), (key3012, 1), (key3017, 1), (key3008, 1), (key3026, 1), (key3010, 1), (key3023, 1), (key2835, 2), (key2798, 2), (key2885, 2), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2809, -1), (key2829, -1), (key2786, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow3293 : Integer.Sparse Key := [(key3017, -2), (key3030, -2), (key3010, -2), (key3017, 1), (key3012, 1), (key3026, 1), (key3008, 1), (key3023, 1), (key3010, 1), (key2835, 2), (key2885, 2), (key2798, 2), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, -1), (key2644, -1), (key2829, -1), (key2809, -1), (key2870, -1), (key2786, -1), (key2860, -1), (key2794, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow3294 : Integer.Sparse Key := [(key3030, -2), (key3010, -2), (key3017, -2), (key3023, 1), (key3026, 1), (key3010, 1), (key3017, 1), (key3008, 1), (key3012, 1), (key2885, 2), (key2798, 2), (key2835, 2), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, -1), (key2676, -1), (key2860, -1), (key2870, -1), (key2794, -1), (key2829, -1), (key2786, -1), (key2809, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow3295 : Integer.Sparse Key := [(key3030, -2), (key3017, -2), (key3010, -2), (key3026, 1), (key3023, 1), (key3017, 1), (key3010, 1), (key3012, 1), (key3008, 1), (key2885, 2), (key2835, 2), (key2798, 2), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, -1), (key2621, -1), (key2870, -1), (key2860, -1), (key2829, -1), (key2794, -1), (key2809, -1), (key2786, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow3296 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2404, 6), (key2839, 2), (key2845, 2), (key3019, 2), (key2589, -2), (key2845, -2), (key2876, -2), (key2916, -6), (key2604, 2), (key2916, 2), (key2925, 2)]

def rawRow3297 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2435, -2), (key2404, 6), (key2845, 2), (key2839, 2), (key3019, 2), (key2589, -2), (key2876, -2), (key2845, -2), (key2916, -6), (key2604, 2), (key2925, 2), (key2916, 2)]

def rawRow3298 : Integer.Sparse Key := [(key2398, -2), (key2435, -2), (key2404, -2), (key2404, 6), (key2839, 2), (key3019, 2), (key2845, 2), (key2845, -2), (key2589, -2), (key2876, -2), (key2916, -6), (key2916, 2), (key2604, 2), (key2925, 2)]

def rawRow3299 : Integer.Sparse Key := [(key2435, -2), (key2398, -2), (key2404, -2), (key2404, 6), (key3019, 2), (key2839, 2), (key2845, 2), (key2845, -2), (key2876, -2), (key2589, -2), (key2916, -6), (key2916, 2), (key2925, 2), (key2604, 2)]

def rawRow3300 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2398, -2), (key2404, 6), (key2845, 2), (key3019, 2), (key2839, 2), (key2876, -2), (key2589, -2), (key2845, -2), (key2916, -6), (key2925, 2), (key2604, 2), (key2916, 2)]

def rawRow3301 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2398, -2), (key2404, 6), (key3019, 2), (key2845, 2), (key2839, 2), (key2876, -2), (key2845, -2), (key2589, -2), (key2916, -6), (key2925, 2), (key2916, 2), (key2604, 2)]

def rawRow3302 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2435, -2), (key2398, 6), (key2876, 2), (key2876, 2), (key3028, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2925, -6), (key2604, 2), (key2916, 2), (key2916, 2)]

def rawRow3303 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2404, -2), (key2398, 6), (key2876, 2), (key3028, 2), (key2876, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2925, -6), (key2916, 2), (key2604, 2), (key2916, 2)]

def rawRow3304 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2404, -2), (key2398, 6), (key3028, 2), (key2876, 2), (key2876, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2925, -6), (key2916, 2), (key2916, 2), (key2604, 2)]

def rawRow3305 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2501, -2), (key2478, 6), (key2398, 2), (key2404, 2), (key2435, 2), (key2604, -2), (key2916, -2), (key2925, -2), (key2768, -6), (key2589, 2), (key2845, 2), (key2876, 2)]

def rawRow3306 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2501, -2), (key2478, 6), (key2404, 2), (key2398, 2), (key2435, 2), (key2604, -2), (key2925, -2), (key2916, -2), (key2768, -6), (key2589, 2), (key2876, 2), (key2845, 2)]

def rawRow3307 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2470, -2), (key2478, 6), (key2398, 2), (key2435, 2), (key2404, 2), (key2916, -2), (key2604, -2), (key2925, -2), (key2768, -6), (key2845, 2), (key2589, 2), (key2876, 2)]

def rawRow3308 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2435, 2), (key2398, 2), (key2404, 2), (key2916, -2), (key2925, -2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2589, 2)]

def rawRow3309 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2464, -2), (key2478, 6), (key2404, 2), (key2435, 2), (key2398, 2), (key2925, -2), (key2604, -2), (key2916, -2), (key2768, -6), (key2876, 2), (key2589, 2), (key2845, 2)]

def rawRow3310 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2464, -2), (key2478, 6), (key2435, 2), (key2404, 2), (key2398, 2), (key2925, -2), (key2916, -2), (key2604, -2), (key2768, -6), (key2876, 2), (key2845, 2), (key2589, 2)]

def rawRow3311 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2501, -2), (key2464, 6), (key2568, 2), (key2570, 2), (key2575, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2876, -6), (key2589, 2), (key2768, 2), (key2845, 2)]

def rawRow3312 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2501, -2), (key2464, 6), (key2570, 2), (key2568, 2), (key2575, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2876, -6), (key2589, 2), (key2845, 2), (key2768, 2)]

def rawRow3313 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2478, -2), (key2464, 6), (key2568, 2), (key2575, 2), (key2570, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2876, -6), (key2768, 2), (key2589, 2), (key2845, 2)]

def rawRow3314 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2478, -2), (key2464, 6), (key2575, 2), (key2568, 2), (key2570, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2876, -6), (key2768, 2), (key2845, 2), (key2589, 2)]

def rawRow3315 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2470, -2), (key2464, 6), (key2570, 2), (key2575, 2), (key2568, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2876, -6), (key2845, 2), (key2589, 2), (key2768, 2)]

def rawRow3316 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2470, -2), (key2464, 6), (key2575, 2), (key2570, 2), (key2568, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2876, -6), (key2845, 2), (key2768, 2), (key2589, 2)]

def rawRow3317 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2575, -2), (key2570, 6), (key2404, 2), (key2404, 2), (key2435, 2), (key2388, -2), (key2478, -2), (key2478, -2), (key2398, -6), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow3318 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2568, -2), (key2570, 6), (key2404, 2), (key2435, 2), (key2404, 2), (key2478, -2), (key2388, -2), (key2478, -2), (key2398, -6), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow3319 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2568, -2), (key2570, 6), (key2435, 2), (key2404, 2), (key2404, 2), (key2478, -2), (key2478, -2), (key2388, -2), (key2398, -6), (key2839, 2), (key2839, 2), (key2583, 2)]

def rawRow3320 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2575, -2), (key2568, 6), (key2470, 2), (key2478, 2), (key2501, 2), (key2376, -2), (key2404, -2), (key2470, -2), (key2464, -6), (key2370, 2), (key2762, 2), (key2839, 2)]

def rawRow3321 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2575, -2), (key2568, 6), (key2478, 2), (key2470, 2), (key2501, 2), (key2376, -2), (key2470, -2), (key2404, -2), (key2464, -6), (key2370, 2), (key2839, 2), (key2762, 2)]

def rawRow3322 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2570, -2), (key2568, 6), (key2470, 2), (key2501, 2), (key2478, 2), (key2404, -2), (key2376, -2), (key2470, -2), (key2464, -6), (key2398, 2), (key2583, 2), (key2839, 2)]

def rawRow3323 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2570, -2), (key2568, 6), (key2501, 2), (key2470, 2), (key2478, 2), (key2404, -2), (key2470, -2), (key2376, -2), (key2464, -6), (key2398, 2), (key2839, 2), (key2583, 2)]

def rawRow3324 : Integer.Sparse Key := [(key2570, -2), (key2575, -2), (key2568, -2), (key2568, 6), (key2478, 2), (key2501, 2), (key2470, 2), (key2470, -2), (key2376, -2), (key2404, -2), (key2464, -6), (key2464, 2), (key2370, 2), (key2762, 2)]

def rawRow3325 : Integer.Sparse Key := [(key2575, -2), (key2570, -2), (key2568, -2), (key2568, 6), (key2501, 2), (key2478, 2), (key2470, 2), (key2470, -2), (key2404, -2), (key2376, -2), (key2464, -6), (key2464, 2), (key2398, 2), (key2583, 2)]

def rawRow3326 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2930, -2), (key2767, 6), (key2840, 2), (key2844, 2), (key2967, 2), (key2588, -2), (key2844, -2), (key2875, -2), (key2888, -6), (key2599, 2), (key2888, 2), (key2909, 2)]

def rawRow3327 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2930, -2), (key2767, 6), (key2844, 2), (key2840, 2), (key2967, 2), (key2588, -2), (key2875, -2), (key2844, -2), (key2888, -6), (key2599, 2), (key2909, 2), (key2888, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow256 : Integer.Sparse Key := [(key254, -1), (key269, -1), (key254, 2), (key264, 1), (key274, 1), (key242, -1), (key264, -1), (key265, -2), (key244, 1), (key265, 1), (key322, 1), (key337, 1), (key322, -2), (key332, -1), (key343, -1), (key308, 1), (key332, 1), (key333, 2), (key310, -1), (key333, -1), (key446, -1), (key472, -1), (key412, 1), (key446, 1), (key454, 1), (key478, 1), (key391, -1), (key454, -1), (key423, -1), (key462, -1), (key402, 1), (key462, 1), (key598, 2), (key580, -1), (key598, -1), (key604, -2), (key570, 1), (key604, 1), (key586, 1), (key610, 1), (key575, -1), (key610, -1)]

def rawRow257 : Integer.Sparse Key := [(key269, -1), (key254, -1), (key254, 2), (key274, 1), (key264, 1), (key264, -1), (key242, -1), (key265, -2), (key265, 1), (key244, 1), (key337, 1), (key322, 1), (key322, -2), (key343, -1), (key332, -1), (key332, 1), (key308, 1), (key333, 2), (key333, -1), (key310, -1), (key472, -1), (key446, -1), (key446, 1), (key412, 1), (key478, 1), (key454, 1), (key454, -1), (key391, -1), (key462, -1), (key423, -1), (key462, 1), (key402, 1), (key598, 2), (key598, -1), (key580, -1), (key604, -2), (key604, 1), (key570, 1), (key610, 1), (key586, 1), (key610, -1), (key575, -1)]

def rawRow258 : Integer.Sparse Key := [(key264, -1), (key265, -1), (key274, 2), (key242, 1), (key244, 1), (key269, -1), (key274, -1), (key242, -2), (key254, 1), (key264, 1), (key332, 1), (key333, 1), (key343, -2), (key308, -1), (key310, -1), (key337, 1), (key343, 1), (key308, 2), (key322, -1), (key332, -1), (key422, -1), (key423, -1), (key478, 1), (key484, 1), (key401, 1), (key402, 1), (key472, -1), (key484, -1), (key391, -1), (key401, -1), (key412, 1), (key422, 1), (key586, 2), (key604, -1), (key610, -1), (key575, -2), (key598, 1), (key610, 1), (key570, 1), (key575, 1), (key580, -1), (key586, -1)]

def rawRow259 : Integer.Sparse Key := [(key265, -1), (key264, -1), (key274, 2), (key244, 1), (key242, 1), (key274, -1), (key269, -1), (key242, -2), (key264, 1), (key254, 1), (key333, 1), (key332, 1), (key343, -2), (key310, -1), (key308, -1), (key343, 1), (key337, 1), (key308, 2), (key332, -1), (key322, -1), (key423, -1), (key422, -1), (key484, 1), (key478, 1), (key402, 1), (key401, 1), (key484, -1), (key472, -1), (key401, -1), (key391, -1), (key422, 1), (key412, 1), (key586, 2), (key610, -1), (key604, -1), (key575, -2), (key610, 1), (key598, 1), (key575, 1), (key570, 1), (key586, -1), (key580, -1)]

def rawRow260 : Integer.Sparse Key := [(key264, -1), (key274, -1), (key265, 2), (key254, 1), (key269, 1), (key244, -1), (key265, -1), (key254, -2), (key242, 1), (key264, 1), (key332, 1), (key343, 1), (key333, -2), (key322, -1), (key337, -1), (key310, 1), (key333, 1), (key322, 2), (key308, -1), (key332, -1), (key454, -1), (key478, -1), (key423, 1), (key462, 1), (key446, 1), (key472, 1), (key402, -1), (key462, -1), (key412, -1), (key446, -1), (key391, 1), (key454, 1), (key604, 2), (key586, -1), (key610, -1), (key598, -2), (key575, 1), (key610, 1), (key580, 1), (key598, 1), (key570, -1), (key604, -1)]

def rawRow261 : Integer.Sparse Key := [(key274, -1), (key264, -1), (key265, 2), (key269, 1), (key254, 1), (key265, -1), (key244, -1), (key254, -2), (key264, 1), (key242, 1), (key343, 1), (key332, 1), (key333, -2), (key337, -1), (key322, -1), (key333, 1), (key310, 1), (key322, 2), (key332, -1), (key308, -1), (key478, -1), (key454, -1), (key462, 1), (key423, 1), (key472, 1), (key446, 1), (key462, -1), (key402, -1), (key446, -1), (key412, -1), (key454, 1), (key391, 1), (key604, 2), (key610, -1), (key586, -1), (key598, -2), (key610, 1), (key575, 1), (key598, 1), (key580, 1), (key604, -1), (key570, -1)]

def rawRow262 : Integer.Sparse Key := [(key308, -1), (key308, -1), (key310, 2), (key391, 1), (key391, 1), (key402, -1), (key402, -1), (key570, -2), (key575, 1), (key575, 1), (key242, 1), (key242, 1), (key244, -2), (key412, -1), (key412, -1), (key423, 1), (key423, 1), (key580, 2), (key586, -1), (key586, -1), (key254, -1), (key254, -1), (key265, 1), (key265, 1), (key322, 1), (key322, 1), (key333, -1), (key333, -1), (key598, -1), (key598, -1), (key604, 1), (key604, 1), (key269, 2), (key274, -1), (key274, -1), (key337, -2), (key343, 1), (key343, 1), (key472, 1), (key472, 1), (key478, -1), (key478, -1)]

def rawRow263 : Integer.Sparse Key := [(key308, -1), (key310, -1), (key308, 2), (key401, 1), (key402, 1), (key391, -1), (key401, -1), (key575, -2), (key570, 1), (key575, 1), (key242, 1), (key244, 1), (key242, -2), (key422, -1), (key423, -1), (key412, 1), (key422, 1), (key586, 2), (key580, -1), (key586, -1), (key264, -1), (key265, -1), (key254, 1), (key264, 1), (key332, 1), (key333, 1), (key322, -1), (key332, -1), (key604, -1), (key610, -1), (key598, 1), (key610, 1), (key274, 2), (key269, -1), (key274, -1), (key343, -2), (key337, 1), (key343, 1), (key478, 1), (key484, 1), (key472, -1), (key484, -1)]

def rawRow264 : Integer.Sparse Key := [(key310, -1), (key308, -1), (key308, 2), (key402, 1), (key401, 1), (key401, -1), (key391, -1), (key575, -2), (key575, 1), (key570, 1), (key244, 1), (key242, 1), (key242, -2), (key423, -1), (key422, -1), (key422, 1), (key412, 1), (key586, 2), (key586, -1), (key580, -1), (key265, -1), (key264, -1), (key264, 1), (key254, 1), (key333, 1), (key332, 1), (key332, -1), (key322, -1), (key610, -1), (key604, -1), (key610, 1), (key598, 1), (key274, 2), (key274, -1), (key269, -1), (key343, -2), (key343, 1), (key337, 1), (key484, 1), (key478, 1), (key484, -1), (key472, -1)]

def rawRow265 : Integer.Sparse Key := [(key391, -1), (key391, -1), (key570, 2), (key308, 1), (key308, 1), (key575, -1), (key575, -1), (key310, -2), (key402, 1), (key402, 1), (key412, 1), (key412, 1), (key580, -2), (key242, -1), (key242, -1), (key586, 1), (key586, 1), (key244, 2), (key423, -1), (key423, -1), (key322, -1), (key322, -1), (key598, 1), (key598, 1), (key254, 1), (key254, 1), (key604, -1), (key604, -1), (key265, -1), (key265, -1), (key333, 1), (key333, 1), (key337, 2), (key472, -1), (key472, -1), (key269, -2), (key478, 1), (key478, 1), (key274, 1), (key274, 1), (key343, -1), (key343, -1)]

def rawRow266 : Integer.Sparse Key := [(key391, -1), (key570, -1), (key391, 2), (key401, 1), (key575, 1), (key308, -1), (key401, -1), (key402, -2), (key310, 1), (key402, 1), (key412, 1), (key580, 1), (key412, -2), (key422, -1), (key586, -1), (key242, 1), (key422, 1), (key423, 2), (key244, -1), (key423, -1), (key446, -1), (key598, -1), (key322, 1), (key446, 1), (key454, 1), (key604, 1), (key254, -1), (key454, -1), (key333, -1), (key462, -1), (key265, 1), (key462, 1), (key472, 2), (key337, -1), (key472, -1), (key478, -2), (key269, 1), (key478, 1), (key343, 1), (key484, 1), (key274, -1), (key484, -1)]

def rawRow267 : Integer.Sparse Key := [(key570, -1), (key391, -1), (key391, 2), (key575, 1), (key401, 1), (key401, -1), (key308, -1), (key402, -2), (key402, 1), (key310, 1), (key580, 1), (key412, 1), (key412, -2), (key586, -1), (key422, -1), (key422, 1), (key242, 1), (key423, 2), (key423, -1), (key244, -1), (key598, -1), (key446, -1), (key446, 1), (key322, 1), (key604, 1), (key454, 1), (key454, -1), (key254, -1), (key462, -1), (key333, -1), (key462, 1), (key265, 1), (key472, 2), (key472, -1), (key337, -1), (key478, -2), (key478, 1), (key269, 1), (key484, 1), (key343, 1), (key484, -1), (key274, -1)]

def rawRow268 : Integer.Sparse Key := [(key401, -1), (key402, -1), (key575, 2), (key308, 1), (key310, 1), (key570, -1), (key575, -1), (key308, -2), (key391, 1), (key401, 1), (key422, 1), (key423, 1), (key586, -2), (key242, -1), (key244, -1), (key580, 1), (key586, 1), (key242, 2), (key412, -1), (key422, -1), (key332, -1), (key333, -1), (key604, 1), (key610, 1), (key264, 1), (key265, 1), (key598, -1), (key610, -1), (key254, -1), (key264, -1), (key322, 1), (key332, 1), (key343, 2), (key478, -1), (key484, -1), (key274, -2), (key472, 1), (key484, 1), (key269, 1), (key274, 1), (key337, -1), (key343, -1)]

def rawRow269 : Integer.Sparse Key := [(key402, -1), (key401, -1), (key575, 2), (key310, 1), (key308, 1), (key575, -1), (key570, -1), (key308, -2), (key401, 1), (key391, 1), (key423, 1), (key422, 1), (key586, -2), (key244, -1), (key242, -1), (key586, 1), (key580, 1), (key242, 2), (key422, -1), (key412, -1), (key333, -1), (key332, -1), (key610, 1), (key604, 1), (key265, 1), (key264, 1), (key610, -1), (key598, -1), (key264, -1), (key254, -1), (key332, 1), (key322, 1), (key343, 2), (key484, -1), (key478, -1), (key274, -2), (key484, 1), (key472, 1), (key274, 1), (key269, 1), (key343, -1), (key337, -1)]

def rawRow270 : Integer.Sparse Key := [(key401, -1), (key575, -1), (key402, 2), (key391, 1), (key570, 1), (key310, -1), (key402, -1), (key391, -2), (key308, 1), (key401, 1), (key422, 1), (key586, 1), (key423, -2), (key412, -1), (key580, -1), (key244, 1), (key423, 1), (key412, 2), (key242, -1), (key422, -1), (key454, -1), (key604, -1), (key333, 1), (key462, 1), (key446, 1), (key598, 1), (key265, -1), (key462, -1), (key322, -1), (key446, -1), (key254, 1), (key454, 1), (key478, 2), (key343, -1), (key484, -1), (key472, -2), (key274, 1), (key484, 1), (key337, 1), (key472, 1), (key269, -1), (key478, -1)]

def rawRow271 : Integer.Sparse Key := [(key575, -1), (key401, -1), (key402, 2), (key570, 1), (key391, 1), (key402, -1), (key310, -1), (key391, -2), (key401, 1), (key308, 1), (key586, 1), (key422, 1), (key423, -2), (key580, -1), (key412, -1), (key423, 1), (key244, 1), (key412, 2), (key422, -1), (key242, -1), (key604, -1), (key454, -1), (key462, 1), (key333, 1), (key598, 1), (key446, 1), (key462, -1), (key265, -1), (key446, -1), (key322, -1), (key454, 1), (key254, 1), (key478, 2), (key484, -1), (key343, -1), (key472, -2), (key484, 1), (key274, 1), (key472, 1), (key337, 1), (key478, -1), (key269, -1)]

def rawRow272 : Integer.Sparse Key := [(key322, -1), (key322, -1), (key337, 2), (key412, 1), (key412, 1), (key472, -1), (key472, -1), (key580, -2), (key598, 1), (key598, 1), (key254, 1), (key254, 1), (key269, -2), (key391, -1), (key391, -1), (key478, 1), (key478, 1), (key570, 2), (key604, -1), (key604, -1), (key242, -1), (key242, -1), (key274, 1), (key274, 1), (key308, 1), (key308, 1), (key343, -1), (key343, -1), (key575, -1), (key575, -1), (key586, 1), (key586, 1), (key244, 2), (key265, -1), (key265, -1), (key310, -2), (key333, 1), (key333, 1), (key402, 1), (key402, 1), (key423, -1), (key423, -1)]

def rawRow273 : Integer.Sparse Key := [(key322, -1), (key337, -1), (key322, 2), (key446, 1), (key472, 1), (key412, -1), (key446, -1), (key598, -2), (key580, 1), (key598, 1), (key254, 1), (key269, 1), (key254, -2), (key454, -1), (key478, -1), (key391, 1), (key454, 1), (key604, 2), (key570, -1), (key604, -1), (key264, -1), (key274, -1), (key242, 1), (key264, 1), (key332, 1), (key343, 1), (key308, -1), (key332, -1), (key586, -1), (key610, -1), (key575, 1), (key610, 1), (key265, 2), (key244, -1), (key265, -1), (key333, -2), (key310, 1), (key333, 1), (key423, 1), (key462, 1), (key402, -1), (key462, -1)]

def rawRow274 : Integer.Sparse Key := [(key337, -1), (key322, -1), (key322, 2), (key472, 1), (key446, 1), (key446, -1), (key412, -1), (key598, -2), (key598, 1), (key580, 1), (key269, 1), (key254, 1), (key254, -2), (key478, -1), (key454, -1), (key454, 1), (key391, 1), (key604, 2), (key604, -1), (key570, -1), (key274, -1), (key264, -1), (key264, 1), (key242, 1), (key343, 1), (key332, 1), (key332, -1), (key308, -1), (key610, -1), (key586, -1), (key610, 1), (key575, 1), (key265, 2), (key265, -1), (key244, -1), (key333, -2), (key333, 1), (key310, 1), (key462, 1), (key423, 1), (key462, -1), (key402, -1)]

def rawRow275 : Integer.Sparse Key := [(key412, -1), (key412, -1), (key580, 2), (key322, 1), (key322, 1), (key598, -1), (key598, -1), (key337, -2), (key472, 1), (key472, 1), (key391, 1), (key391, 1), (key570, -2), (key254, -1), (key254, -1), (key604, 1), (key604, 1), (key269, 2), (key478, -1), (key478, -1), (key308, -1), (key308, -1), (key575, 1), (key575, 1), (key242, 1), (key242, 1), (key586, -1), (key586, -1), (key274, -1), (key274, -1), (key343, 1), (key343, 1), (key310, 2), (key402, -1), (key402, -1), (key244, -2), (key423, 1), (key423, 1), (key265, 1), (key265, 1), (key333, -1), (key333, -1)]

def rawRow276 : Integer.Sparse Key := [(key412, -1), (key580, -1), (key412, 2), (key446, 1), (key598, 1), (key322, -1), (key446, -1), (key472, -2), (key337, 1), (key472, 1), (key391, 1), (key570, 1), (key391, -2), (key454, -1), (key604, -1), (key254, 1), (key454, 1), (key478, 2), (key269, -1), (key478, -1), (key401, -1), (key575, -1), (key308, 1), (key401, 1), (key422, 1), (key586, 1), (key242, -1), (key422, -1), (key343, -1), (key484, -1), (key274, 1), (key484, 1), (key402, 2), (key310, -1), (key402, -1), (key423, -2), (key244, 1), (key423, 1), (key333, 1), (key462, 1), (key265, -1), (key462, -1)]

def rawRow277 : Integer.Sparse Key := [(key580, -1), (key412, -1), (key412, 2), (key598, 1), (key446, 1), (key446, -1), (key322, -1), (key472, -2), (key472, 1), (key337, 1), (key570, 1), (key391, 1), (key391, -2), (key604, -1), (key454, -1), (key454, 1), (key254, 1), (key478, 2), (key478, -1), (key269, -1), (key575, -1), (key401, -1), (key401, 1), (key308, 1), (key586, 1), (key422, 1), (key422, -1), (key242, -1), (key484, -1), (key343, -1), (key484, 1), (key274, 1), (key402, 2), (key402, -1), (key310, -1), (key423, -2), (key423, 1), (key244, 1), (key462, 1), (key333, 1), (key462, -1), (key265, -1)]

def rawRow278 : Integer.Sparse Key := [(key446, -1), (key472, -1), (key598, 2), (key322, 1), (key337, 1), (key580, -1), (key598, -1), (key322, -2), (key412, 1), (key446, 1), (key454, 1), (key478, 1), (key604, -2), (key254, -1), (key269, -1), (key570, 1), (key604, 1), (key254, 2), (key391, -1), (key454, -1), (key332, -1), (key343, -1), (key586, 1), (key610, 1), (key264, 1), (key274, 1), (key575, -1), (key610, -1), (key242, -1), (key264, -1), (key308, 1), (key332, 1), (key333, 2), (key423, -1), (key462, -1), (key265, -2), (key402, 1), (key462, 1), (key244, 1), (key265, 1), (key310, -1), (key333, -1)]

def rawRow279 : Integer.Sparse Key := [(key472, -1), (key446, -1), (key598, 2), (key337, 1), (key322, 1), (key598, -1), (key580, -1), (key322, -2), (key446, 1), (key412, 1), (key478, 1), (key454, 1), (key604, -2), (key269, -1), (key254, -1), (key604, 1), (key570, 1), (key254, 2), (key454, -1), (key391, -1), (key343, -1), (key332, -1), (key610, 1), (key586, 1), (key274, 1), (key264, 1), (key610, -1), (key575, -1), (key264, -1), (key242, -1), (key332, 1), (key308, 1), (key333, 2), (key462, -1), (key423, -1), (key265, -2), (key462, 1), (key402, 1), (key265, 1), (key244, 1), (key333, -1), (key310, -1)]

def rawRow280 : Integer.Sparse Key := [(key446, -1), (key598, -1), (key472, 2), (key412, 1), (key580, 1), (key337, -1), (key472, -1), (key412, -2), (key322, 1), (key446, 1), (key454, 1), (key604, 1), (key478, -2), (key391, -1), (key570, -1), (key269, 1), (key478, 1), (key391, 2), (key254, -1), (key454, -1), (key422, -1), (key586, -1), (key343, 1), (key484, 1), (key401, 1), (key575, 1), (key274, -1), (key484, -1), (key308, -1), (key401, -1), (key242, 1), (key422, 1), (key423, 2), (key333, -1), (key462, -1), (key402, -2), (key265, 1), (key462, 1), (key310, 1), (key402, 1), (key244, -1), (key423, -1)]

def rawRow281 : Integer.Sparse Key := [(key598, -1), (key446, -1), (key472, 2), (key580, 1), (key412, 1), (key472, -1), (key337, -1), (key412, -2), (key446, 1), (key322, 1), (key604, 1), (key454, 1), (key478, -2), (key570, -1), (key391, -1), (key478, 1), (key269, 1), (key391, 2), (key454, -1), (key254, -1), (key586, -1), (key422, -1), (key484, 1), (key343, 1), (key575, 1), (key401, 1), (key484, -1), (key274, -1), (key401, -1), (key308, -1), (key422, 1), (key242, 1), (key423, 2), (key462, -1), (key333, -1), (key402, -2), (key462, 1), (key265, 1), (key402, 1), (key310, 1), (key423, -1), (key244, -1)]

def rawRow282 : Integer.Sparse Key := [(key332, -1), (key333, -1), (key343, 2), (key422, 1), (key423, 1), (key478, -1), (key484, -1), (key586, -2), (key604, 1), (key610, 1), (key264, 1), (key265, 1), (key274, -2), (key401, -1), (key402, -1), (key472, 1), (key484, 1), (key575, 2), (key598, -1), (key610, -1), (key242, -1), (key244, -1), (key269, 1), (key274, 1), (key308, 1), (key310, 1), (key337, -1), (key343, -1), (key570, -1), (key575, -1), (key580, 1), (key586, 1), (key242, 2), (key254, -1), (key264, -1), (key308, -2), (key322, 1), (key332, 1), (key391, 1), (key401, 1), (key412, -1), (key422, -1)]

def rawRow283 : Integer.Sparse Key := [(key333, -1), (key332, -1), (key343, 2), (key423, 1), (key422, 1), (key484, -1), (key478, -1), (key586, -2), (key610, 1), (key604, 1), (key265, 1), (key264, 1), (key274, -2), (key402, -1), (key401, -1), (key484, 1), (key472, 1), (key575, 2), (key610, -1), (key598, -1), (key244, -1), (key242, -1), (key274, 1), (key269, 1), (key310, 1), (key308, 1), (key343, -1), (key337, -1), (key575, -1), (key570, -1), (key586, 1), (key580, 1), (key242, 2), (key264, -1), (key254, -1), (key308, -2), (key332, 1), (key322, 1), (key401, 1), (key391, 1), (key422, -1), (key412, -1)]

def rawRow284 : Integer.Sparse Key := [(key332, -1), (key343, -1), (key333, 2), (key454, 1), (key478, 1), (key423, -1), (key462, -1), (key604, -2), (key586, 1), (key610, 1), (key264, 1), (key274, 1), (key265, -2), (key446, -1), (key472, -1), (key402, 1), (key462, 1), (key598, 2), (key575, -1), (key610, -1), (key254, -1), (key269, -1), (key244, 1), (key265, 1), (key322, 1), (key337, 1), (key310, -1), (key333, -1), (key580, -1), (key598, -1), (key570, 1), (key604, 1), (key254, 2), (key242, -1), (key264, -1), (key322, -2), (key308, 1), (key332, 1), (key412, 1), (key446, 1), (key391, -1), (key454, -1)]

def rawRow285 : Integer.Sparse Key := [(key343, -1), (key332, -1), (key333, 2), (key478, 1), (key454, 1), (key462, -1), (key423, -1), (key604, -2), (key610, 1), (key586, 1), (key274, 1), (key264, 1), (key265, -2), (key472, -1), (key446, -1), (key462, 1), (key402, 1), (key598, 2), (key610, -1), (key575, -1), (key269, -1), (key254, -1), (key265, 1), (key244, 1), (key337, 1), (key322, 1), (key333, -1), (key310, -1), (key598, -1), (key580, -1), (key604, 1), (key570, 1), (key254, 2), (key264, -1), (key242, -1), (key322, -2), (key332, 1), (key308, 1), (key446, 1), (key412, 1), (key454, -1), (key391, -1)]

def rawRow286 : Integer.Sparse Key := [(key422, -1), (key423, -1), (key586, 2), (key332, 1), (key333, 1), (key604, -1), (key610, -1), (key343, -2), (key478, 1), (key484, 1), (key401, 1), (key402, 1), (key575, -2), (key264, -1), (key265, -1), (key598, 1), (key610, 1), (key274, 2), (key472, -1), (key484, -1), (key308, -1), (key310, -1), (key570, 1), (key575, 1), (key242, 1), (key244, 1), (key580, -1), (key586, -1), (key269, -1), (key274, -1), (key337, 1), (key343, 1), (key308, 2), (key391, -1), (key401, -1), (key242, -2), (key412, 1), (key422, 1), (key254, 1), (key264, 1), (key322, -1), (key332, -1)]

def rawRow287 : Integer.Sparse Key := [(key423, -1), (key422, -1), (key586, 2), (key333, 1), (key332, 1), (key610, -1), (key604, -1), (key343, -2), (key484, 1), (key478, 1), (key402, 1), (key401, 1), (key575, -2), (key265, -1), (key264, -1), (key610, 1), (key598, 1), (key274, 2), (key484, -1), (key472, -1), (key310, -1), (key308, -1), (key575, 1), (key570, 1), (key244, 1), (key242, 1), (key586, -1), (key580, -1), (key274, -1), (key269, -1), (key343, 1), (key337, 1), (key308, 2), (key401, -1), (key391, -1), (key242, -2), (key422, 1), (key412, 1), (key264, 1), (key254, 1), (key332, -1), (key322, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3328 : Integer.Sparse Key := [(key2763, -2), (key2930, -2), (key2767, -2), (key2767, 6), (key2840, 2), (key2967, 2), (key2844, 2), (key2844, -2), (key2588, -2), (key2875, -2), (key2888, -6), (key2888, 2), (key2599, 2), (key2909, 2)]

def rawRow3329 : Integer.Sparse Key := [(key2930, -2), (key2763, -2), (key2767, -2), (key2767, 6), (key2967, 2), (key2840, 2), (key2844, 2), (key2844, -2), (key2875, -2), (key2588, -2), (key2888, -6), (key2888, 2), (key2909, 2), (key2599, 2)]

def rawRow3330 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2763, -2), (key2767, 6), (key2844, 2), (key2967, 2), (key2840, 2), (key2875, -2), (key2588, -2), (key2844, -2), (key2888, -6), (key2909, 2), (key2599, 2), (key2888, 2)]

def rawRow3331 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2763, -2), (key2767, 6), (key2967, 2), (key2844, 2), (key2840, 2), (key2875, -2), (key2844, -2), (key2588, -2), (key2888, -6), (key2909, 2), (key2888, 2), (key2599, 2)]

def rawRow3332 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2930, -2), (key2763, 6), (key2875, 2), (key2875, 2), (key2988, 2), (key2584, -2), (key2840, -2), (key2840, -2), (key2909, -6), (key2599, 2), (key2888, 2), (key2888, 2)]

def rawRow3333 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2767, -2), (key2763, 6), (key2875, 2), (key2988, 2), (key2875, 2), (key2840, -2), (key2584, -2), (key2840, -2), (key2909, -6), (key2888, 2), (key2599, 2), (key2888, 2)]

def rawRow3334 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2767, -2), (key2763, 6), (key2988, 2), (key2875, 2), (key2875, 2), (key2840, -2), (key2840, -2), (key2584, -2), (key2909, -6), (key2888, 2), (key2888, 2), (key2599, 2)]

def rawRow3335 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2967, -2), (key2888, 6), (key2763, 2), (key2767, 2), (key2930, 2), (key2599, -2), (key2888, -2), (key2909, -2), (key2767, -6), (key2588, 2), (key2844, 2), (key2875, 2)]

def rawRow3336 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2967, -2), (key2888, 6), (key2767, 2), (key2763, 2), (key2930, 2), (key2599, -2), (key2909, -2), (key2888, -2), (key2767, -6), (key2588, 2), (key2875, 2), (key2844, 2)]

def rawRow3337 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2844, -2), (key2888, 6), (key2763, 2), (key2930, 2), (key2767, 2), (key2888, -2), (key2599, -2), (key2909, -2), (key2767, -6), (key2844, 2), (key2588, 2), (key2875, 2)]

def rawRow3338 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2844, -2), (key2888, 6), (key2930, 2), (key2763, 2), (key2767, 2), (key2888, -2), (key2909, -2), (key2599, -2), (key2767, -6), (key2844, 2), (key2875, 2), (key2588, 2)]

def rawRow3339 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2840, -2), (key2888, 6), (key2767, 2), (key2930, 2), (key2763, 2), (key2909, -2), (key2599, -2), (key2888, -2), (key2767, -6), (key2875, 2), (key2588, 2), (key2844, 2)]

def rawRow3340 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2840, -2), (key2888, 6), (key2930, 2), (key2767, 2), (key2763, 2), (key2909, -2), (key2888, -2), (key2599, -2), (key2767, -6), (key2875, 2), (key2844, 2), (key2588, 2)]

def rawRow3341 : Integer.Sparse Key := [(key2844, -2), (key2888, -2), (key2967, -2), (key2840, 6), (key2875, 2), (key2909, 2), (key2988, 2), (key2584, -2), (key2763, -2), (key2840, -2), (key2875, -6), (key2588, 2), (key2767, 2), (key2844, 2)]

def rawRow3342 : Integer.Sparse Key := [(key2888, -2), (key2844, -2), (key2967, -2), (key2840, 6), (key2909, 2), (key2875, 2), (key2988, 2), (key2584, -2), (key2840, -2), (key2763, -2), (key2875, -6), (key2588, 2), (key2844, 2), (key2767, 2)]

def rawRow3343 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2888, -2), (key2840, 6), (key2875, 2), (key2988, 2), (key2909, 2), (key2763, -2), (key2584, -2), (key2840, -2), (key2875, -6), (key2767, 2), (key2588, 2), (key2844, 2)]

def rawRow3344 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2888, -2), (key2840, 6), (key2988, 2), (key2875, 2), (key2909, 2), (key2763, -2), (key2840, -2), (key2584, -2), (key2875, -6), (key2767, 2), (key2844, 2), (key2588, 2)]

def rawRow3345 : Integer.Sparse Key := [(key2888, -2), (key2967, -2), (key2844, -2), (key2840, 6), (key2909, 2), (key2988, 2), (key2875, 2), (key2840, -2), (key2584, -2), (key2763, -2), (key2875, -6), (key2844, 2), (key2588, 2), (key2767, 2)]

def rawRow3346 : Integer.Sparse Key := [(key2967, -2), (key2888, -2), (key2844, -2), (key2840, 6), (key2988, 2), (key2909, 2), (key2875, 2), (key2840, -2), (key2763, -2), (key2584, -2), (key2875, -6), (key2844, 2), (key2767, 2), (key2588, 2)]

def rawRow3347 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2988, -2), (key2909, 6), (key2767, 2), (key2767, 2), (key2930, 2), (key2599, -2), (key2888, -2), (key2888, -2), (key2763, -6), (key2584, 2), (key2840, 2), (key2840, 2)]

def rawRow3348 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2875, -2), (key2909, 6), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, -2), (key2599, -2), (key2888, -2), (key2763, -6), (key2840, 2), (key2584, 2), (key2840, 2)]

def rawRow3349 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2875, -2), (key2909, 6), (key2930, 2), (key2767, 2), (key2767, 2), (key2888, -2), (key2888, -2), (key2599, -2), (key2763, -6), (key2840, 2), (key2840, 2), (key2584, 2)]

def rawRow3350 : Integer.Sparse Key := [(key2875, -2), (key2909, -2), (key2988, -2), (key2875, 6), (key2844, 2), (key2888, 2), (key2967, 2), (key2588, -2), (key2767, -2), (key2844, -2), (key2840, -6), (key2584, 2), (key2763, 2), (key2840, 2)]

def rawRow3351 : Integer.Sparse Key := [(key2909, -2), (key2875, -2), (key2988, -2), (key2875, 6), (key2888, 2), (key2844, 2), (key2967, 2), (key2588, -2), (key2844, -2), (key2767, -2), (key2840, -6), (key2584, 2), (key2840, 2), (key2763, 2)]

def rawRow3352 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2909, -2), (key2875, 6), (key2844, 2), (key2967, 2), (key2888, 2), (key2767, -2), (key2588, -2), (key2844, -2), (key2840, -6), (key2763, 2), (key2584, 2), (key2840, 2)]

def rawRow3353 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2909, -2), (key2875, 6), (key2967, 2), (key2844, 2), (key2888, 2), (key2767, -2), (key2844, -2), (key2588, -2), (key2840, -6), (key2763, 2), (key2840, 2), (key2584, 2)]

def rawRow3354 : Integer.Sparse Key := [(key2909, -2), (key2988, -2), (key2875, -2), (key2875, 6), (key2888, 2), (key2967, 2), (key2844, 2), (key2844, -2), (key2588, -2), (key2767, -2), (key2840, -6), (key2840, 2), (key2584, 2), (key2763, 2)]

def rawRow3355 : Integer.Sparse Key := [(key2988, -2), (key2909, -2), (key2875, -2), (key2875, 6), (key2967, 2), (key2888, 2), (key2844, 2), (key2844, -2), (key2767, -2), (key2588, -2), (key2840, -6), (key2840, 2), (key2763, 2), (key2584, 2)]

def rawRow3356 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2937, -2), (key2664, 1), (key2668, 1), (key2779, 1), (key2791, 1), (key2937, 1), (key2942, 1), (key2802, 2), (key2806, 2), (key2949, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2699, -1), (key2703, -1), (key2852, -1), (key2857, -1), (key2973, -1), (key2975, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2867, 1), (key2973, 1), (key2982, 1)]

def rawRow3357 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2937, -2), (key2668, 1), (key2664, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2937, 1), (key2806, 2), (key2802, 2), (key2949, 2), (key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2703, -1), (key2699, -1), (key2857, -1), (key2852, -1), (key2975, -1), (key2973, -1), (key2629, 1), (key2625, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2973, 1)]

def rawRow3358 : Integer.Sparse Key := [(key2779, -2), (key2937, -2), (key2783, -2), (key2779, 1), (key2937, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2802, 2), (key2949, 2), (key2806, 2), (key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2852, -1), (key2973, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2852, 1), (key2973, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2867, 1)]

def rawRow3359 : Integer.Sparse Key := [(key2937, -2), (key2779, -2), (key2783, -2), (key2937, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2791, 1), (key2668, 1), (key2949, 2), (key2802, 2), (key2806, 2), (key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2857, -1), (key2703, -1), (key2973, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2867, 1), (key2629, 1)]

def rawRow3360 : Integer.Sparse Key := [(key2783, -2), (key2937, -2), (key2779, -2), (key2791, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2664, 1), (key2779, 1), (key2806, 2), (key2949, 2), (key2802, 2), (key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2857, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2699, -1), (key2852, -1), (key2867, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2625, 1), (key2852, 1)]

def rawRow3361 : Integer.Sparse Key := [(key2937, -2), (key2783, -2), (key2779, -2), (key2942, 1), (key2791, 1), (key2937, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2949, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2975, -1), (key2857, -1), (key2973, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2982, 1), (key2867, 1), (key2973, 1), (key2629, 1), (key2852, 1), (key2625, 1)]

def rawRow3362 : Integer.Sparse Key := [(key2791, -2), (key2791, -2), (key2942, -2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2937, 1), (key2937, 1), (key2826, 2), (key2826, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2723, -1), (key2723, -1), (key2867, -1), (key2867, -1), (key2982, -1), (key2982, -1), (key2637, 1), (key2637, 1), (key2857, 1), (key2857, 1), (key2975, 1), (key2975, 1)]

def rawRow3363 : Integer.Sparse Key := [(key2791, -2), (key2942, -2), (key2791, -2), (key2783, 1), (key2937, 1), (key2668, 1), (key2937, 1), (key2668, 1), (key2783, 1), (key2826, 2), (key2959, 2), (key2826, 2), (key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2867, -1), (key2982, -1), (key2723, -1), (key2982, -1), (key2723, -1), (key2867, -1), (key2857, 1), (key2975, 1), (key2637, 1), (key2975, 1), (key2637, 1), (key2857, 1)]

def rawRow3364 : Integer.Sparse Key := [(key2942, -2), (key2791, -2), (key2791, -2), (key2937, 1), (key2783, 1), (key2937, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2959, 2), (key2826, 2), (key2826, 2), (key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2867, -1), (key2982, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2975, 1), (key2857, 1), (key2975, 1), (key2637, 1), (key2857, 1), (key2637, 1)]

def rawRow3365 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2949, -2), (key2699, 1), (key2703, 1), (key2852, 1), (key2857, 1), (key2973, 1), (key2975, 1), (key2779, 2), (key2783, 2), (key2937, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2779, -1), (key2791, -1), (key2937, -1), (key2942, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2826, 1), (key2949, 1), (key2959, 1)]

def rawRow3366 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2949, -2), (key2703, 1), (key2699, 1), (key2857, 1), (key2852, 1), (key2975, 1), (key2973, 1), (key2783, 2), (key2779, 2), (key2937, 2), (key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2668, -1), (key2664, -1), (key2791, -1), (key2779, -1), (key2942, -1), (key2937, -1), (key2613, 1), (key2609, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2949, 1)]

def rawRow3367 : Integer.Sparse Key := [(key2802, -2), (key2949, -2), (key2806, -2), (key2852, 1), (key2973, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2779, 2), (key2937, 2), (key2783, 2), (key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2779, -1), (key2937, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2802, 1), (key2949, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2826, 1)]

def rawRow3368 : Integer.Sparse Key := [(key2949, -2), (key2802, -2), (key2806, -2), (key2973, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2857, 1), (key2703, 1), (key2937, 2), (key2779, 2), (key2783, 2), (key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2791, -1), (key2668, -1), (key2949, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2826, 1), (key2613, 1)]

def rawRow3369 : Integer.Sparse Key := [(key2806, -2), (key2949, -2), (key2802, -2), (key2857, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2699, 1), (key2852, 1), (key2783, 2), (key2937, 2), (key2779, 2), (key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2791, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2664, -1), (key2779, -1), (key2826, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2609, 1), (key2802, 1)]

def rawRow3370 : Integer.Sparse Key := [(key2949, -2), (key2806, -2), (key2802, -2), (key2975, 1), (key2857, 1), (key2973, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2937, 2), (key2783, 2), (key2779, 2), (key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2942, -1), (key2791, -1), (key2937, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2959, 1), (key2826, 1), (key2949, 1), (key2613, 1), (key2802, 1), (key2609, 1)]

def rawRow3371 : Integer.Sparse Key := [(key2857, -2), (key2896, -2), (key2975, -2), (key2703, 1), (key2736, 1), (key2806, 1), (key2894, 1), (key2949, 1), (key2973, 1), (key2867, 2), (key2903, 2), (key2982, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2894, -1), (key2937, -1), (key2973, -1), (key2723, -1), (key2746, -1), (key2826, -1), (key2903, -1), (key2959, -1), (key2982, -1), (key2637, 1), (key2652, 1), (key2791, 1), (key2896, 1), (key2942, 1), (key2975, 1)]

def rawRow3372 : Integer.Sparse Key := [(key2896, -2), (key2857, -2), (key2975, -2), (key2736, 1), (key2703, 1), (key2894, 1), (key2806, 1), (key2973, 1), (key2949, 1), (key2903, 2), (key2867, 2), (key2982, 2), (key2647, -1), (key2629, -1), (key2894, -1), (key2783, -1), (key2973, -1), (key2937, -1), (key2746, -1), (key2723, -1), (key2903, -1), (key2826, -1), (key2982, -1), (key2959, -1), (key2652, 1), (key2637, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2942, 1)]

def rawRow3373 : Integer.Sparse Key := [(key2857, -2), (key2975, -2), (key2896, -2), (key2806, 1), (key2949, 1), (key2703, 1), (key2973, 1), (key2736, 1), (key2894, 1), (key2867, 2), (key2982, 2), (key2903, 2), (key2783, -1), (key2937, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2826, -1), (key2959, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2791, 1), (key2942, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2896, 1)]

def rawRow3374 : Integer.Sparse Key := [(key2975, -2), (key2857, -2), (key2896, -2), (key2949, 1), (key2806, 1), (key2973, 1), (key2703, 1), (key2894, 1), (key2736, 1), (key2982, 2), (key2867, 2), (key2903, 2), (key2937, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2894, -1), (key2647, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2903, -1), (key2746, -1), (key2942, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2896, 1), (key2652, 1)]

def rawRow3375 : Integer.Sparse Key := [(key2896, -2), (key2975, -2), (key2857, -2), (key2894, 1), (key2973, 1), (key2736, 1), (key2949, 1), (key2703, 1), (key2806, 1), (key2903, 2), (key2982, 2), (key2867, 2), (key2894, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2629, -1), (key2783, -1), (key2903, -1), (key2982, -1), (key2746, -1), (key2959, -1), (key2723, -1), (key2826, -1), (key2896, 1), (key2975, 1), (key2652, 1), (key2942, 1), (key2637, 1), (key2791, 1)]

def rawRow3376 : Integer.Sparse Key := [(key2975, -2), (key2896, -2), (key2857, -2), (key2973, 1), (key2894, 1), (key2949, 1), (key2736, 1), (key2806, 1), (key2703, 1), (key2982, 2), (key2903, 2), (key2867, 2), (key2973, -1), (key2894, -1), (key2937, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2982, -1), (key2903, -1), (key2959, -1), (key2746, -1), (key2826, -1), (key2723, -1), (key2975, 1), (key2896, 1), (key2942, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

def rawRow3377 : Integer.Sparse Key := [(key2826, -2), (key2826, -2), (key2959, -2), (key2723, 1), (key2723, 1), (key2867, 1), (key2867, 1), (key2982, 1), (key2982, 1), (key2791, 2), (key2791, 2), (key2942, 2), (key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2937, -1), (key2937, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2949, 1), (key2949, 1)]

def rawRow3378 : Integer.Sparse Key := [(key2826, -2), (key2959, -2), (key2826, -2), (key2867, 1), (key2982, 1), (key2723, 1), (key2982, 1), (key2723, 1), (key2867, 1), (key2791, 2), (key2942, 2), (key2791, 2), (key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2783, -1), (key2937, -1), (key2668, -1), (key2937, -1), (key2668, -1), (key2783, -1), (key2806, 1), (key2949, 1), (key2613, 1), (key2949, 1), (key2613, 1), (key2806, 1)]

def rawRow3379 : Integer.Sparse Key := [(key2959, -2), (key2826, -2), (key2826, -2), (key2982, 1), (key2867, 1), (key2982, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2942, 2), (key2791, 2), (key2791, 2), (key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2949, 1), (key2806, 1), (key2949, 1), (key2613, 1), (key2806, 1), (key2613, 1)]

def rawRow3380 : Integer.Sparse Key := [(key2867, -2), (key2903, -2), (key2982, -2), (key2723, 1), (key2746, 1), (key2826, 1), (key2903, 1), (key2959, 1), (key2982, 1), (key2857, 2), (key2896, 2), (key2975, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2896, -1), (key2942, -1), (key2975, -1), (key2703, -1), (key2736, -1), (key2806, -1), (key2894, -1), (key2949, -1), (key2973, -1), (key2629, 1), (key2647, 1), (key2783, 1), (key2894, 1), (key2937, 1), (key2973, 1)]

def rawRow3381 : Integer.Sparse Key := [(key2903, -2), (key2867, -2), (key2982, -2), (key2746, 1), (key2723, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2959, 1), (key2896, 2), (key2857, 2), (key2975, 2), (key2652, -1), (key2637, -1), (key2896, -1), (key2791, -1), (key2975, -1), (key2942, -1), (key2736, -1), (key2703, -1), (key2894, -1), (key2806, -1), (key2973, -1), (key2949, -1), (key2647, 1), (key2629, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2937, 1)]

def rawRow3382 : Integer.Sparse Key := [(key2867, -2), (key2982, -2), (key2903, -2), (key2826, 1), (key2959, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2857, 2), (key2975, 2), (key2896, 2), (key2791, -1), (key2942, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2806, -1), (key2949, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2783, 1), (key2937, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2894, 1)]

def rawRow3383 : Integer.Sparse Key := [(key2982, -2), (key2867, -2), (key2903, -2), (key2959, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2903, 1), (key2746, 1), (key2975, 2), (key2857, 2), (key2896, 2), (key2942, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2896, -1), (key2652, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2894, -1), (key2736, -1), (key2937, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2894, 1), (key2647, 1)]

def rawRow3384 : Integer.Sparse Key := [(key2903, -2), (key2982, -2), (key2867, -2), (key2903, 1), (key2982, 1), (key2746, 1), (key2959, 1), (key2723, 1), (key2826, 1), (key2896, 2), (key2975, 2), (key2857, 2), (key2896, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2637, -1), (key2791, -1), (key2894, -1), (key2973, -1), (key2736, -1), (key2949, -1), (key2703, -1), (key2806, -1), (key2894, 1), (key2973, 1), (key2647, 1), (key2937, 1), (key2629, 1), (key2783, 1)]

def rawRow3385 : Integer.Sparse Key := [(key2982, -2), (key2903, -2), (key2867, -2), (key2982, 1), (key2903, 1), (key2959, 1), (key2746, 1), (key2826, 1), (key2723, 1), (key2975, 2), (key2896, 2), (key2857, 2), (key2975, -1), (key2896, -1), (key2942, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2973, -1), (key2894, -1), (key2949, -1), (key2736, -1), (key2806, -1), (key2703, -1), (key2973, 1), (key2894, 1), (key2937, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

def rawRow3386 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2187, -2), (key2176, 6), (key2274, 2), (key2276, 2), (key2287, 2), (key2079, -2), (key2276, -2), (key2341, -2), (key2279, -6), (key2085, 2), (key2279, 2), (key2343, 2)]

def rawRow3387 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2187, -2), (key2176, 6), (key2276, 2), (key2274, 2), (key2287, 2), (key2079, -2), (key2341, -2), (key2276, -2), (key2279, -6), (key2085, 2), (key2343, 2), (key2279, 2)]

def rawRow3388 : Integer.Sparse Key := [(key2174, -2), (key2187, -2), (key2176, -2), (key2176, 6), (key2274, 2), (key2287, 2), (key2276, 2), (key2276, -2), (key2079, -2), (key2341, -2), (key2279, -6), (key2279, 2), (key2085, 2), (key2343, 2)]

def rawRow3389 : Integer.Sparse Key := [(key2187, -2), (key2174, -2), (key2176, -2), (key2176, 6), (key2287, 2), (key2274, 2), (key2276, 2), (key2276, -2), (key2341, -2), (key2079, -2), (key2279, -6), (key2279, 2), (key2343, 2), (key2085, 2)]

def rawRow3390 : Integer.Sparse Key := [(key2176, -2), (key2187, -2), (key2174, -2), (key2176, 6), (key2276, 2), (key2287, 2), (key2274, 2), (key2341, -2), (key2079, -2), (key2276, -2), (key2279, -6), (key2343, 2), (key2085, 2), (key2279, 2)]

def rawRow3391 : Integer.Sparse Key := [(key2187, -2), (key2176, -2), (key2174, -2), (key2176, 6), (key2287, 2), (key2276, 2), (key2274, 2), (key2341, -2), (key2276, -2), (key2079, -2), (key2279, -6), (key2343, 2), (key2279, 2), (key2085, 2)]

def rawRow3392 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2187, -2), (key2174, 6), (key2341, 2), (key2341, 2), (key2347, 2), (key2077, -2), (key2274, -2), (key2274, -2), (key2343, -6), (key2085, 2), (key2279, 2), (key2279, 2)]

def rawRow3393 : Integer.Sparse Key := [(key2176, -2), (key2187, -2), (key2176, -2), (key2174, 6), (key2341, 2), (key2347, 2), (key2341, 2), (key2274, -2), (key2077, -2), (key2274, -2), (key2343, -6), (key2279, 2), (key2085, 2), (key2279, 2)]

def rawRow3394 : Integer.Sparse Key := [(key2187, -2), (key2176, -2), (key2176, -2), (key2174, 6), (key2347, 2), (key2341, 2), (key2341, 2), (key2274, -2), (key2274, -2), (key2077, -2), (key2343, -6), (key2279, 2), (key2279, 2), (key2085, 2)]

def rawRow3395 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2287, -2), (key2279, 6), (key2174, 2), (key2176, 2), (key2187, 2), (key2085, -2), (key2279, -2), (key2343, -2), (key2176, -6), (key2079, 2), (key2276, 2), (key2341, 2)]

def rawRow3396 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2287, -2), (key2279, 6), (key2176, 2), (key2174, 2), (key2187, 2), (key2085, -2), (key2343, -2), (key2279, -2), (key2176, -6), (key2079, 2), (key2341, 2), (key2276, 2)]

def rawRow3397 : Integer.Sparse Key := [(key2274, -2), (key2287, -2), (key2276, -2), (key2279, 6), (key2174, 2), (key2187, 2), (key2176, 2), (key2279, -2), (key2085, -2), (key2343, -2), (key2176, -6), (key2276, 2), (key2079, 2), (key2341, 2)]

def rawRow3398 : Integer.Sparse Key := [(key2287, -2), (key2274, -2), (key2276, -2), (key2279, 6), (key2187, 2), (key2174, 2), (key2176, 2), (key2279, -2), (key2343, -2), (key2085, -2), (key2176, -6), (key2276, 2), (key2341, 2), (key2079, 2)]

def rawRow3399 : Integer.Sparse Key := [(key2276, -2), (key2287, -2), (key2274, -2), (key2279, 6), (key2176, 2), (key2187, 2), (key2174, 2), (key2343, -2), (key2085, -2), (key2279, -2), (key2176, -6), (key2341, 2), (key2079, 2), (key2276, 2)]

def rawRow3400 : Integer.Sparse Key := [(key2287, -2), (key2276, -2), (key2274, -2), (key2279, 6), (key2187, 2), (key2176, 2), (key2174, 2), (key2343, -2), (key2279, -2), (key2085, -2), (key2176, -6), (key2341, 2), (key2276, 2), (key2079, 2)]

def rawRow3401 : Integer.Sparse Key := [(key2276, -2), (key2279, -2), (key2287, -2), (key2274, 6), (key2341, 2), (key2343, 2), (key2347, 2), (key2077, -2), (key2174, -2), (key2274, -2), (key2341, -6), (key2079, 2), (key2176, 2), (key2276, 2)]

def rawRow3402 : Integer.Sparse Key := [(key2279, -2), (key2276, -2), (key2287, -2), (key2274, 6), (key2343, 2), (key2341, 2), (key2347, 2), (key2077, -2), (key2274, -2), (key2174, -2), (key2341, -6), (key2079, 2), (key2276, 2), (key2176, 2)]

def rawRow3403 : Integer.Sparse Key := [(key2276, -2), (key2287, -2), (key2279, -2), (key2274, 6), (key2341, 2), (key2347, 2), (key2343, 2), (key2174, -2), (key2077, -2), (key2274, -2), (key2341, -6), (key2176, 2), (key2079, 2), (key2276, 2)]

def rawRow3404 : Integer.Sparse Key := [(key2287, -2), (key2276, -2), (key2279, -2), (key2274, 6), (key2347, 2), (key2341, 2), (key2343, 2), (key2174, -2), (key2274, -2), (key2077, -2), (key2341, -6), (key2176, 2), (key2276, 2), (key2079, 2)]

def rawRow3405 : Integer.Sparse Key := [(key2279, -2), (key2287, -2), (key2276, -2), (key2274, 6), (key2343, 2), (key2347, 2), (key2341, 2), (key2274, -2), (key2077, -2), (key2174, -2), (key2341, -6), (key2276, 2), (key2079, 2), (key2176, 2)]

def rawRow3406 : Integer.Sparse Key := [(key2287, -2), (key2279, -2), (key2276, -2), (key2274, 6), (key2347, 2), (key2343, 2), (key2341, 2), (key2274, -2), (key2174, -2), (key2077, -2), (key2341, -6), (key2276, 2), (key2176, 2), (key2079, 2)]

def rawRow3407 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2347, -2), (key2343, 6), (key2176, 2), (key2176, 2), (key2187, 2), (key2085, -2), (key2279, -2), (key2279, -2), (key2174, -6), (key2077, 2), (key2274, 2), (key2274, 2)]

def rawRow3408 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2341, -2), (key2343, 6), (key2176, 2), (key2187, 2), (key2176, 2), (key2279, -2), (key2085, -2), (key2279, -2), (key2174, -6), (key2274, 2), (key2077, 2), (key2274, 2)]

def rawRow3409 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2341, -2), (key2343, 6), (key2187, 2), (key2176, 2), (key2176, 2), (key2279, -2), (key2279, -2), (key2085, -2), (key2174, -6), (key2274, 2), (key2274, 2), (key2077, 2)]

def rawRow3410 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2347, -2), (key2341, 6), (key2276, 2), (key2279, 2), (key2287, 2), (key2079, -2), (key2176, -2), (key2276, -2), (key2274, -6), (key2077, 2), (key2174, 2), (key2274, 2)]

def rawRow3411 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2347, -2), (key2341, 6), (key2279, 2), (key2276, 2), (key2287, 2), (key2079, -2), (key2276, -2), (key2176, -2), (key2274, -6), (key2077, 2), (key2274, 2), (key2174, 2)]

def rawRow3412 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2343, -2), (key2341, 6), (key2276, 2), (key2287, 2), (key2279, 2), (key2176, -2), (key2079, -2), (key2276, -2), (key2274, -6), (key2174, 2), (key2077, 2), (key2274, 2)]

def rawRow3413 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2343, -2), (key2341, 6), (key2287, 2), (key2276, 2), (key2279, 2), (key2176, -2), (key2276, -2), (key2079, -2), (key2274, -6), (key2174, 2), (key2274, 2), (key2077, 2)]

def rawRow3414 : Integer.Sparse Key := [(key2343, -2), (key2347, -2), (key2341, -2), (key2341, 6), (key2279, 2), (key2287, 2), (key2276, 2), (key2276, -2), (key2079, -2), (key2176, -2), (key2274, -6), (key2274, 2), (key2077, 2), (key2174, 2)]

def rawRow3415 : Integer.Sparse Key := [(key2347, -2), (key2343, -2), (key2341, -2), (key2341, 6), (key2287, 2), (key2279, 2), (key2276, 2), (key2276, -2), (key2176, -2), (key2079, -2), (key2274, -6), (key2274, 2), (key2174, 2), (key2077, 2)]

def rawRow3416 : Integer.Sparse Key := [(key2406, -2), (key2437, -2), (key2443, -2), (key2406, 2), (key2411, 2), (key2443, 2), (key2843, 2), (key2966, 2), (key2968, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, 1), (key2600, 1), (key2887, 1), (key2910, 1), (key2995, 1), (key3002, 1)]

def rawRow3417 : Integer.Sparse Key := [(key2406, -2), (key2443, -2), (key2437, -2), (key2411, 2), (key2406, 2), (key2443, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, 1), (key2598, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2995, 1)]

def rawRow3418 : Integer.Sparse Key := [(key2437, -2), (key2406, -2), (key2443, -2), (key2406, 2), (key2443, 2), (key2411, 2), (key2966, 2), (key2843, 2), (key2968, 2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, 1), (key2995, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2910, 1)]

def rawRow3419 : Integer.Sparse Key := [(key2437, -2), (key2443, -2), (key2406, -2), (key2443, 2), (key2406, 2), (key2411, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2910, 1), (key2600, 1)]

def rawRow3420 : Integer.Sparse Key := [(key2443, -2), (key2406, -2), (key2437, -2), (key2411, 2), (key2443, 2), (key2406, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2598, 1), (key2887, 1)]

def rawRow3421 : Integer.Sparse Key := [(key2443, -2), (key2437, -2), (key2406, -2), (key2443, 2), (key2411, 2), (key2406, 2), (key2968, 2), (key2966, 2), (key2843, 2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, 1), (key2910, 1), (key2995, 1), (key2600, 1), (key2887, 1), (key2598, 1)]

def rawRow3422 : Integer.Sparse Key := [(key2411, -2), (key2443, -2), (key2443, -2), (key2406, 2), (key2406, 2), (key2437, 2), (key2880, 2), (key2989, 2), (key2989, 2), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, 1), (key2600, 1), (key2889, 1), (key2889, 1), (key2995, 1), (key2995, 1)]

def rawRow3423 : Integer.Sparse Key := [(key2443, -2), (key2411, -2), (key2443, -2), (key2406, 2), (key2437, 2), (key2406, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, 1), (key2995, 1), (key2600, 1), (key2995, 1), (key2600, 1), (key2889, 1)]

def rawRow3424 : Integer.Sparse Key := [(key2443, -2), (key2443, -2), (key2411, -2), (key2437, 2), (key2406, 2), (key2406, 2), (key2989, 2), (key2989, 2), (key2880, 2), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, 1), (key2889, 1), (key2995, 1), (key2600, 1), (key2889, 1), (key2600, 1)]

def rawRow3425 : Integer.Sparse Key := [(key2472, -2), (key2503, -2), (key2509, -2), (key2480, 2), (key2484, 2), (key2524, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, 1), (key2593, 1), (key2843, 1), (key2880, 1), (key2968, 1), (key2989, 1)]

def rawRow3426 : Integer.Sparse Key := [(key2472, -2), (key2509, -2), (key2503, -2), (key2484, 2), (key2480, 2), (key2524, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, 1), (key2587, 1), (key2880, 1), (key2843, 1), (key2989, 1), (key2968, 1)]

def rawRow3427 : Integer.Sparse Key := [(key2503, -2), (key2472, -2), (key2509, -2), (key2480, 2), (key2524, 2), (key2484, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, 1), (key2968, 1), (key2587, 1), (key2989, 1), (key2593, 1), (key2880, 1)]

def rawRow3428 : Integer.Sparse Key := [(key2503, -2), (key2509, -2), (key2472, -2), (key2524, 2), (key2480, 2), (key2484, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, 1), (key2843, 1), (key2989, 1), (key2587, 1), (key2880, 1), (key2593, 1)]

def rawRow3429 : Integer.Sparse Key := [(key2509, -2), (key2472, -2), (key2503, -2), (key2484, 2), (key2524, 2), (key2480, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, 1), (key2989, 1), (key2593, 1), (key2968, 1), (key2587, 1), (key2843, 1)]

def rawRow3430 : Integer.Sparse Key := [(key2509, -2), (key2503, -2), (key2472, -2), (key2524, 2), (key2484, 2), (key2480, 2), (key2443, 2), (key2437, 2), (key2406, 2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, 1), (key2880, 1), (key2968, 1), (key2593, 1), (key2843, 1), (key2587, 1)]

def rawRow3431 : Integer.Sparse Key := [(key2484, -2), (key2509, -2), (key2524, -2), (key2472, 2), (key2480, 2), (key2503, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, -1), (key2503, -1), (key2880, -2), (key2910, -2), (key2989, -2), (key2593, 1), (key2600, 1), (key2772, 1), (key2889, 1), (key2931, 1), (key2968, 1)]

def rawRow3432 : Integer.Sparse Key := [(key2484, -2), (key2524, -2), (key2509, -2), (key2480, 2), (key2472, 2), (key2503, 2), (key2571, 2), (key2580, 2), (key2576, 2), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, -1), (key2437, -1), (key2910, -2), (key2880, -2), (key2989, -2), (key2600, 1), (key2593, 1), (key2889, 1), (key2772, 1), (key2968, 1), (key2931, 1)]

def rawRow3433 : Integer.Sparse Key := [(key2509, -2), (key2484, -2), (key2524, -2), (key2472, 2), (key2503, 2), (key2480, 2), (key2576, 2), (key2571, 2), (key2580, 2), (key2406, -1), (key2437, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2880, -2), (key2989, -2), (key2910, -2), (key2772, 1), (key2931, 1), (key2593, 1), (key2968, 1), (key2600, 1), (key2889, 1)]

def rawRow3434 : Integer.Sparse Key := [(key2509, -2), (key2524, -2), (key2484, -2), (key2503, 2), (key2472, 2), (key2480, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2437, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2480, -1), (key2390, -1), (key2989, -2), (key2880, -2), (key2910, -2), (key2931, 1), (key2772, 1), (key2968, 1), (key2593, 1), (key2889, 1), (key2600, 1)]

def rawRow3435 : Integer.Sparse Key := [(key2524, -2), (key2484, -2), (key2509, -2), (key2480, 2), (key2503, 2), (key2472, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, -1), (key2406, -1), (key2910, -2), (key2989, -2), (key2880, -2), (key2889, 1), (key2968, 1), (key2600, 1), (key2931, 1), (key2593, 1), (key2772, 1)]

def rawRow3436 : Integer.Sparse Key := [(key2524, -2), (key2509, -2), (key2484, -2), (key2503, 2), (key2480, 2), (key2472, 2), (key2580, 2), (key2576, 2), (key2571, 2), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2989, -2), (key2910, -2), (key2880, -2), (key2968, 1), (key2889, 1), (key2931, 1), (key2600, 1), (key2772, 1), (key2593, 1)]

def rawRow3437 : Integer.Sparse Key := [(key2569, -2), (key2576, -2), (key2576, -2), (key2571, 2), (key2571, 2), (key2580, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, -1), (key2524, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, 1), (key2378, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1)]

def rawRow3438 : Integer.Sparse Key := [(key2576, -2), (key2569, -2), (key2576, -2), (key2571, 2), (key2580, 2), (key2571, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, 1), (key2503, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2472, 1)]

def rawRow3439 : Integer.Sparse Key := [(key2576, -2), (key2576, -2), (key2569, -2), (key2580, 2), (key2571, 2), (key2571, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2394, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, 1), (key2472, 1), (key2503, 1), (key2378, 1), (key2472, 1), (key2378, 1)]

def rawRow3440 : Integer.Sparse Key := [(key2571, -2), (key2576, -2), (key2580, -2), (key2569, 2), (key2571, 2), (key2576, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2383, -1), (key2394, -1), (key2411, -1), (key2484, -1), (key2443, -1), (key2509, -1), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, 1), (key2390, 1), (key2406, 1), (key2480, 1), (key2437, 1), (key2503, 1)]

def rawRow3441 : Integer.Sparse Key := [(key2571, -2), (key2580, -2), (key2576, -2), (key2571, 2), (key2569, 2), (key2576, 2), (key2484, 2), (key2524, 2), (key2509, 2), (key2394, -1), (key2383, -1), (key2484, -1), (key2411, -1), (key2509, -1), (key2443, -1), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2437, 1)]

def rawRow3442 : Integer.Sparse Key := [(key2576, -2), (key2571, -2), (key2580, -2), (key2569, 2), (key2576, 2), (key2571, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2411, -1), (key2443, -1), (key2383, -1), (key2509, -1), (key2394, -1), (key2484, -1), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, 1), (key2437, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2480, 1)]

def rawRow3443 : Integer.Sparse Key := [(key2576, -2), (key2580, -2), (key2571, -2), (key2576, 2), (key2569, 2), (key2571, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2443, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2484, -1), (key2394, -1), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2480, 1), (key2390, 1)]

def rawRow3444 : Integer.Sparse Key := [(key2580, -2), (key2571, -2), (key2576, -2), (key2571, 2), (key2576, 2), (key2569, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, -1), (key2509, -1), (key2394, -1), (key2443, -1), (key2383, -1), (key2411, -1), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2378, 1), (key2406, 1)]

def rawRow3445 : Integer.Sparse Key := [(key2580, -2), (key2576, -2), (key2571, -2), (key2576, 2), (key2571, 2), (key2569, 2), (key2524, 2), (key2509, 2), (key2484, 2), (key2509, -1), (key2484, -1), (key2443, -1), (key2394, -1), (key2411, -1), (key2383, -1), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, 1), (key2480, 1), (key2437, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

def rawRow3446 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1), (key2657, -2), (key2918, -2), (key2922, -2), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1)]

def rawRow3447 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1), (key2657, -2), (key2922, -2), (key2918, -2), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1)]

def rawRow3448 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2918, -2), (key2657, -2), (key2922, -2), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1)]

def rawRow3449 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1), (key2918, -2), (key2922, -2), (key2657, -2), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1)]

def rawRow3450 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1), (key2922, -2), (key2657, -2), (key2918, -2), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1)]

def rawRow3451 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2922, -2), (key2918, -2), (key2657, -2), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

def rawRow3452 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2659, -2), (key2919, -2), (key2919, -2), (key2657, 1), (key2657, 1), (key2752, 1), (key2752, 1), (key2918, 1), (key2918, 1)]

def rawRow3453 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2919, -2), (key2659, -2), (key2919, -2), (key2752, 1), (key2918, 1), (key2657, 1), (key2918, 1), (key2657, 1), (key2752, 1)]

def rawRow3454 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2919, -2), (key2919, -2), (key2659, -2), (key2918, 1), (key2752, 1), (key2918, 1), (key2657, 1), (key2752, 1), (key2657, 1)]

def rawRow3455 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2638, 2), (key2858, 2), (key3022, 2), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1), (key2614, -2), (key2807, -2), (key2827, -2), (key2630, 1), (key2638, 1), (key2704, 1), (key2724, 1), (key2858, 1), (key2868, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3456 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2638, 2), (key3022, 2), (key2858, 2), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1), (key2614, -2), (key2827, -2), (key2807, -2), (key2638, 1), (key2630, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2858, 1)]

def rawRow3457 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2858, 2), (key2638, 2), (key3022, 2), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2807, -2), (key2614, -2), (key2827, -2), (key2704, 1), (key2858, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2724, 1)]

def rawRow3458 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2858, 2), (key3022, 2), (key2638, 2), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1), (key2807, -2), (key2827, -2), (key2614, -2), (key2858, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2724, 1), (key2638, 1)]

def rawRow3459 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key3022, 2), (key2638, 2), (key2858, 2), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1), (key2827, -2), (key2614, -2), (key2807, -2), (key2724, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2630, 1), (key2704, 1)]

def rawRow3460 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3022, 2), (key2858, 2), (key2638, 2), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, -2), (key2807, -2), (key2614, -2), (key2868, 1), (key2724, 1), (key2858, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

def rawRow3461 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2638, -2), (key2792, -2), (key2858, -2), (key2614, 1), (key2630, 1), (key2669, 1), (key2704, 1), (key2784, 1), (key2807, 1)]

def rawRow3462 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2638, -2), (key2858, -2), (key2792, -2), (key2630, 1), (key2614, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2784, 1)]

def rawRow3463 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2792, -2), (key2638, -2), (key2858, -2), (key2669, 1), (key2784, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2704, 1)]

def rawRow3464 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2792, -2), (key2858, -2), (key2638, -2), (key2784, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2704, 1), (key2630, 1)]

def rawRow3465 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2858, -2), (key2638, -2), (key2792, -2), (key2704, 1), (key2807, 1), (key2630, 1), (key2784, 1), (key2614, 1), (key2669, 1)]

def rawRow3466 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2858, -2), (key2792, -2), (key2638, -2), (key2807, 1), (key2704, 1), (key2784, 1), (key2630, 1), (key2669, 1), (key2614, 1)]

def rawRow3467 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2638, -1), (key2638, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow3468 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2792, -1), (key2858, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow3469 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2858, -1), (key2792, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2638, -1), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow3470 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2657, 2), (key2752, 2), (key2918, 2), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, -1), (key2630, -1), (key2669, -1), (key2784, -1), (key2704, -1), (key2807, -1), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow3471 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2657, 2), (key2918, 2), (key2752, 2), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2630, -1), (key2614, -1), (key2784, -1), (key2669, -1), (key2807, -1), (key2704, -1), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow3472 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2752, 2), (key2657, 2), (key2918, 2), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, -1), (key2704, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow3473 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2918, 2), (key2657, 2), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2704, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2784, -1), (key2630, -1), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow3474 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2784, -1), (key2807, -1), (key2630, -1), (key2704, -1), (key2614, -1), (key2669, -1), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow3475 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2807, -1), (key2784, -1), (key2704, -1), (key2630, -1), (key2669, -1), (key2614, -1), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow3476 : Integer.Sparse Key := [(key2674, -2), (key2796, -2), (key2796, -2), (key2671, 1), (key2671, 1), (key2786, 1), (key2786, 1), (key2794, 1), (key2794, 1), (key2738, 2), (key2898, 2), (key2898, 2), (key2706, -1), (key2706, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2748, -1), (key2748, -1), (key2905, -1), (key2905, -1), (key2913, -1), (key2913, -1), (key2729, 1), (key2729, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

def rawRow3477 : Integer.Sparse Key := [(key2796, -2), (key2674, -2), (key2796, -2), (key2786, 1), (key2794, 1), (key2671, 1), (key2794, 1), (key2671, 1), (key2786, 1), (key2898, 2), (key2738, 2), (key2898, 2), (key2809, -1), (key2860, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2905, -1), (key2913, -1), (key2748, -1), (key2913, -1), (key2748, -1), (key2905, -1), (key2832, 1), (key2883, 1), (key2729, 1), (key2883, 1), (key2729, 1), (key2832, 1)]

def rawRow3478 : Integer.Sparse Key := [(key2796, -2), (key2796, -2), (key2674, -2), (key2794, 1), (key2786, 1), (key2794, 1), (key2671, 1), (key2786, 1), (key2671, 1), (key2898, 2), (key2898, 2), (key2738, 2), (key2860, -1), (key2809, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2706, -1), (key2913, -1), (key2905, -1), (key2913, -1), (key2748, -1), (key2905, -1), (key2748, -1), (key2883, 1), (key2832, 1), (key2883, 1), (key2729, 1), (key2832, 1), (key2729, 1)]

def rawRow3479 : Integer.Sparse Key := [(key2619, -2), (key2832, -2), (key2832, -2), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2649, 2), (key2905, 2), (key2905, 2), (key2632, -1), (key2632, -1), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2654, -1), (key2654, -1), (key2898, -1), (key2898, -1), (key2913, -1), (key2913, -1), (key2642, 1), (key2642, 1), (key2796, 1), (key2796, 1), (key2883, 1), (key2883, 1)]

def rawRow3480 : Integer.Sparse Key := [(key2832, -2), (key2619, -2), (key2832, -2), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2905, 2), (key2649, 2), (key2905, 2), (key2786, -1), (key2870, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2898, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2898, -1), (key2796, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2796, 1)]

def rawRow3481 : Integer.Sparse Key := [(key2832, -2), (key2832, -2), (key2619, -2), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2616, 1), (key2905, 2), (key2905, 2), (key2649, 2), (key2870, -1), (key2786, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2632, -1), (key2913, -1), (key2898, -1), (key2913, -1), (key2654, -1), (key2898, -1), (key2654, -1), (key2883, 1), (key2796, 1), (key2883, 1), (key2642, 1), (key2796, 1), (key2642, 1)]

def rawRow3482 : Integer.Sparse Key := [(key2738, -2), (key2898, -2), (key2898, -2), (key2748, 1), (key2748, 1), (key2905, 1), (key2905, 1), (key2913, 1), (key2913, 1), (key2674, 2), (key2796, 2), (key2796, 2), (key2729, -1), (key2729, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2671, -1), (key2671, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2706, 1), (key2706, 1), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1)]

def rawRow3483 : Integer.Sparse Key := [(key2898, -2), (key2738, -2), (key2898, -2), (key2905, 1), (key2913, 1), (key2748, 1), (key2913, 1), (key2748, 1), (key2905, 1), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, -1), (key2883, -1), (key2729, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2786, -1), (key2794, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2786, -1), (key2809, 1), (key2860, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2809, 1)]

def rawRow3484 : Integer.Sparse Key := [(key2898, -2), (key2898, -2), (key2738, -2), (key2913, 1), (key2905, 1), (key2913, 1), (key2748, 1), (key2905, 1), (key2748, 1), (key2796, 2), (key2796, 2), (key2674, 2), (key2883, -1), (key2832, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2729, -1), (key2794, -1), (key2786, -1), (key2794, -1), (key2671, -1), (key2786, -1), (key2671, -1), (key2860, 1), (key2809, 1), (key2860, 1), (key2706, 1), (key2809, 1), (key2706, 1)]

def rawRow3485 : Integer.Sparse Key := [(key2649, -2), (key2905, -2), (key2905, -2), (key2654, 1), (key2654, 1), (key2898, 1), (key2898, 1), (key2913, 1), (key2913, 1), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, -1), (key2642, -1), (key2796, -1), (key2796, -1), (key2883, -1), (key2883, -1), (key2616, -1), (key2616, -1), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3486 : Integer.Sparse Key := [(key2905, -2), (key2649, -2), (key2905, -2), (key2898, 1), (key2913, 1), (key2654, 1), (key2913, 1), (key2654, 1), (key2898, 1), (key2832, 2), (key2619, 2), (key2832, 2), (key2796, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3487 : Integer.Sparse Key := [(key2905, -2), (key2905, -2), (key2649, -2), (key2913, 1), (key2898, 1), (key2913, 1), (key2654, 1), (key2898, 1), (key2654, 1), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, -1), (key2796, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2642, -1), (key2829, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2616, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3488 : Integer.Sparse Key := [(key1334, -6), (key1288, 2), (key1308, 2), (key1308, 2), (key1769, 6), (key1383, -2), (key1538, -2), (key1538, -2), (key1785, -2), (key1810, -2), (key1810, -2), (key1452, 2), (key1652, 2), (key1652, 2)]

def rawRow3489 : Integer.Sparse Key := [(key1334, -6), (key1308, 2), (key1288, 2), (key1308, 2), (key1769, 6), (key1538, -2), (key1383, -2), (key1538, -2), (key1810, -2), (key1785, -2), (key1810, -2), (key1652, 2), (key1452, 2), (key1652, 2)]

def rawRow3490 : Integer.Sparse Key := [(key1334, -6), (key1308, 2), (key1308, 2), (key1288, 2), (key1769, 6), (key1538, -2), (key1538, -2), (key1383, -2), (key1810, -2), (key1810, -2), (key1785, -2), (key1652, 2), (key1652, 2), (key1452, 2)]

def rawRow3491 : Integer.Sparse Key := [(key1452, -6), (key1383, 2), (key1416, 2), (key1416, 2), (key1785, 6), (key1288, -2), (key1565, -2), (key1565, -2), (key1769, -2), (key1810, -2), (key1810, -2), (key1334, 2), (key1652, 2), (key1652, 2)]

def rawRow3492 : Integer.Sparse Key := [(key1452, -6), (key1416, 2), (key1383, 2), (key1416, 2), (key1785, 6), (key1565, -2), (key1288, -2), (key1565, -2), (key1810, -2), (key1769, -2), (key1810, -2), (key1652, 2), (key1334, 2), (key1652, 2)]

def rawRow3493 : Integer.Sparse Key := [(key1452, -6), (key1416, 2), (key1416, 2), (key1383, 2), (key1785, 6), (key1565, -2), (key1565, -2), (key1288, -2), (key1810, -2), (key1810, -2), (key1769, -2), (key1652, 2), (key1652, 2), (key1334, 2)]

def rawRow3494 : Integer.Sparse Key := [(key1769, -6), (key1785, 2), (key1810, 2), (key1810, 2), (key1334, 6), (key1452, -2), (key1652, -2), (key1652, -2), (key1288, -2), (key1308, -2), (key1308, -2), (key1383, 2), (key1538, 2), (key1538, 2)]

def rawRow3495 : Integer.Sparse Key := [(key1769, -6), (key1810, 2), (key1785, 2), (key1810, 2), (key1334, 6), (key1652, -2), (key1452, -2), (key1652, -2), (key1308, -2), (key1288, -2), (key1308, -2), (key1538, 2), (key1383, 2), (key1538, 2)]

def rawRow3496 : Integer.Sparse Key := [(key1769, -6), (key1810, 2), (key1810, 2), (key1785, 2), (key1334, 6), (key1652, -2), (key1652, -2), (key1452, -2), (key1308, -2), (key1308, -2), (key1288, -2), (key1538, 2), (key1538, 2), (key1383, 2)]

def rawRow3497 : Integer.Sparse Key := [(key1785, -6), (key1769, 2), (key1810, 2), (key1810, 2), (key1452, 6), (key1334, -2), (key1652, -2), (key1652, -2), (key1383, -2), (key1416, -2), (key1416, -2), (key1288, 2), (key1565, 2), (key1565, 2)]

def rawRow3498 : Integer.Sparse Key := [(key1785, -6), (key1810, 2), (key1769, 2), (key1810, 2), (key1452, 6), (key1652, -2), (key1334, -2), (key1652, -2), (key1416, -2), (key1383, -2), (key1416, -2), (key1565, 2), (key1288, 2), (key1565, 2)]

def rawRow3499 : Integer.Sparse Key := [(key1785, -6), (key1810, 2), (key1810, 2), (key1769, 2), (key1452, 6), (key1652, -2), (key1652, -2), (key1334, -2), (key1416, -2), (key1416, -2), (key1383, -2), (key1565, 2), (key1565, 2), (key1288, 2)]

def rawRow3500 : Integer.Sparse Key := [(key2647, -2), (key2647, -2), (key2652, -2), (key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2937, 2), (key2937, 2), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1)]

def rawRow3501 : Integer.Sparse Key := [(key2647, -2), (key2652, -2), (key2647, -2), (key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2937, 2), (key2942, 2), (key2937, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1)]

def rawRow3502 : Integer.Sparse Key := [(key2652, -2), (key2647, -2), (key2647, -2), (key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2942, 2), (key2937, 2), (key2937, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1)]

def rawRow3503 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1)]

def rawRow3504 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1)]

def rawRow3505 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1)]

def rawRow3506 : Integer.Sparse Key := [(key2937, -2), (key2937, -2), (key2942, -2), (key2949, 1), (key2949, 1), (key2973, 1), (key2973, 1), (key2975, 1), (key2975, 1), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1)]

def rawRow3507 : Integer.Sparse Key := [(key2937, -2), (key2942, -2), (key2937, -2), (key2973, 1), (key2975, 1), (key2949, 1), (key2975, 1), (key2949, 1), (key2973, 1), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1)]

def rawRow3508 : Integer.Sparse Key := [(key2942, -2), (key2937, -2), (key2937, -2), (key2975, 1), (key2973, 1), (key2975, 1), (key2949, 1), (key2973, 1), (key2949, 1), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1)]

def rawRow3509 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1)]

def rawRow3510 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1)]

def rawRow3511 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1)]

def rawRow3512 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key1013, -2), (key994, 6), (key1191, 2), (key1191, 2), (key1197, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1210, -6), (key1069, 2), (key1148, 2), (key1148, 2)]

def rawRow3513 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key999, -2), (key994, 6), (key1191, 2), (key1197, 2), (key1191, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1210, -6), (key1148, 2), (key1069, 2), (key1148, 2)]

def rawRow3514 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key999, -2), (key994, 6), (key1197, 2), (key1191, 2), (key1191, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1210, -6), (key1148, 2), (key1148, 2), (key1069, 2)]

def rawRow3515 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1069, -2), (key1029, 6), (key1191, 2), (key1191, 2), (key1210, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1197, -6), (key1013, 2), (key1121, 2), (key1121, 2)]

def rawRow3516 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1034, -2), (key1029, 6), (key1191, 2), (key1210, 2), (key1191, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1197, -6), (key1121, 2), (key1013, 2), (key1121, 2)]

def rawRow3517 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1034, -2), (key1029, 6), (key1210, 2), (key1191, 2), (key1191, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1197, -6), (key1121, 2), (key1121, 2), (key1013, 2)]

def rawRow3518 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1197, -2), (key1210, 6), (key999, 2), (key999, 2), (key1013, 2), (key1069, -2), (key1148, -2), (key1148, -2), (key994, -6), (key1029, 2), (key1107, 2), (key1107, 2)]

def rawRow3519 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1191, -2), (key1210, 6), (key999, 2), (key1013, 2), (key999, 2), (key1148, -2), (key1069, -2), (key1148, -2), (key994, -6), (key1107, 2), (key1029, 2), (key1107, 2)]

def rawRow3520 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1191, -2), (key1210, 6), (key1013, 2), (key999, 2), (key999, 2), (key1148, -2), (key1148, -2), (key1069, -2), (key994, -6), (key1107, 2), (key1107, 2), (key1029, 2)]

def rawRow3521 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1210, -2), (key1197, 6), (key1034, 2), (key1034, 2), (key1069, 2), (key1013, -2), (key1121, -2), (key1121, -2), (key1029, -6), (key994, 2), (key1107, 2), (key1107, 2)]

def rawRow3522 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1191, -2), (key1197, 6), (key1034, 2), (key1069, 2), (key1034, 2), (key1121, -2), (key1013, -2), (key1121, -2), (key1029, -6), (key1107, 2), (key994, 2), (key1107, 2)]

def rawRow3523 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1191, -2), (key1197, 6), (key1069, 2), (key1034, 2), (key1034, 2), (key1121, -2), (key1121, -2), (key1013, -2), (key1029, -6), (key1107, 2), (key1107, 2), (key994, 2)]

def rawRow3524 : Integer.Sparse Key := [(key2634, -6), (key2607, 2), (key2623, 2), (key2623, 2), (key2720, 6), (key2662, -2), (key2697, -2), (key2697, -2), (key2823, -2), (key2864, -2), (key2864, -2), (key2788, 2), (key2854, 2), (key2854, 2)]

def rawRow3525 : Integer.Sparse Key := [(key2634, -6), (key2623, 2), (key2607, 2), (key2623, 2), (key2720, 6), (key2697, -2), (key2662, -2), (key2697, -2), (key2864, -2), (key2823, -2), (key2864, -2), (key2854, 2), (key2788, 2), (key2854, 2)]

def rawRow3526 : Integer.Sparse Key := [(key2634, -6), (key2623, 2), (key2623, 2), (key2607, 2), (key2720, 6), (key2697, -2), (key2697, -2), (key2662, -2), (key2864, -2), (key2864, -2), (key2823, -2), (key2854, 2), (key2854, 2), (key2788, 2)]

def rawRow3527 : Integer.Sparse Key := [(key2788, -6), (key2662, 2), (key2777, 2), (key2777, 2), (key2823, 6), (key2607, -2), (key2800, -2), (key2800, -2), (key2720, -2), (key2864, -2), (key2864, -2), (key2634, 2), (key2854, 2), (key2854, 2)]

def rawRow3528 : Integer.Sparse Key := [(key2788, -6), (key2777, 2), (key2662, 2), (key2777, 2), (key2823, 6), (key2800, -2), (key2607, -2), (key2800, -2), (key2864, -2), (key2720, -2), (key2864, -2), (key2854, 2), (key2634, 2), (key2854, 2)]

def rawRow3529 : Integer.Sparse Key := [(key2788, -6), (key2777, 2), (key2777, 2), (key2662, 2), (key2823, 6), (key2800, -2), (key2800, -2), (key2607, -2), (key2864, -2), (key2864, -2), (key2720, -2), (key2854, 2), (key2854, 2), (key2634, 2)]

def rawRow3530 : Integer.Sparse Key := [(key2720, -6), (key2823, 2), (key2864, 2), (key2864, 2), (key2634, 6), (key2788, -2), (key2854, -2), (key2854, -2), (key2607, -2), (key2623, -2), (key2623, -2), (key2662, 2), (key2697, 2), (key2697, 2)]

def rawRow3531 : Integer.Sparse Key := [(key2720, -6), (key2864, 2), (key2823, 2), (key2864, 2), (key2634, 6), (key2854, -2), (key2788, -2), (key2854, -2), (key2623, -2), (key2607, -2), (key2623, -2), (key2697, 2), (key2662, 2), (key2697, 2)]

def rawRow3532 : Integer.Sparse Key := [(key2720, -6), (key2864, 2), (key2864, 2), (key2823, 2), (key2634, 6), (key2854, -2), (key2854, -2), (key2788, -2), (key2623, -2), (key2623, -2), (key2607, -2), (key2697, 2), (key2697, 2), (key2662, 2)]

def rawRow3533 : Integer.Sparse Key := [(key2823, -6), (key2720, 2), (key2864, 2), (key2864, 2), (key2788, 6), (key2634, -2), (key2854, -2), (key2854, -2), (key2662, -2), (key2777, -2), (key2777, -2), (key2607, 2), (key2800, 2), (key2800, 2)]

def rawRow3534 : Integer.Sparse Key := [(key2823, -6), (key2864, 2), (key2720, 2), (key2864, 2), (key2788, 6), (key2854, -2), (key2634, -2), (key2854, -2), (key2777, -2), (key2662, -2), (key2777, -2), (key2800, 2), (key2607, 2), (key2800, 2)]

def rawRow3535 : Integer.Sparse Key := [(key2823, -6), (key2864, 2), (key2864, 2), (key2720, 2), (key2788, 6), (key2854, -2), (key2854, -2), (key2634, -2), (key2777, -2), (key2777, -2), (key2662, -2), (key2800, 2), (key2800, 2), (key2607, 2)]

def rawRow3536 : Integer.Sparse Key := [(key1392, -1), (key1392, -1), (key1547, -1), (key1547, -1), (key1555, -1), (key1555, -1), (key1387, 2), (key1542, 2), (key1542, 2), (key1456, 1), (key1456, 1), (key1656, 1), (key1656, 1), (key1658, 1), (key1658, 1), (key1420, -1), (key1420, -1), (key1569, -1), (key1569, -1), (key1618, -1), (key1618, -1), (key1465, -2), (key1666, -2), (key1666, -2), (key1443, 1), (key1443, 1), (key1592, 1), (key1592, 1), (key1632, 1), (key1632, 1)]

def rawRow3537 : Integer.Sparse Key := [(key1547, -1), (key1555, -1), (key1392, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1542, 2), (key1387, 2), (key1542, 2), (key1656, 1), (key1658, 1), (key1456, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1569, -1), (key1618, -1), (key1420, -1), (key1618, -1), (key1420, -1), (key1569, -1), (key1666, -2), (key1465, -2), (key1666, -2), (key1592, 1), (key1632, 1), (key1443, 1), (key1632, 1), (key1443, 1), (key1592, 1)]

def rawRow3538 : Integer.Sparse Key := [(key1555, -1), (key1547, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1392, -1), (key1542, 2), (key1542, 2), (key1387, 2), (key1658, 1), (key1656, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1456, 1), (key1618, -1), (key1569, -1), (key1618, -1), (key1420, -1), (key1569, -1), (key1420, -1), (key1666, -2), (key1666, -2), (key1465, -2), (key1632, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1592, 1), (key1443, 1)]

def rawRow3539 : Integer.Sparse Key := [(key1297, -1), (key1297, -1), (key1574, -1), (key1574, -1), (key1592, -1), (key1592, -1), (key1292, 2), (key1569, 2), (key1569, 2), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1), (key1312, -1), (key1312, -1), (key1542, -1), (key1542, -1), (key1618, -1), (key1618, -1), (key1344, -2), (key1658, -2), (key1658, -2), (key1325, 1), (key1325, 1), (key1555, 1), (key1555, 1), (key1623, 1), (key1623, 1)]

def rawRow3540 : Integer.Sparse Key := [(key1574, -1), (key1592, -1), (key1297, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1569, 2), (key1292, 2), (key1569, 2), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1542, -1), (key1618, -1), (key1312, -1), (key1618, -1), (key1312, -1), (key1542, -1), (key1658, -2), (key1344, -2), (key1658, -2), (key1555, 1), (key1623, 1), (key1325, 1), (key1623, 1), (key1325, 1), (key1555, 1)]

def rawRow3541 : Integer.Sparse Key := [(key1592, -1), (key1574, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1297, -1), (key1569, 2), (key1569, 2), (key1292, 2), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1), (key1618, -1), (key1542, -1), (key1618, -1), (key1312, -1), (key1542, -1), (key1312, -1), (key1658, -2), (key1658, -2), (key1344, -2), (key1623, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1555, 1), (key1325, 1)]

def rawRow3542 : Integer.Sparse Key := [(key1456, -1), (key1456, -1), (key1656, -1), (key1656, -1), (key1658, -1), (key1658, -1), (key1465, 2), (key1666, 2), (key1666, 2), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1), (key1443, -1), (key1443, -1), (key1592, -1), (key1592, -1), (key1632, -1), (key1632, -1), (key1387, -2), (key1542, -2), (key1542, -2), (key1420, 1), (key1420, 1), (key1569, 1), (key1569, 1), (key1618, 1), (key1618, 1)]

def rawRow3543 : Integer.Sparse Key := [(key1656, -1), (key1658, -1), (key1456, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1666, 2), (key1465, 2), (key1666, 2), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1592, -1), (key1632, -1), (key1443, -1), (key1632, -1), (key1443, -1), (key1592, -1), (key1542, -2), (key1387, -2), (key1542, -2), (key1569, 1), (key1618, 1), (key1420, 1), (key1618, 1), (key1420, 1), (key1569, 1)]

def rawRow3544 : Integer.Sparse Key := [(key1658, -1), (key1656, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1456, -1), (key1666, 2), (key1666, 2), (key1465, 2), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1), (key1632, -1), (key1592, -1), (key1632, -1), (key1443, -1), (key1592, -1), (key1443, -1), (key1542, -2), (key1542, -2), (key1387, -2), (key1618, 1), (key1569, 1), (key1618, 1), (key1420, 1), (key1569, 1), (key1420, 1)]

def rawRow3545 : Integer.Sparse Key := [(key1338, -1), (key1338, -1), (key1656, -1), (key1656, -1), (key1666, -1), (key1666, -1), (key1344, 2), (key1658, 2), (key1658, 2), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1), (key1325, -1), (key1325, -1), (key1555, -1), (key1555, -1), (key1623, -1), (key1623, -1), (key1292, -2), (key1569, -2), (key1569, -2), (key1312, 1), (key1312, 1), (key1542, 1), (key1542, 1), (key1618, 1), (key1618, 1)]

def rawRow3546 : Integer.Sparse Key := [(key1656, -1), (key1666, -1), (key1338, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1658, 2), (key1344, 2), (key1658, 2), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1555, -1), (key1623, -1), (key1325, -1), (key1623, -1), (key1325, -1), (key1555, -1), (key1569, -2), (key1292, -2), (key1569, -2), (key1542, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1542, 1)]

def rawRow3547 : Integer.Sparse Key := [(key1666, -1), (key1656, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1338, -1), (key1658, 2), (key1658, 2), (key1344, 2), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1), (key1623, -1), (key1555, -1), (key1623, -1), (key1325, -1), (key1555, -1), (key1325, -1), (key1569, -2), (key1569, -2), (key1292, -2), (key1618, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1542, 1), (key1312, 1)]

def rawRow3548 : Integer.Sparse Key := [(key3052, -2), (key3052, -2), (key3067, -2), (key3048, 2), (key3048, 2), (key3062, 2), (key3108, 2), (key3108, 2), (key3135, 2), (key3097, -6), (key3111, -2), (key3111, -2), (key3137, -2), (key3104, 6)]

def rawRow3549 : Integer.Sparse Key := [(key3052, -2), (key3067, -2), (key3052, -2), (key3048, 2), (key3062, 2), (key3048, 2), (key3108, 2), (key3135, 2), (key3108, 2), (key3097, -6), (key3111, -2), (key3137, -2), (key3111, -2), (key3104, 6)]

def rawRow3550 : Integer.Sparse Key := [(key3067, -2), (key3052, -2), (key3052, -2), (key3062, 2), (key3048, 2), (key3048, 2), (key3135, 2), (key3108, 2), (key3108, 2), (key3097, -6), (key3137, -2), (key3111, -2), (key3111, -2), (key3104, 6)]

def rawRow3551 : Integer.Sparse Key := [(key3052, -2), (key3052, -2), (key3104, -2), (key3048, 2), (key3048, 2), (key3097, 2), (key3071, 2), (key3071, 2), (key3137, 2), (key3062, -6), (key3073, -2), (key3073, -2), (key3135, -2), (key3067, 6)]

def rawRow3552 : Integer.Sparse Key := [(key3052, -2), (key3104, -2), (key3052, -2), (key3048, 2), (key3097, 2), (key3048, 2), (key3071, 2), (key3137, 2), (key3071, 2), (key3062, -6), (key3073, -2), (key3135, -2), (key3073, -2), (key3067, 6)]

def rawRow3553 : Integer.Sparse Key := [(key3104, -2), (key3052, -2), (key3052, -2), (key3097, 2), (key3048, 2), (key3048, 2), (key3137, 2), (key3071, 2), (key3071, 2), (key3062, -6), (key3135, -2), (key3073, -2), (key3073, -2), (key3067, 6)]

def rawRow3554 : Integer.Sparse Key := [(key3108, -2), (key3108, -2), (key3135, -2), (key3111, 2), (key3111, 2), (key3137, 2), (key3052, 2), (key3052, 2), (key3067, 2), (key3104, -6), (key3048, -2), (key3048, -2), (key3062, -2), (key3097, 6)]

def rawRow3555 : Integer.Sparse Key := [(key3108, -2), (key3135, -2), (key3108, -2), (key3111, 2), (key3137, 2), (key3111, 2), (key3052, 2), (key3067, 2), (key3052, 2), (key3104, -6), (key3048, -2), (key3062, -2), (key3048, -2), (key3097, 6)]

def rawRow3556 : Integer.Sparse Key := [(key3135, -2), (key3108, -2), (key3108, -2), (key3137, 2), (key3111, 2), (key3111, 2), (key3067, 2), (key3052, 2), (key3052, 2), (key3104, -6), (key3062, -2), (key3048, -2), (key3048, -2), (key3097, 6)]

def rawRow3557 : Integer.Sparse Key := [(key3071, -2), (key3071, -2), (key3137, -2), (key3073, 2), (key3073, 2), (key3135, 2), (key3052, 2), (key3052, 2), (key3104, 2), (key3067, -6), (key3048, -2), (key3048, -2), (key3097, -2), (key3062, 6)]

def rawRow3558 : Integer.Sparse Key := [(key3071, -2), (key3137, -2), (key3071, -2), (key3073, 2), (key3135, 2), (key3073, 2), (key3052, 2), (key3104, 2), (key3052, 2), (key3067, -6), (key3048, -2), (key3097, -2), (key3048, -2), (key3062, 6)]

def rawRow3559 : Integer.Sparse Key := [(key3137, -2), (key3071, -2), (key3071, -2), (key3135, 2), (key3073, 2), (key3073, 2), (key3104, 2), (key3052, 2), (key3052, 2), (key3067, -6), (key3097, -2), (key3048, -2), (key3048, -2), (key3062, 6)]

def rawRow3560 : Integer.Sparse Key := [(key1338, -2), (key1338, -2), (key1344, -2), (key1297, 1), (key1297, 1), (key1317, 1), (key1317, 1), (key1325, 1), (key1325, 1), (key1773, 2), (key1773, 2), (key1779, 2), (key1392, -1), (key1392, -1), (key1547, -1), (key1547, -1), (key1555, -1), (key1555, -1), (key1789, -1), (key1789, -1), (key1814, -1), (key1814, -1), (key1816, -1), (key1816, -1), (key1456, 1), (key1456, 1), (key1656, 1), (key1656, 1), (key1658, 1), (key1658, 1)]

def rawRow3561 : Integer.Sparse Key := [(key1338, -2), (key1344, -2), (key1338, -2), (key1317, 1), (key1325, 1), (key1297, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1773, 2), (key1779, 2), (key1773, 2), (key1547, -1), (key1555, -1), (key1392, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1814, -1), (key1816, -1), (key1789, -1), (key1816, -1), (key1789, -1), (key1814, -1), (key1656, 1), (key1658, 1), (key1456, 1), (key1658, 1), (key1456, 1), (key1656, 1)]

def rawRow3562 : Integer.Sparse Key := [(key1344, -2), (key1338, -2), (key1338, -2), (key1325, 1), (key1317, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1297, 1), (key1779, 2), (key1773, 2), (key1773, 2), (key1555, -1), (key1547, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1392, -1), (key1816, -1), (key1814, -1), (key1816, -1), (key1789, -1), (key1814, -1), (key1789, -1), (key1658, 1), (key1656, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1456, 1)]

def rawRow3563 : Integer.Sparse Key := [(key1456, -2), (key1456, -2), (key1465, -2), (key1392, 1), (key1392, 1), (key1425, 1), (key1425, 1), (key1443, 1), (key1443, 1), (key1789, 2), (key1789, 2), (key1797, 2), (key1297, -1), (key1297, -1), (key1574, -1), (key1574, -1), (key1592, -1), (key1592, -1), (key1773, -1), (key1773, -1), (key1814, -1), (key1814, -1), (key1824, -1), (key1824, -1), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1)]

def rawRow3564 : Integer.Sparse Key := [(key1456, -2), (key1465, -2), (key1456, -2), (key1425, 1), (key1443, 1), (key1392, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1789, 2), (key1797, 2), (key1789, 2), (key1574, -1), (key1592, -1), (key1297, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1814, -1), (key1824, -1), (key1773, -1), (key1824, -1), (key1773, -1), (key1814, -1), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1)]

def rawRow3565 : Integer.Sparse Key := [(key1465, -2), (key1456, -2), (key1456, -2), (key1443, 1), (key1425, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1392, 1), (key1797, 2), (key1789, 2), (key1789, 2), (key1592, -1), (key1574, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1297, -1), (key1824, -1), (key1814, -1), (key1824, -1), (key1773, -1), (key1814, -1), (key1773, -1), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1)]

def rawRow3566 : Integer.Sparse Key := [(key1773, -2), (key1773, -2), (key1779, -2), (key1789, 1), (key1789, 1), (key1814, 1), (key1814, 1), (key1816, 1), (key1816, 1), (key1338, 2), (key1338, 2), (key1344, 2), (key1456, -1), (key1456, -1), (key1656, -1), (key1656, -1), (key1658, -1), (key1658, -1), (key1297, -1), (key1297, -1), (key1317, -1), (key1317, -1), (key1325, -1), (key1325, -1), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1)]

def rawRow3567 : Integer.Sparse Key := [(key1773, -2), (key1779, -2), (key1773, -2), (key1814, 1), (key1816, 1), (key1789, 1), (key1816, 1), (key1789, 1), (key1814, 1), (key1338, 2), (key1344, 2), (key1338, 2), (key1656, -1), (key1658, -1), (key1456, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1317, -1), (key1325, -1), (key1297, -1), (key1325, -1), (key1297, -1), (key1317, -1), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1)]

def rawRow3568 : Integer.Sparse Key := [(key1779, -2), (key1773, -2), (key1773, -2), (key1816, 1), (key1814, 1), (key1816, 1), (key1789, 1), (key1814, 1), (key1789, 1), (key1344, 2), (key1338, 2), (key1338, 2), (key1658, -1), (key1656, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1456, -1), (key1325, -1), (key1317, -1), (key1325, -1), (key1297, -1), (key1317, -1), (key1297, -1), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1)]

def rawRow3569 : Integer.Sparse Key := [(key1789, -2), (key1789, -2), (key1797, -2), (key1773, 1), (key1773, 1), (key1814, 1), (key1814, 1), (key1824, 1), (key1824, 1), (key1456, 2), (key1456, 2), (key1465, 2), (key1338, -1), (key1338, -1), (key1656, -1), (key1656, -1), (key1666, -1), (key1666, -1), (key1392, -1), (key1392, -1), (key1425, -1), (key1425, -1), (key1443, -1), (key1443, -1), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1)]

def rawRow3570 : Integer.Sparse Key := [(key1789, -2), (key1797, -2), (key1789, -2), (key1814, 1), (key1824, 1), (key1773, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1456, 2), (key1465, 2), (key1456, 2), (key1656, -1), (key1666, -1), (key1338, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1425, -1), (key1443, -1), (key1392, -1), (key1443, -1), (key1392, -1), (key1425, -1), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1)]

def rawRow3571 : Integer.Sparse Key := [(key1797, -2), (key1789, -2), (key1789, -2), (key1824, 1), (key1814, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1773, 1), (key1465, 2), (key1456, 2), (key1456, 2), (key1666, -1), (key1656, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1338, -1), (key1443, -1), (key1425, -1), (key1443, -1), (key1392, -1), (key1425, -1), (key1392, -1), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1)]

def rawRow3572 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key1012, -2), (key993, 6), (key1189, 2), (key1189, 2), (key1196, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1209, -6), (key1068, 2), (key1147, 2), (key1147, 2)]

def rawRow3573 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key997, -2), (key993, 6), (key1189, 2), (key1196, 2), (key1189, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1209, -6), (key1147, 2), (key1068, 2), (key1147, 2)]

def rawRow3574 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key997, -2), (key993, 6), (key1196, 2), (key1189, 2), (key1189, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1209, -6), (key1147, 2), (key1147, 2), (key1068, 2)]

def rawRow3575 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1068, -2), (key1028, 6), (key1189, 2), (key1189, 2), (key1209, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1196, -6), (key1012, 2), (key1120, 2), (key1120, 2)]

def rawRow3576 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1032, -2), (key1028, 6), (key1189, 2), (key1209, 2), (key1189, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1196, -6), (key1120, 2), (key1012, 2), (key1120, 2)]

def rawRow3577 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1032, -2), (key1028, 6), (key1209, 2), (key1189, 2), (key1189, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1196, -6), (key1120, 2), (key1120, 2), (key1012, 2)]

def rawRow3578 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1196, -2), (key1209, 6), (key997, 2), (key997, 2), (key1012, 2), (key1068, -2), (key1147, -2), (key1147, -2), (key993, -6), (key1028, 2), (key1106, 2), (key1106, 2)]

def rawRow3579 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1189, -2), (key1209, 6), (key997, 2), (key1012, 2), (key997, 2), (key1147, -2), (key1068, -2), (key1147, -2), (key993, -6), (key1106, 2), (key1028, 2), (key1106, 2)]

def rawRow3580 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1189, -2), (key1209, 6), (key1012, 2), (key997, 2), (key997, 2), (key1147, -2), (key1147, -2), (key1068, -2), (key993, -6), (key1106, 2), (key1106, 2), (key1028, 2)]

def rawRow3581 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1209, -2), (key1196, 6), (key1032, 2), (key1032, 2), (key1068, 2), (key1012, -2), (key1120, -2), (key1120, -2), (key1028, -6), (key993, 2), (key1106, 2), (key1106, 2)]

def rawRow3582 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1189, -2), (key1196, 6), (key1032, 2), (key1068, 2), (key1032, 2), (key1120, -2), (key1012, -2), (key1120, -2), (key1028, -6), (key1106, 2), (key993, 2), (key1106, 2)]

def rawRow3583 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1189, -2), (key1196, 6), (key1068, 2), (key1032, 2), (key1032, 2), (key1120, -2), (key1120, -2), (key1012, -2), (key1028, -6), (key1106, 2), (key1106, 2), (key993, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3584 : Integer.Sparse Key := [(key2619, -2), (key2642, -2), (key2642, -2), (key2616, 1), (key2616, 1), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2951, 2), (key2977, 2), (key2977, 2), (key2706, -1), (key2706, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2961, -1), (key2961, -1), (key2984, -1), (key2984, -1), (key2992, -1), (key2992, -1), (key2729, 1), (key2729, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

def rawRow3585 : Integer.Sparse Key := [(key2642, -2), (key2619, -2), (key2642, -2), (key2632, 1), (key2640, 1), (key2616, 1), (key2640, 1), (key2616, 1), (key2632, 1), (key2977, 2), (key2951, 2), (key2977, 2), (key2809, -1), (key2860, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2984, -1), (key2992, -1), (key2961, -1), (key2992, -1), (key2961, -1), (key2984, -1), (key2832, 1), (key2883, 1), (key2729, 1), (key2883, 1), (key2729, 1), (key2832, 1)]

def rawRow3586 : Integer.Sparse Key := [(key2642, -2), (key2642, -2), (key2619, -2), (key2640, 1), (key2632, 1), (key2640, 1), (key2616, 1), (key2632, 1), (key2616, 1), (key2977, 2), (key2977, 2), (key2951, 2), (key2860, -1), (key2809, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2706, -1), (key2992, -1), (key2984, -1), (key2992, -1), (key2961, -1), (key2984, -1), (key2961, -1), (key2883, 1), (key2832, 1), (key2883, 1), (key2729, 1), (key2832, 1), (key2729, 1)]

def rawRow3587 : Integer.Sparse Key := [(key2674, -2), (key2729, -2), (key2729, -2), (key2671, 1), (key2671, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2939, 2), (key2984, 2), (key2984, 2), (key2632, -1), (key2632, -1), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2944, -1), (key2944, -1), (key2977, -1), (key2977, -1), (key2992, -1), (key2992, -1), (key2642, 1), (key2642, 1), (key2796, 1), (key2796, 1), (key2883, 1), (key2883, 1)]

def rawRow3588 : Integer.Sparse Key := [(key2729, -2), (key2674, -2), (key2729, -2), (key2706, 1), (key2726, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2984, 2), (key2939, 2), (key2984, 2), (key2786, -1), (key2870, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2977, -1), (key2992, -1), (key2944, -1), (key2992, -1), (key2944, -1), (key2977, -1), (key2796, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2796, 1)]

def rawRow3589 : Integer.Sparse Key := [(key2729, -2), (key2729, -2), (key2674, -2), (key2726, 1), (key2706, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2671, 1), (key2984, 2), (key2984, 2), (key2939, 2), (key2870, -1), (key2786, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2632, -1), (key2992, -1), (key2977, -1), (key2992, -1), (key2944, -1), (key2977, -1), (key2944, -1), (key2883, 1), (key2796, 1), (key2883, 1), (key2642, 1), (key2796, 1), (key2642, 1)]

def rawRow3590 : Integer.Sparse Key := [(key2951, -2), (key2977, -2), (key2977, -2), (key2961, 1), (key2961, 1), (key2984, 1), (key2984, 1), (key2992, 1), (key2992, 1), (key2619, 2), (key2642, 2), (key2642, 2), (key2729, -1), (key2729, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2616, -1), (key2616, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2706, 1), (key2706, 1), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1)]

def rawRow3591 : Integer.Sparse Key := [(key2977, -2), (key2951, -2), (key2977, -2), (key2984, 1), (key2992, 1), (key2961, 1), (key2992, 1), (key2961, 1), (key2984, 1), (key2642, 2), (key2619, 2), (key2642, 2), (key2832, -1), (key2883, -1), (key2729, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2632, -1), (key2640, -1), (key2616, -1), (key2640, -1), (key2616, -1), (key2632, -1), (key2809, 1), (key2860, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2809, 1)]

def rawRow3592 : Integer.Sparse Key := [(key2977, -2), (key2977, -2), (key2951, -2), (key2992, 1), (key2984, 1), (key2992, 1), (key2961, 1), (key2984, 1), (key2961, 1), (key2642, 2), (key2642, 2), (key2619, 2), (key2883, -1), (key2832, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2729, -1), (key2640, -1), (key2632, -1), (key2640, -1), (key2616, -1), (key2632, -1), (key2616, -1), (key2860, 1), (key2809, 1), (key2860, 1), (key2706, 1), (key2809, 1), (key2706, 1)]

def rawRow3593 : Integer.Sparse Key := [(key2939, -2), (key2984, -2), (key2984, -2), (key2944, 1), (key2944, 1), (key2977, 1), (key2977, 1), (key2992, 1), (key2992, 1), (key2674, 2), (key2729, 2), (key2729, 2), (key2642, -1), (key2642, -1), (key2796, -1), (key2796, -1), (key2883, -1), (key2883, -1), (key2671, -1), (key2671, -1), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3594 : Integer.Sparse Key := [(key2984, -2), (key2939, -2), (key2984, -2), (key2977, 1), (key2992, 1), (key2944, 1), (key2992, 1), (key2944, 1), (key2977, 1), (key2729, 2), (key2674, 2), (key2729, 2), (key2796, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3595 : Integer.Sparse Key := [(key2984, -2), (key2984, -2), (key2939, -2), (key2992, 1), (key2977, 1), (key2992, 1), (key2944, 1), (key2977, 1), (key2944, 1), (key2729, 2), (key2729, 2), (key2674, 2), (key2883, -1), (key2796, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2642, -1), (key2726, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2671, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3596 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2387, -2), (key2371, 6), (key2536, 2), (key2536, 2), (key2541, 2), (key2399, -2), (key2465, -2), (key2465, -2), (key2552, -6), (key2434, 2), (key2500, 2), (key2500, 2)]

def rawRow3597 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2375, -2), (key2371, 6), (key2536, 2), (key2541, 2), (key2536, 2), (key2465, -2), (key2399, -2), (key2465, -2), (key2552, -6), (key2500, 2), (key2434, 2), (key2500, 2)]

def rawRow3598 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2375, -2), (key2371, 6), (key2541, 2), (key2536, 2), (key2536, 2), (key2465, -2), (key2465, -2), (key2399, -2), (key2552, -6), (key2500, 2), (key2500, 2), (key2434, 2)]

def rawRow3599 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2434, -2), (key2399, 6), (key2536, 2), (key2536, 2), (key2552, 2), (key2371, -2), (key2465, -2), (key2465, -2), (key2541, -6), (key2387, 2), (key2477, 2), (key2477, 2)]

def rawRow3600 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2403, -2), (key2399, 6), (key2536, 2), (key2552, 2), (key2536, 2), (key2465, -2), (key2371, -2), (key2465, -2), (key2541, -6), (key2477, 2), (key2387, 2), (key2477, 2)]

def rawRow3601 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2403, -2), (key2399, 6), (key2552, 2), (key2536, 2), (key2536, 2), (key2465, -2), (key2465, -2), (key2371, -2), (key2541, -6), (key2477, 2), (key2477, 2), (key2387, 2)]

def rawRow3602 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2541, -2), (key2552, 6), (key2375, 2), (key2375, 2), (key2387, 2), (key2434, -2), (key2500, -2), (key2500, -2), (key2371, -6), (key2399, 2), (key2465, 2), (key2465, 2)]

def rawRow3603 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2536, -2), (key2552, 6), (key2375, 2), (key2387, 2), (key2375, 2), (key2500, -2), (key2434, -2), (key2500, -2), (key2371, -6), (key2465, 2), (key2399, 2), (key2465, 2)]

def rawRow3604 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2536, -2), (key2552, 6), (key2387, 2), (key2375, 2), (key2375, 2), (key2500, -2), (key2500, -2), (key2434, -2), (key2371, -6), (key2465, 2), (key2465, 2), (key2399, 2)]

def rawRow3605 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2552, -2), (key2541, 6), (key2403, 2), (key2403, 2), (key2434, 2), (key2387, -2), (key2477, -2), (key2477, -2), (key2399, -6), (key2371, 2), (key2465, 2), (key2465, 2)]

def rawRow3606 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2536, -2), (key2541, 6), (key2403, 2), (key2434, 2), (key2403, 2), (key2477, -2), (key2387, -2), (key2477, -2), (key2399, -6), (key2465, 2), (key2371, 2), (key2465, 2)]

def rawRow3607 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2536, -2), (key2541, 6), (key2434, 2), (key2403, 2), (key2403, 2), (key2477, -2), (key2477, -2), (key2387, -2), (key2399, -6), (key2465, 2), (key2465, 2), (key2371, 2)]

def rawRow3608 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2386, -2), (key2370, 6), (key2874, 2), (key2874, 2), (key2908, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key2987, -6), (key2928, 2), (key2965, 2), (key2965, 2)]

def rawRow3609 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2373, -2), (key2370, 6), (key2874, 2), (key2908, 2), (key2874, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key2987, -6), (key2965, 2), (key2928, 2), (key2965, 2)]

def rawRow3610 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2373, -2), (key2370, 6), (key2908, 2), (key2874, 2), (key2874, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key2987, -6), (key2965, 2), (key2965, 2), (key2928, 2)]

def rawRow3611 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2433, -2), (key2398, 6), (key2874, 2), (key2874, 2), (key2987, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2908, -6), (key2597, 2), (key2886, 2), (key2886, 2)]

def rawRow3612 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2401, -2), (key2398, 6), (key2874, 2), (key2987, 2), (key2874, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2908, -6), (key2886, 2), (key2597, 2), (key2886, 2)]

def rawRow3613 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2401, -2), (key2398, 6), (key2987, 2), (key2874, 2), (key2874, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2908, -6), (key2886, 2), (key2886, 2), (key2597, 2)]

def rawRow3614 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2540, -2), (key2551, 6), (key2373, 2), (key2373, 2), (key2386, 2), (key2433, -2), (key2499, -2), (key2499, -2), (key2370, -6), (key2762, 2), (key2839, 2), (key2839, 2)]

def rawRow3615 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2534, -2), (key2551, 6), (key2373, 2), (key2386, 2), (key2373, 2), (key2499, -2), (key2433, -2), (key2499, -2), (key2370, -6), (key2839, 2), (key2762, 2), (key2839, 2)]

def rawRow3616 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2534, -2), (key2551, 6), (key2386, 2), (key2373, 2), (key2373, 2), (key2499, -2), (key2499, -2), (key2433, -2), (key2370, -6), (key2839, 2), (key2839, 2), (key2762, 2)]

def rawRow3617 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2551, -2), (key2540, 6), (key2401, 2), (key2401, 2), (key2433, 2), (key2386, -2), (key2476, -2), (key2476, -2), (key2398, -6), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow3618 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2534, -2), (key2540, 6), (key2401, 2), (key2433, 2), (key2401, 2), (key2476, -2), (key2386, -2), (key2476, -2), (key2398, -6), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow3619 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2534, -2), (key2540, 6), (key2433, 2), (key2401, 2), (key2401, 2), (key2476, -2), (key2476, -2), (key2386, -2), (key2398, -6), (key2839, 2), (key2839, 2), (key2583, 2)]

def rawRow3620 : Integer.Sparse Key := [(key2645, -2), (key2645, -2), (key2651, -2), (key2611, 1), (key2611, 1), (key2627, 1), (key2627, 1), (key2636, 1), (key2636, 1), (key2722, 2), (key2722, 2), (key2745, 2), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2734, -1), (key2734, -1), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2902, -1), (key2902, -1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2895, 1), (key2895, 1)]

def rawRow3621 : Integer.Sparse Key := [(key2645, -2), (key2651, -2), (key2645, -2), (key2627, 1), (key2636, 1), (key2611, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2722, 2), (key2745, 2), (key2722, 2), (key2701, -1), (key2734, -1), (key2666, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2856, 1), (key2895, 1), (key2790, 1), (key2895, 1), (key2790, 1), (key2856, 1)]

def rawRow3622 : Integer.Sparse Key := [(key2651, -2), (key2645, -2), (key2645, -2), (key2636, 1), (key2627, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2611, 1), (key2745, 2), (key2722, 2), (key2722, 2), (key2734, -1), (key2701, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2902, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2825, -1), (key2895, 1), (key2856, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2790, 1)]

def rawRow3623 : Integer.Sparse Key := [(key2734, -2), (key2734, -2), (key2745, -2), (key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2722, 1), (key2722, 1), (key2947, 2), (key2947, 2), (key2958, 2), (key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2722, -1), (key2722, -1), (key2866, -1), (key2866, -1), (key2981, -1), (key2981, -1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1)]

def rawRow3624 : Integer.Sparse Key := [(key2734, -2), (key2745, -2), (key2734, -2), (key2701, 1), (key2722, 1), (key2666, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2947, 2), (key2958, 2), (key2947, 2), (key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1)]

def rawRow3625 : Integer.Sparse Key := [(key2745, -2), (key2734, -2), (key2734, -2), (key2722, 1), (key2701, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2958, 2), (key2947, 2), (key2947, 2), (key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2981, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1)]

def rawRow3626 : Integer.Sparse Key := [(key2935, -2), (key2935, -2), (key2941, -2), (key2947, 1), (key2947, 1), (key2971, 1), (key2971, 1), (key2974, 1), (key2974, 1), (key2645, 2), (key2645, 2), (key2651, 2), (key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1), (key2895, -1), (key2895, -1), (key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1)]

def rawRow3627 : Integer.Sparse Key := [(key2935, -2), (key2941, -2), (key2935, -2), (key2971, 1), (key2974, 1), (key2947, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2645, 2), (key2651, 2), (key2645, 2), (key2892, -1), (key2895, -1), (key2734, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1)]

def rawRow3628 : Integer.Sparse Key := [(key2941, -2), (key2935, -2), (key2935, -2), (key2974, 1), (key2971, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2947, 1), (key2651, 2), (key2645, 2), (key2645, 2), (key2895, -1), (key2892, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2734, -1), (key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1)]

def rawRow3629 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2935, 1), (key2935, 1), (key2971, 1), (key2971, 1), (key2981, 1), (key2981, 1), (key2734, 2), (key2734, 2), (key2745, 2), (key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1)]

def rawRow3630 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2971, 1), (key2981, 1), (key2935, 1), (key2981, 1), (key2935, 1), (key2971, 1), (key2734, 2), (key2745, 2), (key2734, 2), (key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1)]

def rawRow3631 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2981, 1), (key2971, 1), (key2981, 1), (key2935, 1), (key2971, 1), (key2935, 1), (key2745, 2), (key2734, 2), (key2734, 2), (key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1)]

def rawRow3632 : Integer.Sparse Key := [(key2091, -2), (key2092, -2), (key2092, -2), (key2095, 6), (key2193, 2), (key2194, 2), (key2194, 2), (key2305, -2), (key2305, -2), (key2343, -2), (key2200, -6), (key2310, 2), (key2310, 2), (key2347, 2)]

def rawRow3633 : Integer.Sparse Key := [(key2092, -2), (key2091, -2), (key2092, -2), (key2095, 6), (key2194, 2), (key2193, 2), (key2194, 2), (key2305, -2), (key2343, -2), (key2305, -2), (key2200, -6), (key2310, 2), (key2347, 2), (key2310, 2)]

def rawRow3634 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2091, -2), (key2095, 6), (key2194, 2), (key2194, 2), (key2193, 2), (key2343, -2), (key2305, -2), (key2305, -2), (key2200, -6), (key2347, 2), (key2310, 2), (key2310, 2)]

def rawRow3635 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2095, -2), (key2091, 6), (key2341, 2), (key2341, 2), (key2343, 2), (key2193, -2), (key2302, -2), (key2302, -2), (key2347, -6), (key2200, 2), (key2310, 2), (key2310, 2)]

def rawRow3636 : Integer.Sparse Key := [(key2092, -2), (key2095, -2), (key2092, -2), (key2091, 6), (key2341, 2), (key2343, 2), (key2341, 2), (key2302, -2), (key2193, -2), (key2302, -2), (key2347, -6), (key2310, 2), (key2200, 2), (key2310, 2)]

def rawRow3637 : Integer.Sparse Key := [(key2095, -2), (key2092, -2), (key2092, -2), (key2091, 6), (key2343, 2), (key2341, 2), (key2341, 2), (key2302, -2), (key2302, -2), (key2193, -2), (key2347, -6), (key2310, 2), (key2310, 2), (key2200, 2)]

def rawRow3638 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2194, -2), (key2200, 6), (key2091, 2), (key2092, 2), (key2092, 2), (key2310, -2), (key2310, -2), (key2347, -2), (key2095, -6), (key2305, 2), (key2305, 2), (key2343, 2)]

def rawRow3639 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2194, -2), (key2200, 6), (key2092, 2), (key2091, 2), (key2092, 2), (key2310, -2), (key2347, -2), (key2310, -2), (key2095, -6), (key2305, 2), (key2343, 2), (key2305, 2)]

def rawRow3640 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2193, -2), (key2200, 6), (key2092, 2), (key2092, 2), (key2091, 2), (key2347, -2), (key2310, -2), (key2310, -2), (key2095, -6), (key2343, 2), (key2305, 2), (key2305, 2)]

def rawRow3641 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2200, -2), (key2193, 6), (key2341, 2), (key2341, 2), (key2347, 2), (key2091, -2), (key2302, -2), (key2302, -2), (key2343, -6), (key2095, 2), (key2305, 2), (key2305, 2)]

def rawRow3642 : Integer.Sparse Key := [(key2194, -2), (key2200, -2), (key2194, -2), (key2193, 6), (key2341, 2), (key2347, 2), (key2341, 2), (key2302, -2), (key2091, -2), (key2302, -2), (key2343, -6), (key2305, 2), (key2095, 2), (key2305, 2)]

def rawRow3643 : Integer.Sparse Key := [(key2200, -2), (key2194, -2), (key2194, -2), (key2193, 6), (key2347, 2), (key2341, 2), (key2341, 2), (key2302, -2), (key2302, -2), (key2091, -2), (key2343, -6), (key2305, 2), (key2305, 2), (key2095, 2)]

def rawRow3644 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2343, -2), (key2347, 6), (key2092, 2), (key2092, 2), (key2095, 2), (key2200, -2), (key2310, -2), (key2310, -2), (key2091, -6), (key2193, 2), (key2302, 2), (key2302, 2)]

def rawRow3645 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2341, -2), (key2347, 6), (key2092, 2), (key2095, 2), (key2092, 2), (key2310, -2), (key2200, -2), (key2310, -2), (key2091, -6), (key2302, 2), (key2193, 2), (key2302, 2)]

def rawRow3646 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2341, -2), (key2347, 6), (key2095, 2), (key2092, 2), (key2092, 2), (key2310, -2), (key2310, -2), (key2200, -2), (key2091, -6), (key2302, 2), (key2302, 2), (key2193, 2)]

def rawRow3647 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2347, -2), (key2343, 6), (key2194, 2), (key2194, 2), (key2200, 2), (key2095, -2), (key2305, -2), (key2305, -2), (key2193, -6), (key2091, 2), (key2302, 2), (key2302, 2)]

def rawRow3648 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2341, -2), (key2343, 6), (key2194, 2), (key2200, 2), (key2194, 2), (key2305, -2), (key2095, -2), (key2305, -2), (key2193, -6), (key2302, 2), (key2091, 2), (key2302, 2)]

def rawRow3649 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2341, -2), (key2343, 6), (key2200, 2), (key2194, 2), (key2194, 2), (key2305, -2), (key2305, -2), (key2095, -2), (key2193, -6), (key2302, 2), (key2302, 2), (key2091, 2)]

def rawRow3650 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2392, 2), (key2406, 2), (key2406, 2), (key2409, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2543, -1), (key2482, -1), (key2543, -1), (key2437, -2), (key2440, -2), (key2440, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2554, 1), (key2506, 1), (key2554, 1)]

def rawRow3651 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2392, 2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2406, 2), (key2482, -1), (key2480, -1), (key2543, -1), (key2480, -1), (key2543, -1), (key2482, -1), (key2440, -2), (key2437, -2), (key2440, -2), (key2506, 1), (key2503, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2506, 1)]

def rawRow3652 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2392, 2), (key2392, 2), (key2390, 2), (key2409, 2), (key2406, 2), (key2406, 2), (key2543, -1), (key2543, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2440, -2), (key2440, -2), (key2437, -2), (key2554, 1), (key2554, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1)]

def rawRow3653 : Integer.Sparse Key := [(key2381, -2), (key2392, -2), (key2392, -2), (key2378, 2), (key2378, 2), (key2390, 2), (key2538, 2), (key2543, 2), (key2543, 2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2554, -2), (key2554, -2), (key2563, -2), (key2440, 1), (key2440, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1)]

def rawRow3654 : Integer.Sparse Key := [(key2392, -2), (key2381, -2), (key2392, -2), (key2378, 2), (key2390, 2), (key2378, 2), (key2543, 2), (key2538, 2), (key2543, 2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2554, -2), (key2563, -2), (key2554, -2), (key2506, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2440, 1), (key2506, 1)]

def rawRow3655 : Integer.Sparse Key := [(key2392, -2), (key2392, -2), (key2381, -2), (key2390, 2), (key2378, 2), (key2378, 2), (key2543, 2), (key2543, 2), (key2538, 2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2563, -2), (key2554, -2), (key2554, -2), (key2522, 1), (key2506, 1), (key2522, 1), (key2440, 1), (key2506, 1), (key2440, 1)]

def rawRow3656 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2440, 2), (key2378, 2), (key2378, 2), (key2381, 2), (key2503, -1), (key2506, -1), (key2503, -1), (key2554, -1), (key2506, -1), (key2554, -1), (key2390, -2), (key2392, -2), (key2392, -2), (key2480, 1), (key2482, 1), (key2480, 1), (key2543, 1), (key2482, 1), (key2543, 1)]

def rawRow3657 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2440, 2), (key2437, 2), (key2440, 2), (key2378, 2), (key2381, 2), (key2378, 2), (key2506, -1), (key2503, -1), (key2554, -1), (key2503, -1), (key2554, -1), (key2506, -1), (key2392, -2), (key2390, -2), (key2392, -2), (key2482, 1), (key2480, 1), (key2543, 1), (key2480, 1), (key2543, 1), (key2482, 1)]

def rawRow3658 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2440, 2), (key2440, 2), (key2437, 2), (key2381, 2), (key2378, 2), (key2378, 2), (key2554, -1), (key2554, -1), (key2506, -1), (key2506, -1), (key2503, -1), (key2503, -1), (key2392, -2), (key2392, -2), (key2390, -2), (key2543, 1), (key2543, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1)]

def rawRow3659 : Integer.Sparse Key := [(key2409, -2), (key2440, -2), (key2440, -2), (key2406, 2), (key2406, 2), (key2437, 2), (key2538, 2), (key2554, 2), (key2554, 2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, 1), (key2392, 1), (key2482, 1), (key2482, 1), (key2522, 1), (key2522, 1)]

def rawRow3660 : Integer.Sparse Key := [(key2440, -2), (key2409, -2), (key2440, -2), (key2406, 2), (key2437, 2), (key2406, 2), (key2554, 2), (key2538, 2), (key2554, 2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2482, 1)]

def rawRow3661 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2409, -2), (key2437, 2), (key2406, 2), (key2406, 2), (key2554, 2), (key2554, 2), (key2538, 2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, 1), (key2482, 1), (key2522, 1), (key2392, 1), (key2482, 1), (key2392, 1)]

def rawRow3662 : Integer.Sparse Key := [(key2538, -2), (key2543, -2), (key2543, -2), (key2554, 2), (key2554, 2), (key2563, 2), (key2381, 2), (key2392, 2), (key2392, 2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, 1), (key2406, 1), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1)]

def rawRow3663 : Integer.Sparse Key := [(key2543, -2), (key2538, -2), (key2543, -2), (key2554, 2), (key2563, 2), (key2554, 2), (key2392, 2), (key2381, 2), (key2392, 2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, 1), (key2480, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2472, 1)]

def rawRow3664 : Integer.Sparse Key := [(key2543, -2), (key2543, -2), (key2538, -2), (key2563, 2), (key2554, 2), (key2554, 2), (key2392, 2), (key2392, 2), (key2381, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, 1), (key2472, 1), (key2480, 1), (key2406, 1), (key2472, 1), (key2406, 1)]

def rawRow3665 : Integer.Sparse Key := [(key2538, -2), (key2554, -2), (key2554, -2), (key2543, 2), (key2543, 2), (key2563, 2), (key2409, 2), (key2440, 2), (key2440, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, 1), (key2378, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1)]

def rawRow3666 : Integer.Sparse Key := [(key2554, -2), (key2538, -2), (key2554, -2), (key2543, 2), (key2563, 2), (key2543, 2), (key2440, 2), (key2409, 2), (key2440, 2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, 1), (key2503, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2472, 1)]

def rawRow3667 : Integer.Sparse Key := [(key2554, -2), (key2554, -2), (key2538, -2), (key2563, 2), (key2543, 2), (key2543, 2), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, 1), (key2472, 1), (key2503, 1), (key2378, 1), (key2472, 1), (key2378, 1)]

def rawRow3668 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2791, 2), (key2791, 2), (key2942, 2), (key2802, 1), (key2806, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2949, 1), (key2857, -1), (key2896, -1), (key2857, -1), (key2975, -1), (key2896, -1), (key2975, -1), (key2826, -2), (key2826, -2), (key2959, -2), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1)]

def rawRow3669 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2937, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2791, 2), (key2942, 2), (key2791, 2), (key2806, 1), (key2802, 1), (key2949, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2896, -1), (key2857, -1), (key2975, -1), (key2857, -1), (key2975, -1), (key2896, -1), (key2826, -2), (key2959, -2), (key2826, -2), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1)]

def rawRow3670 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2783, -1), (key2783, -1), (key2779, -1), (key2779, -1), (key2942, 2), (key2791, 2), (key2791, 2), (key2949, 1), (key2949, 1), (key2806, 1), (key2806, 1), (key2802, 1), (key2802, 1), (key2975, -1), (key2975, -1), (key2896, -1), (key2896, -1), (key2857, -1), (key2857, -1), (key2959, -2), (key2826, -2), (key2826, -2), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1)]

def rawRow3671 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2746, -2), (key2903, -2), (key2903, -2), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1)]

def rawRow3672 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2903, -2), (key2746, -2), (key2903, -2), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1)]

def rawRow3673 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1), (key2903, -2), (key2903, -2), (key2746, -2), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1)]

def rawRow3674 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2949, -1), (key2826, 2), (key2826, 2), (key2959, 2), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2867, -1), (key2903, -1), (key2867, -1), (key2982, -1), (key2903, -1), (key2982, -1), (key2791, -2), (key2791, -2), (key2942, -2), (key2857, 1), (key2896, 1), (key2857, 1), (key2975, 1), (key2896, 1), (key2975, 1)]

def rawRow3675 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2949, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2826, 2), (key2959, 2), (key2826, 2), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2903, -1), (key2867, -1), (key2982, -1), (key2867, -1), (key2982, -1), (key2903, -1), (key2791, -2), (key2942, -2), (key2791, -2), (key2896, 1), (key2857, 1), (key2975, 1), (key2857, 1), (key2975, 1), (key2896, 1)]

def rawRow3676 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2959, 2), (key2826, 2), (key2826, 2), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2982, -1), (key2982, -1), (key2903, -1), (key2903, -1), (key2867, -1), (key2867, -1), (key2942, -2), (key2791, -2), (key2791, -2), (key2975, 1), (key2975, 1), (key2896, 1), (key2896, 1), (key2857, 1), (key2857, 1)]

def rawRow3677 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1), (key2652, -2), (key2896, -2), (key2896, -2), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1)]

def rawRow3678 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2896, -2), (key2652, -2), (key2896, -2), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1)]

def rawRow3679 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1), (key2896, -2), (key2896, -2), (key2652, -2), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1)]

def rawRow3680 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1), (key2664, -2), (key2779, -2), (key2779, -2), (key2699, 1), (key2699, 1), (key2802, 1), (key2802, 1), (key2852, 1), (key2852, 1)]

def rawRow3681 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2779, -2), (key2664, -2), (key2779, -2), (key2802, 1), (key2852, 1), (key2699, 1), (key2852, 1), (key2699, 1), (key2802, 1)]

def rawRow3682 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1), (key2779, -2), (key2779, -2), (key2664, -2), (key2852, 1), (key2802, 1), (key2852, 1), (key2699, 1), (key2802, 1), (key2699, 1)]

def rawRow3683 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2609, -2), (key2802, -2), (key2802, -2), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1)]

def rawRow3684 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2802, -2), (key2609, -2), (key2802, -2), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1)]

def rawRow3685 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1), (key2802, -2), (key2802, -2), (key2609, -2), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1)]

def rawRow3686 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2645, 2), (key2645, 2), (key2651, 2), (key2663, 2), (key2666, 2), (key2666, 2), (key2734, -2), (key2734, -2), (key2745, -2), (key2935, -2), (key2935, -2), (key2941, -2), (key2947, 2), (key2947, 2), (key2958, 2)]

def rawRow3687 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2645, 2), (key2651, 2), (key2645, 2), (key2666, 2), (key2663, 2), (key2666, 2), (key2734, -2), (key2745, -2), (key2734, -2), (key2935, -2), (key2941, -2), (key2935, -2), (key2947, 2), (key2958, 2), (key2947, 2)]

def rawRow3688 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2651, 2), (key2645, 2), (key2645, 2), (key2666, 2), (key2666, 2), (key2663, 2), (key2745, -2), (key2734, -2), (key2734, -2), (key2941, -2), (key2935, -2), (key2935, -2), (key2958, 2), (key2947, 2), (key2947, 2)]

def rawRow3689 : Integer.Sparse Key := [(key2645, -2), (key2645, -2), (key2651, -2), (key2608, 2), (key2624, 2), (key2624, 2), (key2722, 2), (key2722, 2), (key2745, 2), (key2663, -2), (key2698, -2), (key2698, -2), (key2958, -2), (key2981, -2), (key2981, -2), (key2941, 2), (key2974, 2), (key2974, 2)]

def rawRow3690 : Integer.Sparse Key := [(key2645, -2), (key2651, -2), (key2645, -2), (key2624, 2), (key2608, 2), (key2624, 2), (key2722, 2), (key2745, 2), (key2722, 2), (key2698, -2), (key2663, -2), (key2698, -2), (key2981, -2), (key2958, -2), (key2981, -2), (key2974, 2), (key2941, 2), (key2974, 2)]

def rawRow3691 : Integer.Sparse Key := [(key2651, -2), (key2645, -2), (key2645, -2), (key2624, 2), (key2624, 2), (key2608, 2), (key2745, 2), (key2722, 2), (key2722, 2), (key2698, -2), (key2698, -2), (key2663, -2), (key2981, -2), (key2981, -2), (key2958, -2), (key2974, 2), (key2974, 2), (key2941, 2)]

def rawRow3692 : Integer.Sparse Key := [(key2663, -2), (key2666, -2), (key2666, -2), (key2722, 2), (key2722, 2), (key2745, 2), (key2608, 2), (key2611, 2), (key2611, 2), (key2947, -2), (key2947, -2), (key2958, -2), (key2645, -2), (key2645, -2), (key2651, -2), (key2734, 2), (key2734, 2), (key2745, 2)]

def rawRow3693 : Integer.Sparse Key := [(key2666, -2), (key2663, -2), (key2666, -2), (key2722, 2), (key2745, 2), (key2722, 2), (key2611, 2), (key2608, 2), (key2611, 2), (key2947, -2), (key2958, -2), (key2947, -2), (key2645, -2), (key2651, -2), (key2645, -2), (key2734, 2), (key2745, 2), (key2734, 2)]

def rawRow3694 : Integer.Sparse Key := [(key2666, -2), (key2666, -2), (key2663, -2), (key2745, 2), (key2722, 2), (key2722, 2), (key2611, 2), (key2611, 2), (key2608, 2), (key2958, -2), (key2947, -2), (key2947, -2), (key2651, -2), (key2645, -2), (key2645, -2), (key2745, 2), (key2734, 2), (key2734, 2)]

def rawRow3695 : Integer.Sparse Key := [(key2734, -2), (key2734, -2), (key2745, -2), (key2663, 2), (key2698, 2), (key2698, 2), (key2947, 2), (key2947, 2), (key2958, 2), (key2608, -2), (key2801, -2), (key2801, -2), (key2745, -2), (key2902, -2), (key2902, -2), (key2651, 2), (key2895, 2), (key2895, 2)]

def rawRow3696 : Integer.Sparse Key := [(key2734, -2), (key2745, -2), (key2734, -2), (key2698, 2), (key2663, 2), (key2698, 2), (key2947, 2), (key2958, 2), (key2947, 2), (key2801, -2), (key2608, -2), (key2801, -2), (key2902, -2), (key2745, -2), (key2902, -2), (key2895, 2), (key2651, 2), (key2895, 2)]

def rawRow3697 : Integer.Sparse Key := [(key2745, -2), (key2734, -2), (key2734, -2), (key2698, 2), (key2698, 2), (key2663, 2), (key2958, 2), (key2947, 2), (key2947, 2), (key2801, -2), (key2801, -2), (key2608, -2), (key2902, -2), (key2902, -2), (key2745, -2), (key2895, 2), (key2895, 2), (key2651, 2)]

def rawRow3698 : Integer.Sparse Key := [(key2935, -2), (key2935, -2), (key2941, -2), (key2958, 2), (key2981, 2), (key2981, 2), (key2645, 2), (key2645, 2), (key2651, 2), (key2745, -2), (key2902, -2), (key2902, -2), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, 2), (key2698, 2), (key2698, 2)]

def rawRow3699 : Integer.Sparse Key := [(key2935, -2), (key2941, -2), (key2935, -2), (key2981, 2), (key2958, 2), (key2981, 2), (key2645, 2), (key2651, 2), (key2645, 2), (key2902, -2), (key2745, -2), (key2902, -2), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, 2), (key2663, 2), (key2698, 2)]

def rawRow3700 : Integer.Sparse Key := [(key2941, -2), (key2935, -2), (key2935, -2), (key2981, 2), (key2981, 2), (key2958, 2), (key2651, 2), (key2645, 2), (key2645, 2), (key2902, -2), (key2902, -2), (key2745, -2), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, 2), (key2698, 2), (key2663, 2)]

def rawRow3701 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2941, 2), (key2974, 2), (key2974, 2), (key2734, 2), (key2734, 2), (key2745, 2), (key2651, -2), (key2895, -2), (key2895, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, 2), (key2801, 2), (key2801, 2)]

def rawRow3702 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2974, 2), (key2941, 2), (key2974, 2), (key2734, 2), (key2745, 2), (key2734, 2), (key2895, -2), (key2651, -2), (key2895, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, 2), (key2608, 2), (key2801, 2)]

def rawRow3703 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2974, 2), (key2974, 2), (key2941, 2), (key2745, 2), (key2734, 2), (key2734, 2), (key2895, -2), (key2895, -2), (key2651, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, 2), (key2801, 2), (key2608, 2)]

def rawRow3704 : Integer.Sparse Key := [(key1296, -2), (key1788, -2), (key1798, -2), (key1296, 1), (key1302, 1), (key1573, 1), (key1596, 1), (key1790, 1), (key1798, 1), (key1316, 2), (key1813, 2), (key1825, 2), (key1316, -1), (key1329, -1), (key1424, -1), (key1447, -1), (key1817, -1), (key1825, -1), (key1337, -1), (key1339, -1), (key1655, -1), (key1667, -1), (key1839, -1), (key1844, -1), (key1337, 1), (key1345, 1), (key1455, 1), (key1466, 1), (key1841, 1), (key1844, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3734 : Integer.Sparse Key := [(key384, -6), (key301, 2), (key384, 2), (key393, 2), (key405, 6), (key235, -2), (key405, -2), (key416, -2), (key315, -2), (key434, -2), (key438, -2), (key247, 2), (key434, 2), (key448, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow288 : Integer.Sparse Key := [(key422, -1), (key586, -1), (key423, 2), (key454, 1), (key604, 1), (key333, -1), (key462, -1), (key478, -2), (key343, 1), (key484, 1), (key401, 1), (key575, 1), (key402, -2), (key446, -1), (key598, -1), (key265, 1), (key462, 1), (key472, 2), (key274, -1), (key484, -1), (key391, -1), (key570, -1), (key310, 1), (key402, 1), (key412, 1), (key580, 1), (key244, -1), (key423, -1), (key337, -1), (key472, -1), (key269, 1), (key478, 1), (key391, 2), (key308, -1), (key401, -1), (key412, -2), (key242, 1), (key422, 1), (key322, 1), (key446, 1), (key254, -1), (key454, -1)]

def rawRow289 : Integer.Sparse Key := [(key586, -1), (key422, -1), (key423, 2), (key604, 1), (key454, 1), (key462, -1), (key333, -1), (key478, -2), (key484, 1), (key343, 1), (key575, 1), (key401, 1), (key402, -2), (key598, -1), (key446, -1), (key462, 1), (key265, 1), (key472, 2), (key484, -1), (key274, -1), (key570, -1), (key391, -1), (key402, 1), (key310, 1), (key580, 1), (key412, 1), (key423, -1), (key244, -1), (key472, -1), (key337, -1), (key478, 1), (key269, 1), (key391, 2), (key401, -1), (key308, -1), (key412, -2), (key422, 1), (key242, 1), (key446, 1), (key322, 1), (key454, -1), (key254, -1)]

def rawRow290 : Integer.Sparse Key := [(key454, -1), (key478, -1), (key604, 2), (key332, 1), (key343, 1), (key586, -1), (key610, -1), (key333, -2), (key423, 1), (key462, 1), (key446, 1), (key472, 1), (key598, -2), (key264, -1), (key274, -1), (key575, 1), (key610, 1), (key265, 2), (key402, -1), (key462, -1), (key322, -1), (key337, -1), (key580, 1), (key598, 1), (key254, 1), (key269, 1), (key570, -1), (key604, -1), (key244, -1), (key265, -1), (key310, 1), (key333, 1), (key322, 2), (key412, -1), (key446, -1), (key254, -2), (key391, 1), (key454, 1), (key242, 1), (key264, 1), (key308, -1), (key332, -1)]

def rawRow291 : Integer.Sparse Key := [(key478, -1), (key454, -1), (key604, 2), (key343, 1), (key332, 1), (key610, -1), (key586, -1), (key333, -2), (key462, 1), (key423, 1), (key472, 1), (key446, 1), (key598, -2), (key274, -1), (key264, -1), (key610, 1), (key575, 1), (key265, 2), (key462, -1), (key402, -1), (key337, -1), (key322, -1), (key598, 1), (key580, 1), (key269, 1), (key254, 1), (key604, -1), (key570, -1), (key265, -1), (key244, -1), (key333, 1), (key310, 1), (key322, 2), (key446, -1), (key412, -1), (key254, -2), (key454, 1), (key391, 1), (key264, 1), (key242, 1), (key332, -1), (key308, -1)]

def rawRow292 : Integer.Sparse Key := [(key454, -1), (key604, -1), (key478, 2), (key422, 1), (key586, 1), (key343, -1), (key484, -1), (key423, -2), (key333, 1), (key462, 1), (key446, 1), (key598, 1), (key472, -2), (key401, -1), (key575, -1), (key274, 1), (key484, 1), (key402, 2), (key265, -1), (key462, -1), (key412, -1), (key580, -1), (key337, 1), (key472, 1), (key391, 1), (key570, 1), (key269, -1), (key478, -1), (key310, -1), (key402, -1), (key244, 1), (key423, 1), (key412, 2), (key322, -1), (key446, -1), (key391, -2), (key254, 1), (key454, 1), (key308, 1), (key401, 1), (key242, -1), (key422, -1)]

def rawRow293 : Integer.Sparse Key := [(key604, -1), (key454, -1), (key478, 2), (key586, 1), (key422, 1), (key484, -1), (key343, -1), (key423, -2), (key462, 1), (key333, 1), (key598, 1), (key446, 1), (key472, -2), (key575, -1), (key401, -1), (key484, 1), (key274, 1), (key402, 2), (key462, -1), (key265, -1), (key580, -1), (key412, -1), (key472, 1), (key337, 1), (key570, 1), (key391, 1), (key478, -1), (key269, -1), (key402, -1), (key310, -1), (key423, 1), (key244, 1), (key412, 2), (key446, -1), (key322, -1), (key391, -2), (key454, 1), (key254, 1), (key401, 1), (key308, 1), (key422, -1), (key242, -1)]

def rawRow294 : Integer.Sparse Key := [(key1301, -2), (key1305, 1), (key1305, 1), (key1321, 2), (key1332, -1), (key1332, -1), (key1342, -1), (key1342, -1), (key1348, 1), (key1348, 1), (key1396, 2), (key1400, -1), (key1400, -1), (key1429, -2), (key1450, 1), (key1450, 1), (key1460, 1), (key1460, 1), (key1469, -1), (key1469, -1), (key1551, -2), (key1562, 1), (key1562, 1), (key1578, 2), (key1599, -1), (key1599, -1), (key1662, -1), (key1662, -1), (key1670, 1), (key1670, 1), (key1777, 1), (key1777, 1), (key1783, -1), (key1783, -1), (key1793, -1), (key1793, -1), (key1801, 1), (key1801, 1), (key1820, 1), (key1820, 1), (key1828, -1), (key1828, -1)]

def rawRow295 : Integer.Sparse Key := [(key1305, -2), (key1301, 1), (key1305, 1), (key1332, 2), (key1321, -1), (key1332, -1), (key1348, -1), (key1349, -1), (key1342, 1), (key1349, 1), (key1400, 2), (key1396, -1), (key1400, -1), (key1450, -2), (key1429, 1), (key1450, 1), (key1469, 1), (key1470, 1), (key1460, -1), (key1470, -1), (key1562, -2), (key1551, 1), (key1562, 1), (key1599, 2), (key1578, -1), (key1599, -1), (key1670, -1), (key1676, -1), (key1662, 1), (key1676, 1), (key1783, 1), (key1784, 1), (key1777, -1), (key1784, -1), (key1801, -1), (key1802, -1), (key1793, 1), (key1802, 1), (key1828, 1), (key1834, 1), (key1820, -1), (key1834, -1)]

def rawRow296 : Integer.Sparse Key := [(key1305, -2), (key1305, 1), (key1301, 1), (key1332, 2), (key1332, -1), (key1321, -1), (key1349, -1), (key1348, -1), (key1349, 1), (key1342, 1), (key1400, 2), (key1400, -1), (key1396, -1), (key1450, -2), (key1450, 1), (key1429, 1), (key1470, 1), (key1469, 1), (key1470, -1), (key1460, -1), (key1562, -2), (key1562, 1), (key1551, 1), (key1599, 2), (key1599, -1), (key1578, -1), (key1676, -1), (key1670, -1), (key1676, 1), (key1662, 1), (key1784, 1), (key1783, 1), (key1784, -1), (key1777, -1), (key1802, -1), (key1801, -1), (key1802, 1), (key1793, 1), (key1834, 1), (key1828, 1), (key1834, -1), (key1820, -1)]

def rawRow297 : Integer.Sparse Key := [(key1321, -2), (key1342, 1), (key1342, 1), (key1301, 2), (key1348, -1), (key1348, -1), (key1305, -1), (key1305, -1), (key1332, 1), (key1332, 1), (key1429, 2), (key1460, -1), (key1460, -1), (key1396, -2), (key1469, 1), (key1469, 1), (key1400, 1), (key1400, 1), (key1450, -1), (key1450, -1), (key1578, -2), (key1662, 1), (key1662, 1), (key1551, 2), (key1670, -1), (key1670, -1), (key1562, -1), (key1562, -1), (key1599, 1), (key1599, 1), (key1793, 1), (key1793, 1), (key1820, -1), (key1820, -1), (key1777, -1), (key1777, -1), (key1828, 1), (key1828, 1), (key1783, 1), (key1783, 1), (key1801, -1), (key1801, -1)]

def rawRow298 : Integer.Sparse Key := [(key1342, -2), (key1321, 1), (key1342, 1), (key1348, 2), (key1301, -1), (key1348, -1), (key1332, -1), (key1349, -1), (key1305, 1), (key1349, 1), (key1460, 2), (key1429, -1), (key1460, -1), (key1469, -2), (key1396, 1), (key1469, 1), (key1450, 1), (key1470, 1), (key1400, -1), (key1470, -1), (key1662, -2), (key1578, 1), (key1662, 1), (key1670, 2), (key1551, -1), (key1670, -1), (key1599, -1), (key1676, -1), (key1562, 1), (key1676, 1), (key1820, 1), (key1843, 1), (key1793, -1), (key1843, -1), (key1828, -1), (key1846, -1), (key1777, 1), (key1846, 1), (key1801, 1), (key1849, 1), (key1783, -1), (key1849, -1)]

def rawRow299 : Integer.Sparse Key := [(key1342, -2), (key1342, 1), (key1321, 1), (key1348, 2), (key1348, -1), (key1301, -1), (key1349, -1), (key1332, -1), (key1349, 1), (key1305, 1), (key1460, 2), (key1460, -1), (key1429, -1), (key1469, -2), (key1469, 1), (key1396, 1), (key1470, 1), (key1450, 1), (key1470, -1), (key1400, -1), (key1662, -2), (key1662, 1), (key1578, 1), (key1670, 2), (key1670, -1), (key1551, -1), (key1676, -1), (key1599, -1), (key1676, 1), (key1562, 1), (key1843, 1), (key1820, 1), (key1843, -1), (key1793, -1), (key1846, -1), (key1828, -1), (key1846, 1), (key1777, 1), (key1849, 1), (key1801, 1), (key1849, -1), (key1783, -1)]

def rawRow300 : Integer.Sparse Key := [(key1332, -2), (key1348, 1), (key1349, 1), (key1305, 2), (key1342, -1), (key1349, -1), (key1301, -1), (key1305, -1), (key1321, 1), (key1332, 1), (key1450, 2), (key1469, -1), (key1470, -1), (key1400, -2), (key1460, 1), (key1470, 1), (key1396, 1), (key1400, 1), (key1429, -1), (key1450, -1), (key1599, -2), (key1670, 1), (key1676, 1), (key1562, 2), (key1662, -1), (key1676, -1), (key1551, -1), (key1562, -1), (key1578, 1), (key1599, 1), (key1801, 1), (key1802, 1), (key1828, -1), (key1834, -1), (key1783, -1), (key1784, -1), (key1820, 1), (key1834, 1), (key1777, 1), (key1784, 1), (key1793, -1), (key1802, -1)]

def rawRow301 : Integer.Sparse Key := [(key1332, -2), (key1349, 1), (key1348, 1), (key1305, 2), (key1349, -1), (key1342, -1), (key1305, -1), (key1301, -1), (key1332, 1), (key1321, 1), (key1450, 2), (key1470, -1), (key1469, -1), (key1400, -2), (key1470, 1), (key1460, 1), (key1400, 1), (key1396, 1), (key1450, -1), (key1429, -1), (key1599, -2), (key1676, 1), (key1670, 1), (key1562, 2), (key1676, -1), (key1662, -1), (key1562, -1), (key1551, -1), (key1599, 1), (key1578, 1), (key1802, 1), (key1801, 1), (key1834, -1), (key1828, -1), (key1784, -1), (key1783, -1), (key1834, 1), (key1820, 1), (key1784, 1), (key1777, 1), (key1802, -1), (key1793, -1)]

def rawRow302 : Integer.Sparse Key := [(key1348, -2), (key1332, 1), (key1349, 1), (key1342, 2), (key1305, -1), (key1349, -1), (key1321, -1), (key1342, -1), (key1301, 1), (key1348, 1), (key1469, 2), (key1450, -1), (key1470, -1), (key1460, -2), (key1400, 1), (key1470, 1), (key1429, 1), (key1460, 1), (key1396, -1), (key1469, -1), (key1670, -2), (key1599, 1), (key1676, 1), (key1662, 2), (key1562, -1), (key1676, -1), (key1578, -1), (key1662, -1), (key1551, 1), (key1670, 1), (key1828, 1), (key1846, 1), (key1801, -1), (key1849, -1), (key1820, -1), (key1843, -1), (key1783, 1), (key1849, 1), (key1793, 1), (key1843, 1), (key1777, -1), (key1846, -1)]

def rawRow303 : Integer.Sparse Key := [(key1348, -2), (key1349, 1), (key1332, 1), (key1342, 2), (key1349, -1), (key1305, -1), (key1342, -1), (key1321, -1), (key1348, 1), (key1301, 1), (key1469, 2), (key1470, -1), (key1450, -1), (key1460, -2), (key1470, 1), (key1400, 1), (key1460, 1), (key1429, 1), (key1469, -1), (key1396, -1), (key1670, -2), (key1676, 1), (key1599, 1), (key1662, 2), (key1676, -1), (key1562, -1), (key1662, -1), (key1578, -1), (key1670, 1), (key1551, 1), (key1846, 1), (key1828, 1), (key1849, -1), (key1801, -1), (key1843, -1), (key1820, -1), (key1849, 1), (key1783, 1), (key1843, 1), (key1793, 1), (key1846, -1), (key1777, -1)]

def rawRow304 : Integer.Sparse Key := [(key1396, -2), (key1400, 1), (key1400, 1), (key1551, 2), (key1562, -1), (key1562, -1), (key1777, -1), (key1777, -1), (key1783, 1), (key1783, 1), (key1301, 2), (key1305, -1), (key1305, -1), (key1578, -2), (key1599, 1), (key1599, 1), (key1793, 1), (key1793, 1), (key1801, -1), (key1801, -1), (key1321, -2), (key1332, 1), (key1332, 1), (key1429, 2), (key1450, -1), (key1450, -1), (key1820, -1), (key1820, -1), (key1828, 1), (key1828, 1), (key1342, 1), (key1342, 1), (key1348, -1), (key1348, -1), (key1460, -1), (key1460, -1), (key1469, 1), (key1469, 1), (key1662, 1), (key1662, 1), (key1670, -1), (key1670, -1)]

def rawRow305 : Integer.Sparse Key := [(key1400, -2), (key1396, 1), (key1400, 1), (key1562, 2), (key1551, -1), (key1562, -1), (key1783, -1), (key1784, -1), (key1777, 1), (key1784, 1), (key1305, 2), (key1301, -1), (key1305, -1), (key1599, -2), (key1578, 1), (key1599, 1), (key1801, 1), (key1802, 1), (key1793, -1), (key1802, -1), (key1332, -2), (key1321, 1), (key1332, 1), (key1450, 2), (key1429, -1), (key1450, -1), (key1828, -1), (key1834, -1), (key1820, 1), (key1834, 1), (key1348, 1), (key1349, 1), (key1342, -1), (key1349, -1), (key1469, -1), (key1470, -1), (key1460, 1), (key1470, 1), (key1670, 1), (key1676, 1), (key1662, -1), (key1676, -1)]

def rawRow306 : Integer.Sparse Key := [(key1400, -2), (key1400, 1), (key1396, 1), (key1562, 2), (key1562, -1), (key1551, -1), (key1784, -1), (key1783, -1), (key1784, 1), (key1777, 1), (key1305, 2), (key1305, -1), (key1301, -1), (key1599, -2), (key1599, 1), (key1578, 1), (key1802, 1), (key1801, 1), (key1802, -1), (key1793, -1), (key1332, -2), (key1332, 1), (key1321, 1), (key1450, 2), (key1450, -1), (key1429, -1), (key1834, -1), (key1828, -1), (key1834, 1), (key1820, 1), (key1349, 1), (key1348, 1), (key1349, -1), (key1342, -1), (key1470, -1), (key1469, -1), (key1470, 1), (key1460, 1), (key1676, 1), (key1670, 1), (key1676, -1), (key1662, -1)]

def rawRow307 : Integer.Sparse Key := [(key1551, -2), (key1777, 1), (key1777, 1), (key1396, 2), (key1783, -1), (key1783, -1), (key1400, -1), (key1400, -1), (key1562, 1), (key1562, 1), (key1578, 2), (key1793, -1), (key1793, -1), (key1301, -2), (key1801, 1), (key1801, 1), (key1305, 1), (key1305, 1), (key1599, -1), (key1599, -1), (key1429, -2), (key1820, 1), (key1820, 1), (key1321, 2), (key1828, -1), (key1828, -1), (key1332, -1), (key1332, -1), (key1450, 1), (key1450, 1), (key1460, 1), (key1460, 1), (key1662, -1), (key1662, -1), (key1342, -1), (key1342, -1), (key1670, 1), (key1670, 1), (key1348, 1), (key1348, 1), (key1469, -1), (key1469, -1)]

def rawRow308 : Integer.Sparse Key := [(key1777, -2), (key1551, 1), (key1777, 1), (key1783, 2), (key1396, -1), (key1783, -1), (key1562, -1), (key1784, -1), (key1400, 1), (key1784, 1), (key1793, 2), (key1578, -1), (key1793, -1), (key1801, -2), (key1301, 1), (key1801, 1), (key1599, 1), (key1802, 1), (key1305, -1), (key1802, -1), (key1820, -2), (key1429, 1), (key1820, 1), (key1828, 2), (key1321, -1), (key1828, -1), (key1450, -1), (key1834, -1), (key1332, 1), (key1834, 1), (key1662, 1), (key1843, 1), (key1460, -1), (key1843, -1), (key1670, -1), (key1846, -1), (key1342, 1), (key1846, 1), (key1469, 1), (key1849, 1), (key1348, -1), (key1849, -1)]

def rawRow309 : Integer.Sparse Key := [(key1777, -2), (key1777, 1), (key1551, 1), (key1783, 2), (key1783, -1), (key1396, -1), (key1784, -1), (key1562, -1), (key1784, 1), (key1400, 1), (key1793, 2), (key1793, -1), (key1578, -1), (key1801, -2), (key1801, 1), (key1301, 1), (key1802, 1), (key1599, 1), (key1802, -1), (key1305, -1), (key1820, -2), (key1820, 1), (key1429, 1), (key1828, 2), (key1828, -1), (key1321, -1), (key1834, -1), (key1450, -1), (key1834, 1), (key1332, 1), (key1843, 1), (key1662, 1), (key1843, -1), (key1460, -1), (key1846, -1), (key1670, -1), (key1846, 1), (key1342, 1), (key1849, 1), (key1469, 1), (key1849, -1), (key1348, -1)]

def rawRow310 : Integer.Sparse Key := [(key1562, -2), (key1783, 1), (key1784, 1), (key1400, 2), (key1777, -1), (key1784, -1), (key1396, -1), (key1400, -1), (key1551, 1), (key1562, 1), (key1599, 2), (key1801, -1), (key1802, -1), (key1305, -2), (key1793, 1), (key1802, 1), (key1301, 1), (key1305, 1), (key1578, -1), (key1599, -1), (key1450, -2), (key1828, 1), (key1834, 1), (key1332, 2), (key1820, -1), (key1834, -1), (key1321, -1), (key1332, -1), (key1429, 1), (key1450, 1), (key1469, 1), (key1470, 1), (key1670, -1), (key1676, -1), (key1348, -1), (key1349, -1), (key1662, 1), (key1676, 1), (key1342, 1), (key1349, 1), (key1460, -1), (key1470, -1)]

def rawRow311 : Integer.Sparse Key := [(key1562, -2), (key1784, 1), (key1783, 1), (key1400, 2), (key1784, -1), (key1777, -1), (key1400, -1), (key1396, -1), (key1562, 1), (key1551, 1), (key1599, 2), (key1802, -1), (key1801, -1), (key1305, -2), (key1802, 1), (key1793, 1), (key1305, 1), (key1301, 1), (key1599, -1), (key1578, -1), (key1450, -2), (key1834, 1), (key1828, 1), (key1332, 2), (key1834, -1), (key1820, -1), (key1332, -1), (key1321, -1), (key1450, 1), (key1429, 1), (key1470, 1), (key1469, 1), (key1676, -1), (key1670, -1), (key1349, -1), (key1348, -1), (key1676, 1), (key1662, 1), (key1349, 1), (key1342, 1), (key1470, -1), (key1460, -1)]

def rawRow312 : Integer.Sparse Key := [(key1783, -2), (key1562, 1), (key1784, 1), (key1777, 2), (key1400, -1), (key1784, -1), (key1551, -1), (key1777, -1), (key1396, 1), (key1783, 1), (key1801, 2), (key1599, -1), (key1802, -1), (key1793, -2), (key1305, 1), (key1802, 1), (key1578, 1), (key1793, 1), (key1301, -1), (key1801, -1), (key1828, -2), (key1450, 1), (key1834, 1), (key1820, 2), (key1332, -1), (key1834, -1), (key1429, -1), (key1820, -1), (key1321, 1), (key1828, 1), (key1670, 1), (key1846, 1), (key1469, -1), (key1849, -1), (key1662, -1), (key1843, -1), (key1348, 1), (key1849, 1), (key1460, 1), (key1843, 1), (key1342, -1), (key1846, -1)]

def rawRow313 : Integer.Sparse Key := [(key1783, -2), (key1784, 1), (key1562, 1), (key1777, 2), (key1784, -1), (key1400, -1), (key1777, -1), (key1551, -1), (key1783, 1), (key1396, 1), (key1801, 2), (key1802, -1), (key1599, -1), (key1793, -2), (key1802, 1), (key1305, 1), (key1793, 1), (key1578, 1), (key1801, -1), (key1301, -1), (key1828, -2), (key1834, 1), (key1450, 1), (key1820, 2), (key1834, -1), (key1332, -1), (key1820, -1), (key1429, -1), (key1828, 1), (key1321, 1), (key1846, 1), (key1670, 1), (key1849, -1), (key1469, -1), (key1843, -1), (key1662, -1), (key1849, 1), (key1348, 1), (key1843, 1), (key1460, 1), (key1846, -1), (key1342, -1)]

def rawRow314 : Integer.Sparse Key := [(key1429, -2), (key1460, 1), (key1460, 1), (key1578, 2), (key1662, -1), (key1662, -1), (key1793, -1), (key1793, -1), (key1820, 1), (key1820, 1), (key1321, 2), (key1342, -1), (key1342, -1), (key1551, -2), (key1670, 1), (key1670, 1), (key1777, 1), (key1777, 1), (key1828, -1), (key1828, -1), (key1301, -2), (key1348, 1), (key1348, 1), (key1396, 2), (key1469, -1), (key1469, -1), (key1783, -1), (key1783, -1), (key1801, 1), (key1801, 1), (key1305, 1), (key1305, 1), (key1332, -1), (key1332, -1), (key1400, -1), (key1400, -1), (key1450, 1), (key1450, 1), (key1562, 1), (key1562, 1), (key1599, -1), (key1599, -1)]

def rawRow315 : Integer.Sparse Key := [(key1460, -2), (key1429, 1), (key1460, 1), (key1662, 2), (key1578, -1), (key1662, -1), (key1820, -1), (key1843, -1), (key1793, 1), (key1843, 1), (key1342, 2), (key1321, -1), (key1342, -1), (key1670, -2), (key1551, 1), (key1670, 1), (key1828, 1), (key1846, 1), (key1777, -1), (key1846, -1), (key1348, -2), (key1301, 1), (key1348, 1), (key1469, 2), (key1396, -1), (key1469, -1), (key1801, -1), (key1849, -1), (key1783, 1), (key1849, 1), (key1332, 1), (key1349, 1), (key1305, -1), (key1349, -1), (key1450, -1), (key1470, -1), (key1400, 1), (key1470, 1), (key1599, 1), (key1676, 1), (key1562, -1), (key1676, -1)]

def rawRow316 : Integer.Sparse Key := [(key1460, -2), (key1460, 1), (key1429, 1), (key1662, 2), (key1662, -1), (key1578, -1), (key1843, -1), (key1820, -1), (key1843, 1), (key1793, 1), (key1342, 2), (key1342, -1), (key1321, -1), (key1670, -2), (key1670, 1), (key1551, 1), (key1846, 1), (key1828, 1), (key1846, -1), (key1777, -1), (key1348, -2), (key1348, 1), (key1301, 1), (key1469, 2), (key1469, -1), (key1396, -1), (key1849, -1), (key1801, -1), (key1849, 1), (key1783, 1), (key1349, 1), (key1332, 1), (key1349, -1), (key1305, -1), (key1470, -1), (key1450, -1), (key1470, 1), (key1400, 1), (key1676, 1), (key1599, 1), (key1676, -1), (key1562, -1)]

def rawRow317 : Integer.Sparse Key := [(key1578, -2), (key1793, 1), (key1793, 1), (key1429, 2), (key1820, -1), (key1820, -1), (key1460, -1), (key1460, -1), (key1662, 1), (key1662, 1), (key1551, 2), (key1777, -1), (key1777, -1), (key1321, -2), (key1828, 1), (key1828, 1), (key1342, 1), (key1342, 1), (key1670, -1), (key1670, -1), (key1396, -2), (key1783, 1), (key1783, 1), (key1301, 2), (key1801, -1), (key1801, -1), (key1348, -1), (key1348, -1), (key1469, 1), (key1469, 1), (key1400, 1), (key1400, 1), (key1562, -1), (key1562, -1), (key1305, -1), (key1305, -1), (key1599, 1), (key1599, 1), (key1332, 1), (key1332, 1), (key1450, -1), (key1450, -1)]

def rawRow318 : Integer.Sparse Key := [(key1793, -2), (key1578, 1), (key1793, 1), (key1820, 2), (key1429, -1), (key1820, -1), (key1662, -1), (key1843, -1), (key1460, 1), (key1843, 1), (key1777, 2), (key1551, -1), (key1777, -1), (key1828, -2), (key1321, 1), (key1828, 1), (key1670, 1), (key1846, 1), (key1342, -1), (key1846, -1), (key1783, -2), (key1396, 1), (key1783, 1), (key1801, 2), (key1301, -1), (key1801, -1), (key1469, -1), (key1849, -1), (key1348, 1), (key1849, 1), (key1562, 1), (key1784, 1), (key1400, -1), (key1784, -1), (key1599, -1), (key1802, -1), (key1305, 1), (key1802, 1), (key1450, 1), (key1834, 1), (key1332, -1), (key1834, -1)]

def rawRow319 : Integer.Sparse Key := [(key1793, -2), (key1793, 1), (key1578, 1), (key1820, 2), (key1820, -1), (key1429, -1), (key1843, -1), (key1662, -1), (key1843, 1), (key1460, 1), (key1777, 2), (key1777, -1), (key1551, -1), (key1828, -2), (key1828, 1), (key1321, 1), (key1846, 1), (key1670, 1), (key1846, -1), (key1342, -1), (key1783, -2), (key1783, 1), (key1396, 1), (key1801, 2), (key1801, -1), (key1301, -1), (key1849, -1), (key1469, -1), (key1849, 1), (key1348, 1), (key1784, 1), (key1562, 1), (key1784, -1), (key1400, -1), (key1802, -1), (key1599, -1), (key1802, 1), (key1305, 1), (key1834, 1), (key1450, 1), (key1834, -1), (key1332, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow320 : Integer.Sparse Key := [(key1662, -2), (key1820, 1), (key1843, 1), (key1460, 2), (key1793, -1), (key1843, -1), (key1429, -1), (key1460, -1), (key1578, 1), (key1662, 1), (key1670, 2), (key1828, -1), (key1846, -1), (key1342, -2), (key1777, 1), (key1846, 1), (key1321, 1), (key1342, 1), (key1551, -1), (key1670, -1), (key1469, -2), (key1801, 1), (key1849, 1), (key1348, 2), (key1783, -1), (key1849, -1), (key1301, -1), (key1348, -1), (key1396, 1), (key1469, 1), (key1450, 1), (key1470, 1), (key1599, -1), (key1676, -1), (key1332, -1), (key1349, -1), (key1562, 1), (key1676, 1), (key1305, 1), (key1349, 1), (key1400, -1), (key1470, -1)]

def rawRow321 : Integer.Sparse Key := [(key1662, -2), (key1843, 1), (key1820, 1), (key1460, 2), (key1843, -1), (key1793, -1), (key1460, -1), (key1429, -1), (key1662, 1), (key1578, 1), (key1670, 2), (key1846, -1), (key1828, -1), (key1342, -2), (key1846, 1), (key1777, 1), (key1342, 1), (key1321, 1), (key1670, -1), (key1551, -1), (key1469, -2), (key1849, 1), (key1801, 1), (key1348, 2), (key1849, -1), (key1783, -1), (key1348, -1), (key1301, -1), (key1469, 1), (key1396, 1), (key1470, 1), (key1450, 1), (key1676, -1), (key1599, -1), (key1349, -1), (key1332, -1), (key1676, 1), (key1562, 1), (key1349, 1), (key1305, 1), (key1470, -1), (key1400, -1)]

def rawRow322 : Integer.Sparse Key := [(key1820, -2), (key1662, 1), (key1843, 1), (key1793, 2), (key1460, -1), (key1843, -1), (key1578, -1), (key1793, -1), (key1429, 1), (key1820, 1), (key1828, 2), (key1670, -1), (key1846, -1), (key1777, -2), (key1342, 1), (key1846, 1), (key1551, 1), (key1777, 1), (key1321, -1), (key1828, -1), (key1801, -2), (key1469, 1), (key1849, 1), (key1783, 2), (key1348, -1), (key1849, -1), (key1396, -1), (key1783, -1), (key1301, 1), (key1801, 1), (key1599, 1), (key1802, 1), (key1450, -1), (key1834, -1), (key1562, -1), (key1784, -1), (key1332, 1), (key1834, 1), (key1400, 1), (key1784, 1), (key1305, -1), (key1802, -1)]

def rawRow323 : Integer.Sparse Key := [(key1820, -2), (key1843, 1), (key1662, 1), (key1793, 2), (key1843, -1), (key1460, -1), (key1793, -1), (key1578, -1), (key1820, 1), (key1429, 1), (key1828, 2), (key1846, -1), (key1670, -1), (key1777, -2), (key1846, 1), (key1342, 1), (key1777, 1), (key1551, 1), (key1828, -1), (key1321, -1), (key1801, -2), (key1849, 1), (key1469, 1), (key1783, 2), (key1849, -1), (key1348, -1), (key1783, -1), (key1396, -1), (key1801, 1), (key1301, 1), (key1802, 1), (key1599, 1), (key1834, -1), (key1450, -1), (key1784, -1), (key1562, -1), (key1834, 1), (key1332, 1), (key1784, 1), (key1400, 1), (key1802, -1), (key1305, -1)]

def rawRow324 : Integer.Sparse Key := [(key1450, -2), (key1469, 1), (key1470, 1), (key1599, 2), (key1670, -1), (key1676, -1), (key1801, -1), (key1802, -1), (key1828, 1), (key1834, 1), (key1332, 2), (key1348, -1), (key1349, -1), (key1562, -2), (key1662, 1), (key1676, 1), (key1783, 1), (key1784, 1), (key1820, -1), (key1834, -1), (key1305, -2), (key1342, 1), (key1349, 1), (key1400, 2), (key1460, -1), (key1470, -1), (key1777, -1), (key1784, -1), (key1793, 1), (key1802, 1), (key1301, 1), (key1305, 1), (key1321, -1), (key1332, -1), (key1396, -1), (key1400, -1), (key1429, 1), (key1450, 1), (key1551, 1), (key1562, 1), (key1578, -1), (key1599, -1)]

def rawRow325 : Integer.Sparse Key := [(key1450, -2), (key1470, 1), (key1469, 1), (key1599, 2), (key1676, -1), (key1670, -1), (key1802, -1), (key1801, -1), (key1834, 1), (key1828, 1), (key1332, 2), (key1349, -1), (key1348, -1), (key1562, -2), (key1676, 1), (key1662, 1), (key1784, 1), (key1783, 1), (key1834, -1), (key1820, -1), (key1305, -2), (key1349, 1), (key1342, 1), (key1400, 2), (key1470, -1), (key1460, -1), (key1784, -1), (key1777, -1), (key1802, 1), (key1793, 1), (key1305, 1), (key1301, 1), (key1332, -1), (key1321, -1), (key1400, -1), (key1396, -1), (key1450, 1), (key1429, 1), (key1562, 1), (key1551, 1), (key1599, -1), (key1578, -1)]

def rawRow326 : Integer.Sparse Key := [(key1469, -2), (key1450, 1), (key1470, 1), (key1670, 2), (key1599, -1), (key1676, -1), (key1828, -1), (key1846, -1), (key1801, 1), (key1849, 1), (key1348, 2), (key1332, -1), (key1349, -1), (key1662, -2), (key1562, 1), (key1676, 1), (key1820, 1), (key1843, 1), (key1783, -1), (key1849, -1), (key1342, -2), (key1305, 1), (key1349, 1), (key1460, 2), (key1400, -1), (key1470, -1), (key1793, -1), (key1843, -1), (key1777, 1), (key1846, 1), (key1321, 1), (key1342, 1), (key1301, -1), (key1348, -1), (key1429, -1), (key1460, -1), (key1396, 1), (key1469, 1), (key1578, 1), (key1662, 1), (key1551, -1), (key1670, -1)]

def rawRow327 : Integer.Sparse Key := [(key1469, -2), (key1470, 1), (key1450, 1), (key1670, 2), (key1676, -1), (key1599, -1), (key1846, -1), (key1828, -1), (key1849, 1), (key1801, 1), (key1348, 2), (key1349, -1), (key1332, -1), (key1662, -2), (key1676, 1), (key1562, 1), (key1843, 1), (key1820, 1), (key1849, -1), (key1783, -1), (key1342, -2), (key1349, 1), (key1305, 1), (key1460, 2), (key1470, -1), (key1400, -1), (key1843, -1), (key1793, -1), (key1846, 1), (key1777, 1), (key1342, 1), (key1321, 1), (key1348, -1), (key1301, -1), (key1460, -1), (key1429, -1), (key1469, 1), (key1396, 1), (key1662, 1), (key1578, 1), (key1670, -1), (key1551, -1)]

def rawRow328 : Integer.Sparse Key := [(key1599, -2), (key1801, 1), (key1802, 1), (key1450, 2), (key1828, -1), (key1834, -1), (key1469, -1), (key1470, -1), (key1670, 1), (key1676, 1), (key1562, 2), (key1783, -1), (key1784, -1), (key1332, -2), (key1820, 1), (key1834, 1), (key1348, 1), (key1349, 1), (key1662, -1), (key1676, -1), (key1400, -2), (key1777, 1), (key1784, 1), (key1305, 2), (key1793, -1), (key1802, -1), (key1342, -1), (key1349, -1), (key1460, 1), (key1470, 1), (key1396, 1), (key1400, 1), (key1551, -1), (key1562, -1), (key1301, -1), (key1305, -1), (key1578, 1), (key1599, 1), (key1321, 1), (key1332, 1), (key1429, -1), (key1450, -1)]

def rawRow329 : Integer.Sparse Key := [(key1599, -2), (key1802, 1), (key1801, 1), (key1450, 2), (key1834, -1), (key1828, -1), (key1470, -1), (key1469, -1), (key1676, 1), (key1670, 1), (key1562, 2), (key1784, -1), (key1783, -1), (key1332, -2), (key1834, 1), (key1820, 1), (key1349, 1), (key1348, 1), (key1676, -1), (key1662, -1), (key1400, -2), (key1784, 1), (key1777, 1), (key1305, 2), (key1802, -1), (key1793, -1), (key1349, -1), (key1342, -1), (key1470, 1), (key1460, 1), (key1400, 1), (key1396, 1), (key1562, -1), (key1551, -1), (key1305, -1), (key1301, -1), (key1599, 1), (key1578, 1), (key1332, 1), (key1321, 1), (key1450, -1), (key1429, -1)]

def rawRow330 : Integer.Sparse Key := [(key1801, -2), (key1599, 1), (key1802, 1), (key1828, 2), (key1450, -1), (key1834, -1), (key1670, -1), (key1846, -1), (key1469, 1), (key1849, 1), (key1783, 2), (key1562, -1), (key1784, -1), (key1820, -2), (key1332, 1), (key1834, 1), (key1662, 1), (key1843, 1), (key1348, -1), (key1849, -1), (key1777, -2), (key1400, 1), (key1784, 1), (key1793, 2), (key1305, -1), (key1802, -1), (key1460, -1), (key1843, -1), (key1342, 1), (key1846, 1), (key1551, 1), (key1777, 1), (key1396, -1), (key1783, -1), (key1578, -1), (key1793, -1), (key1301, 1), (key1801, 1), (key1429, 1), (key1820, 1), (key1321, -1), (key1828, -1)]

def rawRow331 : Integer.Sparse Key := [(key1801, -2), (key1802, 1), (key1599, 1), (key1828, 2), (key1834, -1), (key1450, -1), (key1846, -1), (key1670, -1), (key1849, 1), (key1469, 1), (key1783, 2), (key1784, -1), (key1562, -1), (key1820, -2), (key1834, 1), (key1332, 1), (key1843, 1), (key1662, 1), (key1849, -1), (key1348, -1), (key1777, -2), (key1784, 1), (key1400, 1), (key1793, 2), (key1802, -1), (key1305, -1), (key1843, -1), (key1460, -1), (key1846, 1), (key1342, 1), (key1777, 1), (key1551, 1), (key1783, -1), (key1396, -1), (key1793, -1), (key1578, -1), (key1801, 1), (key1301, 1), (key1820, 1), (key1429, 1), (key1828, -1), (key1321, -1)]

def rawRow332 : Integer.Sparse Key := [(key1670, -2), (key1828, 1), (key1846, 1), (key1469, 2), (key1801, -1), (key1849, -1), (key1450, -1), (key1470, -1), (key1599, 1), (key1676, 1), (key1662, 2), (key1820, -1), (key1843, -1), (key1348, -2), (key1783, 1), (key1849, 1), (key1332, 1), (key1349, 1), (key1562, -1), (key1676, -1), (key1460, -2), (key1793, 1), (key1843, 1), (key1342, 2), (key1777, -1), (key1846, -1), (key1305, -1), (key1349, -1), (key1400, 1), (key1470, 1), (key1429, 1), (key1460, 1), (key1578, -1), (key1662, -1), (key1321, -1), (key1342, -1), (key1551, 1), (key1670, 1), (key1301, 1), (key1348, 1), (key1396, -1), (key1469, -1)]

def rawRow333 : Integer.Sparse Key := [(key1670, -2), (key1846, 1), (key1828, 1), (key1469, 2), (key1849, -1), (key1801, -1), (key1470, -1), (key1450, -1), (key1676, 1), (key1599, 1), (key1662, 2), (key1843, -1), (key1820, -1), (key1348, -2), (key1849, 1), (key1783, 1), (key1349, 1), (key1332, 1), (key1676, -1), (key1562, -1), (key1460, -2), (key1843, 1), (key1793, 1), (key1342, 2), (key1846, -1), (key1777, -1), (key1349, -1), (key1305, -1), (key1470, 1), (key1400, 1), (key1460, 1), (key1429, 1), (key1662, -1), (key1578, -1), (key1342, -1), (key1321, -1), (key1670, 1), (key1551, 1), (key1348, 1), (key1301, 1), (key1469, -1), (key1396, -1)]

def rawRow334 : Integer.Sparse Key := [(key1828, -2), (key1670, 1), (key1846, 1), (key1801, 2), (key1469, -1), (key1849, -1), (key1599, -1), (key1802, -1), (key1450, 1), (key1834, 1), (key1820, 2), (key1662, -1), (key1843, -1), (key1783, -2), (key1348, 1), (key1849, 1), (key1562, 1), (key1784, 1), (key1332, -1), (key1834, -1), (key1793, -2), (key1460, 1), (key1843, 1), (key1777, 2), (key1342, -1), (key1846, -1), (key1400, -1), (key1784, -1), (key1305, 1), (key1802, 1), (key1578, 1), (key1793, 1), (key1429, -1), (key1820, -1), (key1551, -1), (key1777, -1), (key1321, 1), (key1828, 1), (key1396, 1), (key1783, 1), (key1301, -1), (key1801, -1)]

def rawRow335 : Integer.Sparse Key := [(key1828, -2), (key1846, 1), (key1670, 1), (key1801, 2), (key1849, -1), (key1469, -1), (key1802, -1), (key1599, -1), (key1834, 1), (key1450, 1), (key1820, 2), (key1843, -1), (key1662, -1), (key1783, -2), (key1849, 1), (key1348, 1), (key1784, 1), (key1562, 1), (key1834, -1), (key1332, -1), (key1793, -2), (key1843, 1), (key1460, 1), (key1777, 2), (key1846, -1), (key1342, -1), (key1784, -1), (key1400, -1), (key1802, 1), (key1305, 1), (key1793, 1), (key1578, 1), (key1820, -1), (key1429, -1), (key1777, -1), (key1551, -1), (key1828, 1), (key1321, 1), (key1783, 1), (key1396, 1), (key1801, -1), (key1301, -1)]

def rawRow336 : Integer.Sparse Key := [(key1300, -1), (key1300, -1), (key1306, 2), (key1320, 1), (key1320, 1), (key1333, -1), (key1333, -1), (key1353, -2), (key1356, 1), (key1356, 1), (key1395, 1), (key1395, 1), (key1401, -2), (key1428, -1), (key1428, -1), (key1451, 1), (key1451, 1), (key1474, 2), (key1482, -1), (key1482, -1), (key1550, -1), (key1550, -1), (key1563, 1), (key1563, 1), (key1577, 1), (key1577, 1), (key1600, -1), (key1600, -1), (key1685, -1), (key1685, -1), (key1691, 1), (key1691, 1), (key1898, 2), (key1901, -1), (key1901, -1), (key1905, -2), (key1913, 1), (key1913, 1), (key1922, 1), (key1922, 1), (key1928, -1), (key1928, -1)]

def rawRow337 : Integer.Sparse Key := [(key1300, -1), (key1306, -1), (key1300, 2), (key1328, 1), (key1333, 1), (key1320, -1), (key1328, -1), (key1356, -2), (key1353, 1), (key1356, 1), (key1395, 1), (key1401, 1), (key1395, -2), (key1446, -1), (key1451, -1), (key1428, 1), (key1446, 1), (key1482, 2), (key1474, -1), (key1482, -1), (key1558, -1), (key1563, -1), (key1550, 1), (key1558, 1), (key1595, 1), (key1600, 1), (key1577, -1), (key1595, -1), (key1691, -1), (key1694, -1), (key1685, 1), (key1694, 1), (key1901, 2), (key1898, -1), (key1901, -1), (key1913, -2), (key1905, 1), (key1913, 1), (key1928, 1), (key1931, 1), (key1922, -1), (key1931, -1)]

def rawRow338 : Integer.Sparse Key := [(key1306, -1), (key1300, -1), (key1300, 2), (key1333, 1), (key1328, 1), (key1328, -1), (key1320, -1), (key1356, -2), (key1356, 1), (key1353, 1), (key1401, 1), (key1395, 1), (key1395, -2), (key1451, -1), (key1446, -1), (key1446, 1), (key1428, 1), (key1482, 2), (key1482, -1), (key1474, -1), (key1563, -1), (key1558, -1), (key1558, 1), (key1550, 1), (key1600, 1), (key1595, 1), (key1595, -1), (key1577, -1), (key1694, -1), (key1691, -1), (key1694, 1), (key1685, 1), (key1901, 2), (key1901, -1), (key1898, -1), (key1913, -2), (key1913, 1), (key1905, 1), (key1931, 1), (key1928, 1), (key1931, -1), (key1922, -1)]

def rawRow339 : Integer.Sparse Key := [(key1320, -1), (key1320, -1), (key1353, 2), (key1300, 1), (key1300, 1), (key1356, -1), (key1356, -1), (key1306, -2), (key1333, 1), (key1333, 1), (key1428, 1), (key1428, 1), (key1474, -2), (key1395, -1), (key1395, -1), (key1482, 1), (key1482, 1), (key1401, 2), (key1451, -1), (key1451, -1), (key1577, -1), (key1577, -1), (key1685, 1), (key1685, 1), (key1550, 1), (key1550, 1), (key1691, -1), (key1691, -1), (key1563, -1), (key1563, -1), (key1600, 1), (key1600, 1), (key1905, 2), (key1922, -1), (key1922, -1), (key1898, -2), (key1928, 1), (key1928, 1), (key1901, 1), (key1901, 1), (key1913, -1), (key1913, -1)]

def rawRow340 : Integer.Sparse Key := [(key1320, -1), (key1353, -1), (key1320, 2), (key1328, 1), (key1356, 1), (key1300, -1), (key1328, -1), (key1333, -2), (key1306, 1), (key1333, 1), (key1428, 1), (key1474, 1), (key1428, -2), (key1446, -1), (key1482, -1), (key1395, 1), (key1446, 1), (key1451, 2), (key1401, -1), (key1451, -1), (key1626, -1), (key1685, -1), (key1577, 1), (key1626, 1), (key1635, 1), (key1691, 1), (key1550, -1), (key1635, -1), (key1600, -1), (key1644, -1), (key1563, 1), (key1644, 1), (key1922, 2), (key1905, -1), (key1922, -1), (key1928, -2), (key1898, 1), (key1928, 1), (key1913, 1), (key1931, 1), (key1901, -1), (key1931, -1)]

def rawRow341 : Integer.Sparse Key := [(key1353, -1), (key1320, -1), (key1320, 2), (key1356, 1), (key1328, 1), (key1328, -1), (key1300, -1), (key1333, -2), (key1333, 1), (key1306, 1), (key1474, 1), (key1428, 1), (key1428, -2), (key1482, -1), (key1446, -1), (key1446, 1), (key1395, 1), (key1451, 2), (key1451, -1), (key1401, -1), (key1685, -1), (key1626, -1), (key1626, 1), (key1577, 1), (key1691, 1), (key1635, 1), (key1635, -1), (key1550, -1), (key1644, -1), (key1600, -1), (key1644, 1), (key1563, 1), (key1922, 2), (key1922, -1), (key1905, -1), (key1928, -2), (key1928, 1), (key1898, 1), (key1931, 1), (key1913, 1), (key1931, -1), (key1901, -1)]

def rawRow342 : Integer.Sparse Key := [(key1328, -1), (key1333, -1), (key1356, 2), (key1300, 1), (key1306, 1), (key1353, -1), (key1356, -1), (key1300, -2), (key1320, 1), (key1328, 1), (key1446, 1), (key1451, 1), (key1482, -2), (key1395, -1), (key1401, -1), (key1474, 1), (key1482, 1), (key1395, 2), (key1428, -1), (key1446, -1), (key1595, -1), (key1600, -1), (key1691, 1), (key1694, 1), (key1558, 1), (key1563, 1), (key1685, -1), (key1694, -1), (key1550, -1), (key1558, -1), (key1577, 1), (key1595, 1), (key1913, 2), (key1928, -1), (key1931, -1), (key1901, -2), (key1922, 1), (key1931, 1), (key1898, 1), (key1901, 1), (key1905, -1), (key1913, -1)]

def rawRow343 : Integer.Sparse Key := [(key1333, -1), (key1328, -1), (key1356, 2), (key1306, 1), (key1300, 1), (key1356, -1), (key1353, -1), (key1300, -2), (key1328, 1), (key1320, 1), (key1451, 1), (key1446, 1), (key1482, -2), (key1401, -1), (key1395, -1), (key1482, 1), (key1474, 1), (key1395, 2), (key1446, -1), (key1428, -1), (key1600, -1), (key1595, -1), (key1694, 1), (key1691, 1), (key1563, 1), (key1558, 1), (key1694, -1), (key1685, -1), (key1558, -1), (key1550, -1), (key1595, 1), (key1577, 1), (key1913, 2), (key1931, -1), (key1928, -1), (key1901, -2), (key1931, 1), (key1922, 1), (key1901, 1), (key1898, 1), (key1913, -1), (key1905, -1)]

def rawRow344 : Integer.Sparse Key := [(key1328, -1), (key1356, -1), (key1333, 2), (key1320, 1), (key1353, 1), (key1306, -1), (key1333, -1), (key1320, -2), (key1300, 1), (key1328, 1), (key1446, 1), (key1482, 1), (key1451, -2), (key1428, -1), (key1474, -1), (key1401, 1), (key1451, 1), (key1428, 2), (key1395, -1), (key1446, -1), (key1635, -1), (key1691, -1), (key1600, 1), (key1644, 1), (key1626, 1), (key1685, 1), (key1563, -1), (key1644, -1), (key1577, -1), (key1626, -1), (key1550, 1), (key1635, 1), (key1928, 2), (key1913, -1), (key1931, -1), (key1922, -2), (key1901, 1), (key1931, 1), (key1905, 1), (key1922, 1), (key1898, -1), (key1928, -1)]

def rawRow345 : Integer.Sparse Key := [(key1356, -1), (key1328, -1), (key1333, 2), (key1353, 1), (key1320, 1), (key1333, -1), (key1306, -1), (key1320, -2), (key1328, 1), (key1300, 1), (key1482, 1), (key1446, 1), (key1451, -2), (key1474, -1), (key1428, -1), (key1451, 1), (key1401, 1), (key1428, 2), (key1446, -1), (key1395, -1), (key1691, -1), (key1635, -1), (key1644, 1), (key1600, 1), (key1685, 1), (key1626, 1), (key1644, -1), (key1563, -1), (key1626, -1), (key1577, -1), (key1635, 1), (key1550, 1), (key1928, 2), (key1931, -1), (key1913, -1), (key1922, -2), (key1931, 1), (key1901, 1), (key1922, 1), (key1905, 1), (key1928, -1), (key1898, -1)]

def rawRow346 : Integer.Sparse Key := [(key1395, -1), (key1395, -1), (key1401, 2), (key1550, 1), (key1550, 1), (key1563, -1), (key1563, -1), (key1898, -2), (key1901, 1), (key1901, 1), (key1300, 1), (key1300, 1), (key1306, -2), (key1577, -1), (key1577, -1), (key1600, 1), (key1600, 1), (key1905, 2), (key1913, -1), (key1913, -1), (key1320, -1), (key1320, -1), (key1333, 1), (key1333, 1), (key1428, 1), (key1428, 1), (key1451, -1), (key1451, -1), (key1922, -1), (key1922, -1), (key1928, 1), (key1928, 1), (key1353, 2), (key1356, -1), (key1356, -1), (key1474, -2), (key1482, 1), (key1482, 1), (key1685, 1), (key1685, 1), (key1691, -1), (key1691, -1)]

def rawRow347 : Integer.Sparse Key := [(key1395, -1), (key1401, -1), (key1395, 2), (key1558, 1), (key1563, 1), (key1550, -1), (key1558, -1), (key1901, -2), (key1898, 1), (key1901, 1), (key1300, 1), (key1306, 1), (key1300, -2), (key1595, -1), (key1600, -1), (key1577, 1), (key1595, 1), (key1913, 2), (key1905, -1), (key1913, -1), (key1328, -1), (key1333, -1), (key1320, 1), (key1328, 1), (key1446, 1), (key1451, 1), (key1428, -1), (key1446, -1), (key1928, -1), (key1931, -1), (key1922, 1), (key1931, 1), (key1356, 2), (key1353, -1), (key1356, -1), (key1482, -2), (key1474, 1), (key1482, 1), (key1691, 1), (key1694, 1), (key1685, -1), (key1694, -1)]

def rawRow348 : Integer.Sparse Key := [(key1401, -1), (key1395, -1), (key1395, 2), (key1563, 1), (key1558, 1), (key1558, -1), (key1550, -1), (key1901, -2), (key1901, 1), (key1898, 1), (key1306, 1), (key1300, 1), (key1300, -2), (key1600, -1), (key1595, -1), (key1595, 1), (key1577, 1), (key1913, 2), (key1913, -1), (key1905, -1), (key1333, -1), (key1328, -1), (key1328, 1), (key1320, 1), (key1451, 1), (key1446, 1), (key1446, -1), (key1428, -1), (key1931, -1), (key1928, -1), (key1931, 1), (key1922, 1), (key1356, 2), (key1356, -1), (key1353, -1), (key1482, -2), (key1482, 1), (key1474, 1), (key1694, 1), (key1691, 1), (key1694, -1), (key1685, -1)]

def rawRow349 : Integer.Sparse Key := [(key1550, -1), (key1550, -1), (key1898, 2), (key1395, 1), (key1395, 1), (key1901, -1), (key1901, -1), (key1401, -2), (key1563, 1), (key1563, 1), (key1577, 1), (key1577, 1), (key1905, -2), (key1300, -1), (key1300, -1), (key1913, 1), (key1913, 1), (key1306, 2), (key1600, -1), (key1600, -1), (key1428, -1), (key1428, -1), (key1922, 1), (key1922, 1), (key1320, 1), (key1320, 1), (key1928, -1), (key1928, -1), (key1333, -1), (key1333, -1), (key1451, 1), (key1451, 1), (key1474, 2), (key1685, -1), (key1685, -1), (key1353, -2), (key1691, 1), (key1691, 1), (key1356, 1), (key1356, 1), (key1482, -1), (key1482, -1)]

def rawRow350 : Integer.Sparse Key := [(key1550, -1), (key1898, -1), (key1550, 2), (key1558, 1), (key1901, 1), (key1395, -1), (key1558, -1), (key1563, -2), (key1401, 1), (key1563, 1), (key1577, 1), (key1905, 1), (key1577, -2), (key1595, -1), (key1913, -1), (key1300, 1), (key1595, 1), (key1600, 2), (key1306, -1), (key1600, -1), (key1626, -1), (key1922, -1), (key1428, 1), (key1626, 1), (key1635, 1), (key1928, 1), (key1320, -1), (key1635, -1), (key1451, -1), (key1644, -1), (key1333, 1), (key1644, 1), (key1685, 2), (key1474, -1), (key1685, -1), (key1691, -2), (key1353, 1), (key1691, 1), (key1482, 1), (key1694, 1), (key1356, -1), (key1694, -1)]

def rawRow351 : Integer.Sparse Key := [(key1898, -1), (key1550, -1), (key1550, 2), (key1901, 1), (key1558, 1), (key1558, -1), (key1395, -1), (key1563, -2), (key1563, 1), (key1401, 1), (key1905, 1), (key1577, 1), (key1577, -2), (key1913, -1), (key1595, -1), (key1595, 1), (key1300, 1), (key1600, 2), (key1600, -1), (key1306, -1), (key1922, -1), (key1626, -1), (key1626, 1), (key1428, 1), (key1928, 1), (key1635, 1), (key1635, -1), (key1320, -1), (key1644, -1), (key1451, -1), (key1644, 1), (key1333, 1), (key1685, 2), (key1685, -1), (key1474, -1), (key1691, -2), (key1691, 1), (key1353, 1), (key1694, 1), (key1482, 1), (key1694, -1), (key1356, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow352 : Integer.Sparse Key := [(key1558, -1), (key1563, -1), (key1901, 2), (key1395, 1), (key1401, 1), (key1898, -1), (key1901, -1), (key1395, -2), (key1550, 1), (key1558, 1), (key1595, 1), (key1600, 1), (key1913, -2), (key1300, -1), (key1306, -1), (key1905, 1), (key1913, 1), (key1300, 2), (key1577, -1), (key1595, -1), (key1446, -1), (key1451, -1), (key1928, 1), (key1931, 1), (key1328, 1), (key1333, 1), (key1922, -1), (key1931, -1), (key1320, -1), (key1328, -1), (key1428, 1), (key1446, 1), (key1482, 2), (key1691, -1), (key1694, -1), (key1356, -2), (key1685, 1), (key1694, 1), (key1353, 1), (key1356, 1), (key1474, -1), (key1482, -1)]

def rawRow353 : Integer.Sparse Key := [(key1563, -1), (key1558, -1), (key1901, 2), (key1401, 1), (key1395, 1), (key1901, -1), (key1898, -1), (key1395, -2), (key1558, 1), (key1550, 1), (key1600, 1), (key1595, 1), (key1913, -2), (key1306, -1), (key1300, -1), (key1913, 1), (key1905, 1), (key1300, 2), (key1595, -1), (key1577, -1), (key1451, -1), (key1446, -1), (key1931, 1), (key1928, 1), (key1333, 1), (key1328, 1), (key1931, -1), (key1922, -1), (key1328, -1), (key1320, -1), (key1446, 1), (key1428, 1), (key1482, 2), (key1694, -1), (key1691, -1), (key1356, -2), (key1694, 1), (key1685, 1), (key1356, 1), (key1353, 1), (key1482, -1), (key1474, -1)]

def rawRow354 : Integer.Sparse Key := [(key1558, -1), (key1901, -1), (key1563, 2), (key1550, 1), (key1898, 1), (key1401, -1), (key1563, -1), (key1550, -2), (key1395, 1), (key1558, 1), (key1595, 1), (key1913, 1), (key1600, -2), (key1577, -1), (key1905, -1), (key1306, 1), (key1600, 1), (key1577, 2), (key1300, -1), (key1595, -1), (key1635, -1), (key1928, -1), (key1451, 1), (key1644, 1), (key1626, 1), (key1922, 1), (key1333, -1), (key1644, -1), (key1428, -1), (key1626, -1), (key1320, 1), (key1635, 1), (key1691, 2), (key1482, -1), (key1694, -1), (key1685, -2), (key1356, 1), (key1694, 1), (key1474, 1), (key1685, 1), (key1353, -1), (key1691, -1)]

def rawRow355 : Integer.Sparse Key := [(key1901, -1), (key1558, -1), (key1563, 2), (key1898, 1), (key1550, 1), (key1563, -1), (key1401, -1), (key1550, -2), (key1558, 1), (key1395, 1), (key1913, 1), (key1595, 1), (key1600, -2), (key1905, -1), (key1577, -1), (key1600, 1), (key1306, 1), (key1577, 2), (key1595, -1), (key1300, -1), (key1928, -1), (key1635, -1), (key1644, 1), (key1451, 1), (key1922, 1), (key1626, 1), (key1644, -1), (key1333, -1), (key1626, -1), (key1428, -1), (key1635, 1), (key1320, 1), (key1691, 2), (key1694, -1), (key1482, -1), (key1685, -2), (key1694, 1), (key1356, 1), (key1685, 1), (key1474, 1), (key1691, -1), (key1353, -1)]

def rawRow356 : Integer.Sparse Key := [(key1428, -1), (key1428, -1), (key1474, 2), (key1577, 1), (key1577, 1), (key1685, -1), (key1685, -1), (key1905, -2), (key1922, 1), (key1922, 1), (key1320, 1), (key1320, 1), (key1353, -2), (key1550, -1), (key1550, -1), (key1691, 1), (key1691, 1), (key1898, 2), (key1928, -1), (key1928, -1), (key1300, -1), (key1300, -1), (key1356, 1), (key1356, 1), (key1395, 1), (key1395, 1), (key1482, -1), (key1482, -1), (key1901, -1), (key1901, -1), (key1913, 1), (key1913, 1), (key1306, 2), (key1333, -1), (key1333, -1), (key1401, -2), (key1451, 1), (key1451, 1), (key1563, 1), (key1563, 1), (key1600, -1), (key1600, -1)]

def rawRow357 : Integer.Sparse Key := [(key1428, -1), (key1474, -1), (key1428, 2), (key1626, 1), (key1685, 1), (key1577, -1), (key1626, -1), (key1922, -2), (key1905, 1), (key1922, 1), (key1320, 1), (key1353, 1), (key1320, -2), (key1635, -1), (key1691, -1), (key1550, 1), (key1635, 1), (key1928, 2), (key1898, -1), (key1928, -1), (key1328, -1), (key1356, -1), (key1300, 1), (key1328, 1), (key1446, 1), (key1482, 1), (key1395, -1), (key1446, -1), (key1913, -1), (key1931, -1), (key1901, 1), (key1931, 1), (key1333, 2), (key1306, -1), (key1333, -1), (key1451, -2), (key1401, 1), (key1451, 1), (key1600, 1), (key1644, 1), (key1563, -1), (key1644, -1)]

def rawRow358 : Integer.Sparse Key := [(key1474, -1), (key1428, -1), (key1428, 2), (key1685, 1), (key1626, 1), (key1626, -1), (key1577, -1), (key1922, -2), (key1922, 1), (key1905, 1), (key1353, 1), (key1320, 1), (key1320, -2), (key1691, -1), (key1635, -1), (key1635, 1), (key1550, 1), (key1928, 2), (key1928, -1), (key1898, -1), (key1356, -1), (key1328, -1), (key1328, 1), (key1300, 1), (key1482, 1), (key1446, 1), (key1446, -1), (key1395, -1), (key1931, -1), (key1913, -1), (key1931, 1), (key1901, 1), (key1333, 2), (key1333, -1), (key1306, -1), (key1451, -2), (key1451, 1), (key1401, 1), (key1644, 1), (key1600, 1), (key1644, -1), (key1563, -1)]

def rawRow359 : Integer.Sparse Key := [(key1577, -1), (key1577, -1), (key1905, 2), (key1428, 1), (key1428, 1), (key1922, -1), (key1922, -1), (key1474, -2), (key1685, 1), (key1685, 1), (key1550, 1), (key1550, 1), (key1898, -2), (key1320, -1), (key1320, -1), (key1928, 1), (key1928, 1), (key1353, 2), (key1691, -1), (key1691, -1), (key1395, -1), (key1395, -1), (key1901, 1), (key1901, 1), (key1300, 1), (key1300, 1), (key1913, -1), (key1913, -1), (key1356, -1), (key1356, -1), (key1482, 1), (key1482, 1), (key1401, 2), (key1563, -1), (key1563, -1), (key1306, -2), (key1600, 1), (key1600, 1), (key1333, 1), (key1333, 1), (key1451, -1), (key1451, -1)]

def rawRow360 : Integer.Sparse Key := [(key1577, -1), (key1905, -1), (key1577, 2), (key1626, 1), (key1922, 1), (key1428, -1), (key1626, -1), (key1685, -2), (key1474, 1), (key1685, 1), (key1550, 1), (key1898, 1), (key1550, -2), (key1635, -1), (key1928, -1), (key1320, 1), (key1635, 1), (key1691, 2), (key1353, -1), (key1691, -1), (key1558, -1), (key1901, -1), (key1395, 1), (key1558, 1), (key1595, 1), (key1913, 1), (key1300, -1), (key1595, -1), (key1482, -1), (key1694, -1), (key1356, 1), (key1694, 1), (key1563, 2), (key1401, -1), (key1563, -1), (key1600, -2), (key1306, 1), (key1600, 1), (key1451, 1), (key1644, 1), (key1333, -1), (key1644, -1)]

def rawRow361 : Integer.Sparse Key := [(key1905, -1), (key1577, -1), (key1577, 2), (key1922, 1), (key1626, 1), (key1626, -1), (key1428, -1), (key1685, -2), (key1685, 1), (key1474, 1), (key1898, 1), (key1550, 1), (key1550, -2), (key1928, -1), (key1635, -1), (key1635, 1), (key1320, 1), (key1691, 2), (key1691, -1), (key1353, -1), (key1901, -1), (key1558, -1), (key1558, 1), (key1395, 1), (key1913, 1), (key1595, 1), (key1595, -1), (key1300, -1), (key1694, -1), (key1482, -1), (key1694, 1), (key1356, 1), (key1563, 2), (key1563, -1), (key1401, -1), (key1600, -2), (key1600, 1), (key1306, 1), (key1644, 1), (key1451, 1), (key1644, -1), (key1333, -1)]

def rawRow362 : Integer.Sparse Key := [(key1626, -1), (key1685, -1), (key1922, 2), (key1428, 1), (key1474, 1), (key1905, -1), (key1922, -1), (key1428, -2), (key1577, 1), (key1626, 1), (key1635, 1), (key1691, 1), (key1928, -2), (key1320, -1), (key1353, -1), (key1898, 1), (key1928, 1), (key1320, 2), (key1550, -1), (key1635, -1), (key1446, -1), (key1482, -1), (key1913, 1), (key1931, 1), (key1328, 1), (key1356, 1), (key1901, -1), (key1931, -1), (key1300, -1), (key1328, -1), (key1395, 1), (key1446, 1), (key1451, 2), (key1600, -1), (key1644, -1), (key1333, -2), (key1563, 1), (key1644, 1), (key1306, 1), (key1333, 1), (key1401, -1), (key1451, -1)]

def rawRow363 : Integer.Sparse Key := [(key1685, -1), (key1626, -1), (key1922, 2), (key1474, 1), (key1428, 1), (key1922, -1), (key1905, -1), (key1428, -2), (key1626, 1), (key1577, 1), (key1691, 1), (key1635, 1), (key1928, -2), (key1353, -1), (key1320, -1), (key1928, 1), (key1898, 1), (key1320, 2), (key1635, -1), (key1550, -1), (key1482, -1), (key1446, -1), (key1931, 1), (key1913, 1), (key1356, 1), (key1328, 1), (key1931, -1), (key1901, -1), (key1328, -1), (key1300, -1), (key1446, 1), (key1395, 1), (key1451, 2), (key1644, -1), (key1600, -1), (key1333, -2), (key1644, 1), (key1563, 1), (key1333, 1), (key1306, 1), (key1451, -1), (key1401, -1)]

def rawRow364 : Integer.Sparse Key := [(key1626, -1), (key1922, -1), (key1685, 2), (key1577, 1), (key1905, 1), (key1474, -1), (key1685, -1), (key1577, -2), (key1428, 1), (key1626, 1), (key1635, 1), (key1928, 1), (key1691, -2), (key1550, -1), (key1898, -1), (key1353, 1), (key1691, 1), (key1550, 2), (key1320, -1), (key1635, -1), (key1595, -1), (key1913, -1), (key1482, 1), (key1694, 1), (key1558, 1), (key1901, 1), (key1356, -1), (key1694, -1), (key1395, -1), (key1558, -1), (key1300, 1), (key1595, 1), (key1600, 2), (key1451, -1), (key1644, -1), (key1563, -2), (key1333, 1), (key1644, 1), (key1401, 1), (key1563, 1), (key1306, -1), (key1600, -1)]

def rawRow365 : Integer.Sparse Key := [(key1922, -1), (key1626, -1), (key1685, 2), (key1905, 1), (key1577, 1), (key1685, -1), (key1474, -1), (key1577, -2), (key1626, 1), (key1428, 1), (key1928, 1), (key1635, 1), (key1691, -2), (key1898, -1), (key1550, -1), (key1691, 1), (key1353, 1), (key1550, 2), (key1635, -1), (key1320, -1), (key1913, -1), (key1595, -1), (key1694, 1), (key1482, 1), (key1901, 1), (key1558, 1), (key1694, -1), (key1356, -1), (key1558, -1), (key1395, -1), (key1595, 1), (key1300, 1), (key1600, 2), (key1644, -1), (key1451, -1), (key1563, -2), (key1644, 1), (key1333, 1), (key1563, 1), (key1401, 1), (key1600, -1), (key1306, -1)]

def rawRow366 : Integer.Sparse Key := [(key1446, -1), (key1451, -1), (key1482, 2), (key1595, 1), (key1600, 1), (key1691, -1), (key1694, -1), (key1913, -2), (key1928, 1), (key1931, 1), (key1328, 1), (key1333, 1), (key1356, -2), (key1558, -1), (key1563, -1), (key1685, 1), (key1694, 1), (key1901, 2), (key1922, -1), (key1931, -1), (key1300, -1), (key1306, -1), (key1353, 1), (key1356, 1), (key1395, 1), (key1401, 1), (key1474, -1), (key1482, -1), (key1898, -1), (key1901, -1), (key1905, 1), (key1913, 1), (key1300, 2), (key1320, -1), (key1328, -1), (key1395, -2), (key1428, 1), (key1446, 1), (key1550, 1), (key1558, 1), (key1577, -1), (key1595, -1)]

def rawRow367 : Integer.Sparse Key := [(key1451, -1), (key1446, -1), (key1482, 2), (key1600, 1), (key1595, 1), (key1694, -1), (key1691, -1), (key1913, -2), (key1931, 1), (key1928, 1), (key1333, 1), (key1328, 1), (key1356, -2), (key1563, -1), (key1558, -1), (key1694, 1), (key1685, 1), (key1901, 2), (key1931, -1), (key1922, -1), (key1306, -1), (key1300, -1), (key1356, 1), (key1353, 1), (key1401, 1), (key1395, 1), (key1482, -1), (key1474, -1), (key1901, -1), (key1898, -1), (key1913, 1), (key1905, 1), (key1300, 2), (key1328, -1), (key1320, -1), (key1395, -2), (key1446, 1), (key1428, 1), (key1558, 1), (key1550, 1), (key1595, -1), (key1577, -1)]

def rawRow368 : Integer.Sparse Key := [(key1446, -1), (key1482, -1), (key1451, 2), (key1635, 1), (key1691, 1), (key1600, -1), (key1644, -1), (key1928, -2), (key1913, 1), (key1931, 1), (key1328, 1), (key1356, 1), (key1333, -2), (key1626, -1), (key1685, -1), (key1563, 1), (key1644, 1), (key1922, 2), (key1901, -1), (key1931, -1), (key1320, -1), (key1353, -1), (key1306, 1), (key1333, 1), (key1428, 1), (key1474, 1), (key1401, -1), (key1451, -1), (key1905, -1), (key1922, -1), (key1898, 1), (key1928, 1), (key1320, 2), (key1300, -1), (key1328, -1), (key1428, -2), (key1395, 1), (key1446, 1), (key1577, 1), (key1626, 1), (key1550, -1), (key1635, -1)]

def rawRow369 : Integer.Sparse Key := [(key1482, -1), (key1446, -1), (key1451, 2), (key1691, 1), (key1635, 1), (key1644, -1), (key1600, -1), (key1928, -2), (key1931, 1), (key1913, 1), (key1356, 1), (key1328, 1), (key1333, -2), (key1685, -1), (key1626, -1), (key1644, 1), (key1563, 1), (key1922, 2), (key1931, -1), (key1901, -1), (key1353, -1), (key1320, -1), (key1333, 1), (key1306, 1), (key1474, 1), (key1428, 1), (key1451, -1), (key1401, -1), (key1922, -1), (key1905, -1), (key1928, 1), (key1898, 1), (key1320, 2), (key1328, -1), (key1300, -1), (key1428, -2), (key1446, 1), (key1395, 1), (key1626, 1), (key1577, 1), (key1635, -1), (key1550, -1)]

def rawRow370 : Integer.Sparse Key := [(key1595, -1), (key1600, -1), (key1913, 2), (key1446, 1), (key1451, 1), (key1928, -1), (key1931, -1), (key1482, -2), (key1691, 1), (key1694, 1), (key1558, 1), (key1563, 1), (key1901, -2), (key1328, -1), (key1333, -1), (key1922, 1), (key1931, 1), (key1356, 2), (key1685, -1), (key1694, -1), (key1395, -1), (key1401, -1), (key1898, 1), (key1901, 1), (key1300, 1), (key1306, 1), (key1905, -1), (key1913, -1), (key1353, -1), (key1356, -1), (key1474, 1), (key1482, 1), (key1395, 2), (key1550, -1), (key1558, -1), (key1300, -2), (key1577, 1), (key1595, 1), (key1320, 1), (key1328, 1), (key1428, -1), (key1446, -1)]

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

def rawRow7377 : Integer.Sparse Key := [(key0, -24), (key83, 6), (key83, 6), (key83, 6), (key83, 6)]

end MUB6.Certificate.GramRows

end OAI
end


