-- Prove2me | Definitions.Def_Q238L051
-- name    : Q238L051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:47:35.026947+00:00
-- url     : https://prove2.me/theorems/c4f7e1ec-7def-4a82-a8b2-a162f968d216
-- title:
--   Definitions bundle Q238L051 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.member_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.budgetBound`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Encoding_MaskOutput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/MaskOutput.lean), [`KMedianRecovery_Strictness_BidBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L041` and `Q238L043` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L054`; the statement `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L041
import Definitions.Def_Q238L043

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
noncomputable def budgetBound : Polynomial ℕ := Polynomial.X+bidBound+100*(Polynomial.X+1)^2
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MaskOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskOutput
open WordOperations WordList
variable {n : ℕ}
noncomputable def member_computes : PolyComputes member :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (discardPrefix_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes)).comp
    ((mapWith_computes member_computes).comp Flatten.run_computes)
  simpa only [Function.comp_def] using computes
end MetricKMedianRecovery.BitMachine.BinaryMaskOutput

end OAI
end


