-- Prove2me | Definitions.Def_Q238L047
-- name    : Q238L047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:43:13.603392+00:00
-- url     : https://prove2.me/theorems/fe0e5212-22d9-468c-b3d4-14e2e65444ad
-- title:
--   Definitions bundle Q238L047 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.callInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.add_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.keep_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.retain_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.atRawInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.metricContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.minus_computes`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Algorithms_CandidateSanitize`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/CandidateSanitize.lean), [`KMedianRecovery_Algorithms_GlobalOuter`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean), [`KMedianRecovery_Recovery_FinImages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinImages.lean), [`KMedianRecovery_Sampling_SamplingStateMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean).
--
--   **Imports.** It imports the bundle `Q238L039` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L050`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238L039

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def minus_computes : PolyComputes minus := NatOps.sub discardPrefix_computes extractPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def add_computes : PolyComputes add := (extractPrefix_computes.comp extractPrefix_computes).pair
  ((extractPrefix_computes.comp discardPrefix_computes).append (cons_computes discardPrefix_computes (const_computes [])))
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) := by
  simpa only [keep,Bool.decide_and,Function.comp_def] using (NatOps.le (((discardPrefix_computes.comp discardPrefix_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes)
    extractPrefix_computes).and
      (NatOps.le (((discardPrefix_computes.comp extractPrefix_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes)
        extractPrefix_computes)
noncomputable def retain_computes : PolyComputes retain := keep_computes.cond
  (cons_computes discardPrefix_computes (const_computes [])) (const_computes [])
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (field_computes 0)
  (cons_computes (field_computes 1) (const_computes []))
noncomputable def atRawInput_computes : PolyComputes atRawInput := cons_computes (extractPrefix_computes.comp (field_computes 0))
  (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes (extractPrefix_computes.comp (field_computes 2))
    (cons_computes discardPrefix_computes (const_computes []))))
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def callInput_computes : PolyComputes callInput := list_computes
  [extractPrefix ∘ extractPrefix,discardPrefix,discardPrefix ∘ extractPrefix] (by
    intro f hf;refine Classical.choice ?_;simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨extractPrefix_computes.comp extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩
    · exact ⟨extractPrefix_computes.comp discardPrefix_computes⟩)
attribute [local irreducible] BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


