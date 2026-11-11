-- Prove2me | Definitions.Def_Q224R002
-- name    : Q224R002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:19.72221+00:00
-- url     : https://prove2.me/theorems/029472f1-5d0b-422e-8350-b3658aa0f091
-- title:
--   Definitions bundle Q224R002 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 2 definitions and 13 theorems. The definitions and types are `OAI.MetricKMedianRecovery.RefinedRecovery.algorithm`, `OAI.MetricKMedianRecovery.RefinedRecovery.totalProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Refined_ConditionalRecovery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/ConditionalRecovery.lean).
--
--   **Imports.** It imports the published bundles `Def_KMedianRefinedRecovery` and `Def_MetricKMedian`; the bundles `Q224R000` and `Q224R001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI_MetricKMedianRecovery_RefinedRecovery_refined_recovery_conditional` and `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery_conditional_s35`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_MetricKMedian
import Definitions.Def_Q224R000
import Definitions.Def_Q224R001

section
-- module Solutions.Q224_RR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_ConditionalRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

open MetricKMedian.Binary

noncomputable def totalProgram {f : MetricKMedian.Instance → List Bool}
    (P : PolyProgram MetricKMedian.InstanceProgram.encode id f) :
    PolyProgram id id (fun xs => f (CheckedInput.checked (MetricKMedian.InputParser.raw
      (first (first xs))))) :=
  (((WordTransducer.projecting false).program.comp
    (WordTransducer.projecting false).program).comp CheckedInput.parseProgram).comp P

noncomputable def algorithm {f : MetricKMedian.Instance → List Bool}
    (P : PolyProgram MetricKMedian.InstanceProgram.encode id f) : BinaryRandomizedAlgorithm where
  randomBits := 0
  run p := f (CheckedInput.checked (MetricKMedian.InputParser.raw (first (first (pairBits p)))))
  computation := ((totalProgram P).recode pairBits (fun _ => rfl) (fun _ => rfl)).stock
  finiteWorkAlphabet := ((totalProgram P).recode pairBits (fun _ => rfl) (fun _ => rfl)).finite_work

end MetricKMedianRecovery.RefinedRecovery

end OAI
end


