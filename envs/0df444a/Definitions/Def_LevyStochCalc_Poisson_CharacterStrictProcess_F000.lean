-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F000
-- name    : LevyStochCalc_Poisson_CharacterStrictProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:59:50.785623+00:00
-- url     : https://prove2.me/theorems/cb3089f5-b1b7-4f32-8a41-c8ee0e0bd0b7
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterStrictProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterStrictProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Evaluating a marked progressively measurable process at a fixed mark. -/
theorem progressivelyMeasurable_eval_mark {ψ : Ω → ℝ → E → ℝ}
    (h : Probability.MarkedProgressivelyMeasurable ℱ ψ) (e : E) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => ψ ω s e := by
  intro t
  have hg : @Measurable (Ω × ℝ) (Ω × ℝ × E)
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance)
      fun p : Ω × ℝ => (p.1, (p.2, e)) :=
    Measurable.prodMk measurable_fst (measurable_snd.prodMk measurable_const)
  exact (h t).comp_measurable hg
end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

end Parts

end Clamped

end LevyStochCalc.Poisson


