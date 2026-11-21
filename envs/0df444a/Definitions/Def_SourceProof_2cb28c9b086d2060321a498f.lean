-- Prove2me | Definitions.Def_SourceProof_2cb28c9b086d2060321a498f
-- name    : SourceProof_2cb28c9b086d2060321a498f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:06:06.114749+00:00
-- url     : https://prove2.me/theorems/d5bf91e7-d397-40d1-b568-82ac34c01a44
-- title:
--   LevyStochCalc source module: SourceProof_2cb28c9b086d2060321a498f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_im` comes from the `LevyStochCalc.Poisson.CharacterStrictProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F000
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F002
import Definitions.Def_SourceProof_dc6cca7c0c003bf51b6e990a

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

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

include hℱ hBm hA hAν in

theorem _root_.Prove2MeSourceProof.h_2cb28c9b086d2060321a498f (T : ℝ) (e₀ : E) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (charStrictPred N w Bfam A T e₀ s ω).im := by
  have hbase : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (LevyStochCalc.Poisson.predStrict N w Bfam A T) :=
    (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (LevyStochCalc.Poisson.markedPredictable_predStrict N hℱ w hBm hA hAν T))
  have hmp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e =>
      Real.sin (LevyStochCalc.Poisson.predStrict N w Bfam A T ω s e) :=
    Continuous.comp_markedProgressivelyMeasurable (g := Real.sin) Real.continuous_sin
      (by simp) hbase
  have hsub := _root_.Prove2MeSourceProof.h_dc6cca7c0c003bf51b6e990a (LevyStochCalc.Poisson.progressivelyMeasurable_eval_mark hmp e₀) T
  have heq : (fun ω s => Real.sin (LevyStochCalc.Poisson.predStrict N w Bfam A T ω (min s T) e₀))
      = fun ω s => (LevyStochCalc.Poisson.charStrictPred N w Bfam A T e₀ s ω).im := by
    funext ω s
    rw [LevyStochCalc.Poisson.charStrictPred, LevyStochCalc.Poisson.exp_I_mul_ofReal_im]
  rwa [heq] at hsub
section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

end Parts

end Clamped

end LevyStochCalc.Poisson


