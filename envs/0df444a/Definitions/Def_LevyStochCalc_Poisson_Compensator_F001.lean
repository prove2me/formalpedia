-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Compensator_F001
-- name    : LevyStochCalc_Poisson_Compensator_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:51:54.714969+00:00
-- url     : https://prove2.me/theorems/096db0e1-f89c-4926-88b8-84b5f30052f2
-- title:
--   Source declarations: LevyStochCalc.Poisson.Compensator
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Compensator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_LevyStochCalc_Poisson_FiniteActivity_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F001
import Definitions.Def_SourceProof_a6be76747887c395a8454e6f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The reference intensity as compensator on a finite-activity window

On a predictable rectangle the count of the Poisson random measure is independent of the past
event carried by the rectangle, so its mean factorises as the probability of that event times
the intensity of the time–mark part. The sets on which the two mean occupations agree form a
Dynkin system — complements by subtracting from the finite occupation of the window, countable
disjoint unions by monotone convergence — so they agree on every predictable set.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Rectangle

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Rectangle

section Window

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The compensator identity for predictable functions. -/
theorem lintegral_lintegral_slice_eq (hℱ : IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {Ψ : Ω × ℝ × E → ℝ≥0∞}
    (hΨ : Measurable[Probability.markedPredictableSigma ℱ ν] Ψ) :
    ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(N.N ω) ∂P
      = ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(referenceIntensity ν) ∂P :=
  (_root_.Prove2MeSourceProof.h_a6be76747887c395a8454e6f N hℱ hA hAν T hΨ).2.2
end Window

end LevyStochCalc.Poisson


