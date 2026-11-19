-- Prove2me | Definitions.Def_LevyStochCalc_Probability_IndepLimit_F000
-- name    : LevyStochCalc_Probability_IndepLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:03:36.100403+00:00
-- url     : https://prove2.me/theorems/ad24d04d-15fe-46eb-9511-f45a333ce82c
-- title:
--   LevyStochCalc source module: LevyStochCalc.Probability.IndepLimit
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Probability.IndepLimit in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Independence.Integration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence survives almost-everywhere limits

If each random variable `X n` is independent of a σ-algebra `m` and `X n → Y` almost
everywhere, then `Y` is independent of `m`: for a set `A ∈ m` the laws of `Y` under `P|_A` and
under `P(A) • P` have the same integrals against bounded continuous functions, by dominated
convergence, hence coincide.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace 𝓧] [MeasurableSpace 𝓧] [BorelSpace 𝓧] [HasOuterApproxClosed 𝓧]

omit [HasOuterApproxClosed 𝓧] in
/-- For `A ∈ m` and `X` independent of `m`, `∫_A f ∘ X = P(A) ∫ f ∘ X`. -/
lemma setIntegral_eq_measure_mul_of_indep (hm : m ≤ mΩ) {X : Ω → 𝓧}
    (hX : Measurable[mΩ] X) (hind : Indep m (MeasurableSpace.comap X inferInstance) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) (f : 𝓧 →ᵇ ℝ) :
    ∫ ω in A, f (X ω) ∂P = (P A).toReal * ∫ ω, f (X ω) ∂P := by
  have hA' : MeasurableSet[mΩ] A := hm _ hA
  have hindf : IndepFun (A.indicator (1 : Ω → ℝ)) (fun ω => f (X ω)) P := by
    change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) P
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
    · have hmeas : Measurable[m] (A.indicator (1 : Ω → ℝ)) := by
        letI := m
        exact measurable_const.indicator hA
      exact hmeas.comap_le
    · rw [show (fun ω => f (X ω)) = f ∘ X from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (f.continuous.measurable.comap_le)
  have hfX : Integrable (fun ω => f (X ω)) P :=
    Integrable.of_bound (f.continuous.measurable.comp hX).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  have h := hindf.integral_mul_eq_mul_integral
    ((integrable_const (1 : ℝ)).indicator hA').aestronglyMeasurable hfX.aestronglyMeasurable
  have hfun : (A.indicator (1 : Ω → ℝ) * fun ω => f (X ω)) = A.indicator (fun ω => f (X ω)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [integral_indicator_one hA', hfun, integral_indicator hA', measureReal_def] at h
  exact h
end LevyStochCalc.Probability


