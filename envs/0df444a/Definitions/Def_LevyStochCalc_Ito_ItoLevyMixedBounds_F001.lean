-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
-- name    : LevyStochCalc_Ito_ItoLevyMixedBounds_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:19:49.116495+00:00
-- url     : https://prove2.me/theorems/d93eb82f-9ff3-44c8-a855-54ced412c695
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyMixedBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyMixedBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F000
import Definitions.Def_SourceProof_d7551ffa72e4a3e8bbb658cc

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- A component of the mixed diffusion integrand is bounded, through the gradient bound, by the
sum of the absolute entries of the corresponding column of the diffusion matrix. -/
theorem abs_mixedDiffusionIntegrand_le {σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)} {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (s : ℝ) (y x : Fin n → ℝ) (j : Fin d) :
    |mixedDiffusionIntegrand u σ s y x j| ≤ K₁ * ∑ i, |σ s x i j| := by
  unfold mixedDiffusionIntegrand
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hK₁ s y i) (abs_nonneg _)
/-- The mixed jump increment is bounded, through the gradient bound, by `n K₁` times the sum of
the absolute coordinates of the jump size. -/
theorem abs_mixedJumpIncrement_le (hu : ContDiff ℝ 2 (Function.uncurry u))
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₁0 : 0 ≤ K₁) (s : ℝ) (y x : Fin n → ℝ)
    (e : E) : |mixedJumpIncrement u γ s y x e| ≤ (n : ℝ) * K₁ * ∑ i, |γ s x e i| := by
  unfold mixedJumpIncrement
  refine (abs_sub_le_of_gradient_le hu s (hK₁ s) y (γ s x e)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_le_sum_abs _) (mul_nonneg (Nat.cast_nonneg n) hK₁0)
/-- The mixed compensator-drift integrand is bounded, through the Hessian bound, by `n³ K₂`
times the sum of the squared coordinates of the jump size. -/
theorem abs_mixedCompensatorDriftIntegrand_le (hu : ContDiff ℝ 2 (Function.uncurry u))
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (hK₂0 : 0 ≤ K₂) (s : ℝ) (y x : Fin n → ℝ)
    (e : E) :
    |mixedCompensatorDriftIntegrand u γ s y x e|
      ≤ (n : ℝ) ^ 2 * K₂ * ((n : ℝ) * ∑ i, γ s x e i ^ 2) := by
  unfold mixedCompensatorDriftIntegrand
  refine (_root_.Prove2MeSourceProof.h_d7551ffa72e4a3e8bbb658cc hu s (hK₂ s) y (γ s x e)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sq_le_card_mul_sum_sq _)
    (mul_nonneg (sq_nonneg _) hK₂0)
/-- The mark cut of an integrand is bounded by the integrand. -/
theorem abs_markCut_le {Ω : Type u} (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    |markCut A φ ω s e| ≤ |φ ω s e| := by
  by_cases h : e ∈ A
  · simp [markCut, h]
  · simp [markCut, h]
end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

/-- At a fixed time and coefficient state, the mixed drift integrand transports convergence of
the derivative state. -/
theorem tendsto_mixedDriftIntegrand_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u))
    (coeffs : JumpDiffusionCoeffs n d E) (s : ℝ) (x : Fin n → ℝ)
    (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => mixedDriftIntegrand u coeffs s (z m) x) atTop
      (𝓝 (mixedDriftIntegrand u coeffs s w x)) := by
  unfold mixedDriftIntegrand
  refine (tendsto_timeDeriv_of_tendsto hu s h).add (Tendsto.add ?_ (tendsto_const_nhds.mul ?_))
  · exact tendsto_finsetSum _ fun p _ =>
      tendsto_const_nhds.mul (tendsto_gradient_apply_of_tendsto hu s p h)
  · exact tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ =>
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (tendsto_hessian_of_tendsto hu s p q h)
/-- At a fixed time, coefficient state and mark, the mixed jump increment transports convergence
of the derivative state. -/
theorem tendsto_mixedJumpIncrement_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u))
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E)
    (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => mixedJumpIncrement u γ s (z m) x e) atTop
      (𝓝 (mixedJumpIncrement u γ s w x e)) := by
  unfold mixedJumpIncrement
  exact (SmallJump.tendsto_comp_of_tendsto hu s (h.add_const _)).sub
    (SmallJump.tendsto_comp_of_tendsto hu s h)
/-- At a fixed time, coefficient state and mark, the mixed compensator-drift integrand
transports convergence of the derivative state. -/
theorem tendsto_mixedCompensatorDriftIntegrand_of_tendsto
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ)
    (x : Fin n → ℝ) (e : E) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => mixedCompensatorDriftIntegrand u γ s (z m) x e) atTop
      (𝓝 (mixedCompensatorDriftIntegrand u γ s w x e)) := by
  unfold mixedCompensatorDriftIntegrand
  refine ((SmallJump.tendsto_comp_of_tendsto hu s (h.add_const _)).sub
    (SmallJump.tendsto_comp_of_tendsto hu s h)).sub ?_
  exact tendsto_finsetSum _ fun i _ =>
    tendsto_const_nhds.mul (tendsto_gradient_apply_of_tendsto hu s i h)
end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-- A finite sum of progressively measurable real processes is progressively measurable. -/
theorem progressivelyMeasurable_finset_sum {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {ι : Type*}
    (s : Finset ι) {H : ι → Ω → ℝ → ℝ} (h : ∀ i ∈ s, ProgressivelyMeasurable ℱ (H i)) :
    ProgressivelyMeasurable ℱ fun ω t => ∑ i ∈ s, H i ω t := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun r => ∑ i ∈ s, H i p.1 r) p.2)
      = fun p : Ω × ℝ => ∑ i ∈ s, (Set.Iic t).indicator (H i p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, Finset.sum_const_zero]
  rw [key]
  exact Finset.stronglyMeasurable_fun_sum
    (f := fun i (p : Ω × ℝ) => (Set.Iic t).indicator (H i p.1) p.2) s fun i hi => h i hi t
end Progressive

end LevyStochCalc.Ito.JumpFormula


