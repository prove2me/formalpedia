-- Prove2me | Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
-- name    : LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:35:33.136867+00:00
-- url     : https://prove2.me/theorems/d90becc2-5e4c-4cdd-87d1-a9b140a556b2
-- title:
--   Source declarations: LevyStochCalc.Ito.FiniteActivityMixedPrelims
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.FiniteActivityMixedPrelims. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F001
import Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixedDictionary_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Preliminaries for the finite-activity Itô–Lévy identity in the mixed form

The small facts the finite-activity identity along a truncated path assembles from: the
left-limit jump sum of the mark-cut coefficient bundle is the prescribed-path jump sum along the
left limits; the left limit of the time-augmented path; the value of a progressively measurable
vector process at a stopping time is known at that time; the drift reconciliation for the mixed
integrands asked at almost every time only; and the bounds on the partial derivatives of the
time-augmented representative of a state function with bounded derivatives.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath`
* `LevyStochCalc.Ito.JumpFormula.leftLim_timeAugProcess_eq_cons`
* `LevyStochCalc.Ito.JumpFormula.measurable_stoppingTime_eval_untopA`
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae`
* `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv_timeAug_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv₂_timeAug_mul_le`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Probability LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section JumpSum

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

end JumpSum

section LeftLimit

variable {Ω : Type u} {n : ℕ}

end LeftLimit

section StoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}

end StoppingTime

section MixedAe

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end MixedAe

section MixedAssemblyAe

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : JumpDiffusionCoeffs n d E}

end MixedAssemblyAe

section TimeAugBounds

variable {Ω : Type u} {n d : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

/-- The time-augmented representative of a `C²` function of time and state is `C²`. -/
theorem contDiff_timeAugFun (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    ContDiff ℝ 2 (timeAugFun u) := by
  have hproj : ∀ i : Fin (n + 1), ContDiff ℝ 2 fun z : Fin (n + 1) → ℝ => z i :=
    fun i => contDiff_pi.mp contDiff_id i
  have h : timeAugFun u
      = Function.uncurry u ∘ fun z : Fin (n + 1) → ℝ => (z 0, fun q => z q.succ) := by
    funext z
    rfl
  rw [h]
  exact hu.comp ((hproj 0).prodMk (contDiff_pi.mpr fun q => hproj q.succ))
/-- The partial derivatives of the time-augmented representative are bounded by the larger of
the bounds on the time derivative and on the gradient. -/
theorem abs_coordDeriv_timeAug_le (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) {K₀ K₁ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀) (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (p : Fin (n + 1)) (z : Fin (n + 1) → ℝ) : |coordDeriv f' p z| ≤ max K₀ K₁ := by
  induction p using Fin.cases with
  | zero =>
    rw [coordDeriv_zero_eq_timeDeriv hfu hf]
    exact (hK₀ _ _).trans (le_max_left _ _)
  | succ q =>
    rw [coordDeriv_succ_eq_gradient hfu hf]
    exact (hK₁ _ _ _).trans (le_max_right _ _)
/-- Against the quadratic covariation density of the time-augmented diffusion, whose time row
vanishes, the second partial derivatives of the time-augmented representative are bounded by
the Hessian bound. -/
theorem abs_coordDeriv₂_timeAug_mul_le (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (p q : Fin (n + 1)) (z : Fin (n + 1) → ℝ) (ω : Ω) (s : ℝ) :
    |coordDeriv₂ f'' p q z|
        * |∑ k : Fin d, timeAugDiffusion H p k ω s * timeAugDiffusion H q k ω s|
      ≤ K₂ * |∑ k : Fin d, timeAugDiffusion H p k ω s * timeAugDiffusion H q k ω s| := by
  induction p using Fin.cases with
  | zero => simp [timeAugDiffusion]
  | succ p' =>
    induction q using Fin.cases with
    | zero => simp [timeAugDiffusion]
    | succ q' =>
      rw [coordDeriv₂_succ_succ_eq_hessian hfu hf hf']
      exact mul_le_mul_of_nonneg_right (hK₂ _ _ _ _) (abs_nonneg _)
/-- Adding a vector with a zero time coordinate to a time-consed vector adds the states. -/
theorem cons_add_cons_zero (s : ℝ) (x v : Fin n → ℝ) :
    (Fin.cons s x : Fin (n + 1) → ℝ) + Fin.cons 0 v = Fin.cons s (x + v) := by
  funext p
  refine Fin.cases ?_ ?_ p <;> simp
/-- The time-augmented representative at a time-consed state translated by a state. -/
theorem timeAugFun_cons_add_cons_zero (u : ℝ → (Fin n → ℝ) → ℝ) (s : ℝ) (x v : Fin n → ℝ) :
    timeAugFun u (Fin.cons s x + Fin.cons 0 v) = u s (x + v) := by
  rw [cons_add_cons_zero, timeAugFun_cons]
end TimeAugBounds

end LevyStochCalc.Ito.JumpFormula


