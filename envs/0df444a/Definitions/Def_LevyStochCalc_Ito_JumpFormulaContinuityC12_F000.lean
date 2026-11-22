-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000
-- name    : LevyStochCalc_Ito_JumpFormulaContinuityC12_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:33:15.319172+00:00
-- url     : https://prove2.me/theorems/3156640f-bb2f-4367-bbd7-4bb7e5a3c79a
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaContinuityC12
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaContinuityC12. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12Product_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_LocalDerivBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Derivative bounds for a `C^{1,2}` state function

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of class `C^{1,2}` the state section `u s` is `C²`, so
the mean value bounds of a jointly `C²` function of time and state hold verbatim: the increment
`u(s, y + v) − u(s, y)` is controlled by a coordinatewise bound on the gradient and the
first-order Taylor remainder `u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by a coordinatewise bound on
the Hessian. The mixed jump increment and the mixed compensator-drift integrand inherit those
bounds, and the joint continuity of the time derivative, the gradient and the Hessian bounds all
three by one constant on a compact time–space box.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.abs_sub_le_of_gradient_le_c12` — the increment bound
  `|u(s, y + v) − u(s, y)| ≤ n K₁ ‖v‖` for a `C^{1,2}` function.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le_c12` — the remainder bound
  `|u(s, y + v) − u(s, y) − vᵀ∇u(s, y)| ≤ n² K₂ ‖v‖²` for a `C^{1,2}` function.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le_c12`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedCompensatorDriftIntegrand_le_c12` — the bounds on the
  mixed jump increment and the mixed compensator-drift integrand of a `C^{1,2}` function.
* `LevyStochCalc.Ito.JumpFormula.exists_bound_on_box_c12` — on `[a, b] × closedBall 0 R` the time
  derivative, every gradient entry and every Hessian entry of a `C^{1,2}` function are bounded by
  one constant.
-/

namespace LevyStochCalc.Ito.JumpFormula

universe v

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

section Derivatives

/-- The state section of a `C^{1,2}` function of time and state is differentiable, with
derivative its Fréchet derivative. -/
theorem hasFDerivAt_state_section_c12 (hu : IsC12 u) (s : ℝ) (z : Fin n → ℝ) :
    HasFDerivAt (u s) (fderiv ℝ (u s) z) z :=
  ((hu.contDiff_section s).differentiable (by norm_num) z).hasFDerivAt
/-- The state derivative of a `C^{1,2}` function of time and state is differentiable, with
derivative the second Fréchet derivative. -/
theorem hasFDerivAt_fderiv_state_section_c12 (hu : IsC12 u) (s : ℝ) (z : Fin n → ℝ) :
    HasFDerivAt (fderiv ℝ (u s)) (fderiv ℝ (fderiv ℝ (u s)) z) z :=
  (((hu.contDiff_section s).fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) z).hasFDerivAt
/-- The Hessian of a `C^{1,2}` function is the second state derivative evaluated on the standard
basis, the direction of the outer differentiation first. -/
theorem hessian_eq_fderiv_fderiv_c12 (hu : IsC12 u) (s : ℝ) (z : Fin n → ℝ) (p q : Fin n) :
    hessian u s z p q = fderiv ℝ (fderiv ℝ (u s)) z (Pi.single q 1) (Pi.single p 1) := by
  have hap : HasFDerivAt (fun y : Fin n → ℝ => fderiv ℝ (u s) y (Pi.single p 1))
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single p 1 : Fin n → ℝ)).comp
        (fderiv ℝ (fderiv ℝ (u s)) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single p 1 : Fin n → ℝ)).hasFDerivAt.comp z
      (hasFDerivAt_fderiv_state_section_c12 hu s z)
  simp only [hessian, hap.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
end Derivatives

section GradientBound

/-- **Increment bound from a gradient bound.** A coordinatewise bound `K₁` on the gradient of a
`C^{1,2}` function of time and state bounds its state increments by `n K₁ ‖v‖`. -/
theorem abs_sub_le_of_gradient_le_c12 (hu : IsC12 u) {K₁ : ℝ} (s : ℝ)
    (hK : ∀ z i, |gradient u s z i| ≤ K₁) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y| ≤ (n : ℝ) * K₁ * ‖v‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := u s)
    (f' := fun z => fderiv ℝ (u s) z) (s := Set.univ) (C := (n : ℝ) * K₁)
    (fun z _ => (hasFDerivAt_state_section_c12 hu s z).hasFDerivWithinAt)
    (fun z _ => norm_fderiv_le_of_gradient_le s hK z) convex_univ (Set.mem_univ y)
    (Set.mem_univ (y + v))
  simpa [Real.norm_eq_abs] using h
end GradientBound

section HessianBound

/-- The operator norm of the second state derivative of a `C^{1,2}` function is at most `n²`
times a coordinatewise bound on the Hessian. -/
theorem norm_fderiv_fderiv_le_of_hessian_le_c12 (hu : IsC12 u) {K₂ : ℝ} (s : ℝ)
    (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (z : Fin n → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (u s)) z‖ ≤ (n : ℝ) ^ 2 * K₂ := by
  refine (_root_.Prove2MeSourceProof.h_487d91410cc5e15ee891c2c1 (fderiv ℝ (fderiv ℝ (u s)) z)).trans ?_
  calc ∑ p, ∑ q, |fderiv ℝ (fderiv ℝ (u s)) z (Pi.single p 1) (Pi.single q 1)|
      = ∑ p, ∑ q, |hessian u s z q p| := by simp only [hessian_eq_fderiv_fderiv_c12 hu s]
    _ ≤ ∑ _p : Fin n, ∑ _q : Fin n, K₂ :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hK z q p
    _ = (n : ℝ) ^ 2 * K₂ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
/-- The state derivative of a `C^{1,2}` function of time and state is Lipschitz with constant
`n²` times a coordinatewise bound on the Hessian. -/
theorem norm_fderiv_sub_le_of_hessian_le_c12 (hu : IsC12 u) {K₂ : ℝ} (s : ℝ)
    (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (z w : Fin n → ℝ) :
    ‖fderiv ℝ (u s) z - fderiv ℝ (u s) w‖ ≤ (n : ℝ) ^ 2 * K₂ * ‖z - w‖ :=
  norm_fderiv_sub_le (hasFDerivAt_fderiv_state_section_c12 hu s)
    (norm_fderiv_fderiv_le_of_hessian_le_c12 hu s hK) z w
/-- **First-order Taylor remainder bound from a Hessian bound.** A coordinatewise bound `K₂` on
the Hessian of a `C^{1,2}` function of time and state bounds the remainder
`u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by `n² K₂ ‖v‖²`. -/
theorem abs_sub_sub_le_of_hessian_le_c12 (hu : IsC12 u) {K₂ : ℝ} (s : ℝ)
    (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y - ∑ i, v i * gradient u s y i| ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by
  have hK0 : 0 ≤ (n : ℝ) ^ 2 * K₂ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · exact mul_nonneg (by positivity) ((abs_nonneg _).trans (hK y ⟨0, hn⟩ ⟨0, hn⟩))
  have hg : ∀ z ∈ Metric.closedBall y ‖v‖,
      HasFDerivWithinAt (fun z => u s z - fderiv ℝ (u s) y z)
        (fderiv ℝ (u s) z - fderiv ℝ (u s) y) (Metric.closedBall y ‖v‖) z :=
    fun z _ => ((hasFDerivAt_state_section_c12 hu s z).sub
      (fderiv ℝ (u s) y).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall y ‖v‖,
      ‖fderiv ℝ (u s) z - fderiv ℝ (u s) y‖ ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact (norm_fderiv_sub_le_of_hessian_le_c12 hu s hK z y).trans
      (mul_le_mul_of_nonneg_left hz hK0)
  have hmem : y + v ∈ Metric.closedBall y ‖v‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound
    (convex_closedBall y ‖v‖) (Metric.mem_closedBall_self (norm_nonneg v)) hmem
  have halg : u s (y + v) - fderiv ℝ (u s) y (y + v) - (u s y - fderiv ℝ (u s) y y)
      = u s (y + v) - u s y - ∑ i, v i * gradient u s y i := by
    rw [← fderiv_apply_eq_sum_gradient, map_add]
    ring
  rw [halg, Real.norm_eq_abs, add_sub_cancel_left] at hmvt
  calc |u s (y + v) - u s y - ∑ i, v i * gradient u s y i|
      ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ * ‖v‖ := hmvt
    _ = (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by ring
end HessianBound

section MixedBounds

variable {E : Type v}

/-- The mixed jump increment of a `C^{1,2}` function is bounded, through the gradient bound, by
`n K₁` times the sum of the absolute coordinates of the jump size. -/
theorem abs_mixedJumpIncrement_le_c12 (hu : IsC12 u)
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₁0 : 0 ≤ K₁) (s : ℝ) (y x : Fin n → ℝ)
    (e : E) : |mixedJumpIncrement u γ s y x e| ≤ (n : ℝ) * K₁ * ∑ i, |γ s x e i| := by
  unfold mixedJumpIncrement
  refine (abs_sub_le_of_gradient_le_c12 hu s (hK₁ s) y (γ s x e)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_le_sum_abs _) (mul_nonneg (Nat.cast_nonneg n) hK₁0)
/-- The mixed compensator-drift integrand of a `C^{1,2}` function is bounded, through the Hessian
bound, by `n³ K₂` times the sum of the squared coordinates of the jump size. -/
theorem abs_mixedCompensatorDriftIntegrand_le_c12 (hu : IsC12 u)
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (hK₂0 : 0 ≤ K₂) (s : ℝ) (y x : Fin n → ℝ)
    (e : E) :
    |mixedCompensatorDriftIntegrand u γ s y x e|
      ≤ (n : ℝ) ^ 2 * K₂ * ((n : ℝ) * ∑ i, γ s x e i ^ 2) := by
  unfold mixedCompensatorDriftIntegrand
  refine (abs_sub_sub_le_of_hessian_le_c12 hu s (hK₂ s) y (γ s x e)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sq_le_card_mul_sum_sq _)
    (mul_nonneg (sq_nonneg _) hK₂0)
end MixedBounds

section BoxBounds

/-- The sum of the absolute values of the gradient entries of a `C^{1,2}` function is
continuous. -/
theorem continuous_sum_abs_gradient_c12 (hu : IsC12 u) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, |gradient u p.1 p.2 i| :=
  continuous_finsetSum _ fun i _ => (hu.continuous_gradient i).abs
/-- The sum of the absolute values of the Hessian entries of a `C^{1,2}` function is
continuous. -/
theorem continuous_sum_abs_hessian_c12 (hu : IsC12 u) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, ∑ j : Fin n, |hessian u p.1 p.2 i j| :=
  continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (hu.continuous_hessian i j).abs
end BoxBounds

end LevyStochCalc.Ito.JumpFormula


