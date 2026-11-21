-- Prove2me | Definitions.Def_SourceProof_d7551ffa72e4a3e8bbb658cc
-- name    : SourceProof_d7551ffa72e4a3e8bbb658cc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:27.206465+00:00
-- url     : https://prove2.me/theorems/335d2f91-b572-4dea-975e-e3b1b985cff0
-- title:
--   LevyStochCalc source module: SourceProof_d7551ffa72e4a3e8bbb658cc
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le` comes from the `LevyStochCalc.Ito.JumpFormulaTaylorBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Taylor bounds for the state increments of a `C²` function

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state that is `C²` jointly, the increment
`u(s, y + v) − u(s, y)` at a fixed time is controlled by a bound on the gradient, and the
first-order Taylor remainder `u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by a bound on the Hessian.
Both are mean value bounds: the first for `u(s, ·)` on the whole state space, the second for
`z ↦ u(s, z) − ∇u(s, y)ᵀ z` on the ball of radius `‖v‖` about `y`, where its derivative
`∇u(s, z) − ∇u(s, y)` is at most the Lipschitz constant of the gradient times `‖v‖`.

The hypotheses are the coordinatewise bounds on `gradient` and `hessian`, and the state space
carries the supremum norm, so the constants pick up the dimension: the operator norm of a
functional on `Fin n → ℝ` is at most the sum of its `n` coordinates, and that of a bilinear form
at most the sum of its `n²` coordinates.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.fderiv_apply_eq_sum_gradient` — the state derivative applied to
  a vector is the coordinate pairing with the gradient.
* `LevyStochCalc.Ito.JumpFormula.hessian_eq_fderiv_fderiv` — the Hessian is the second state
  derivative on the standard basis.
* `LevyStochCalc.Ito.JumpFormula.norm_fderiv_le_of_gradient_le`,
  `LevyStochCalc.Ito.JumpFormula.norm_fderiv_fderiv_le_of_hessian_le` — operator norm bounds on
  the first and second state derivatives from the coordinatewise bounds.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_le_of_gradient_le` — the increment bound
  `|u(s, y + v) − u(s, y)| ≤ n K₁ ‖v‖`.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le` — the remainder bound
  `|u(s, y + v) − u(s, y) − vᵀ∇u(s, y)| ≤ n² K₂ ‖v‖²`.
-/

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

section Derivatives

end Derivatives

section GradientBound

end GradientBound

section HessianBound


theorem _root_.Prove2MeSourceProof.h_d7551ffa72e4a3e8bbb658cc (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₂ : ℝ}
    (s : ℝ) (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y - ∑ i, v i * gradient u s y i| ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by
  have hK0 : 0 ≤ (n : ℝ) ^ 2 * K₂ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · exact mul_nonneg (by positivity) ((abs_nonneg _).trans (hK y ⟨0, hn⟩ ⟨0, hn⟩))
  have hg : ∀ z ∈ Metric.closedBall y ‖v‖,
      HasFDerivWithinAt (fun z => u s z - fderiv ℝ (u s) y z)
        (fderiv ℝ (u s) z - fderiv ℝ (u s) y) (Metric.closedBall y ‖v‖) z :=
    fun z _ => ((LevyStochCalc.Ito.JumpFormula.hasFDerivAt_state_section hu s z).sub
      (fderiv ℝ (u s) y).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall y ‖v‖,
      ‖fderiv ℝ (u s) z - fderiv ℝ (u s) y‖ ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact (LevyStochCalc.Ito.JumpFormula.norm_fderiv_sub_le_of_hessian_le hu s hK z y).trans
      (mul_le_mul_of_nonneg_left hz hK0)
  have hmem : y + v ∈ Metric.closedBall y ‖v‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound
    (convex_closedBall y ‖v‖) (Metric.mem_closedBall_self (norm_nonneg v)) hmem
  have halg : u s (y + v) - fderiv ℝ (u s) y (y + v) - (u s y - fderiv ℝ (u s) y y)
      = u s (y + v) - u s y - ∑ i, v i * LevyStochCalc.Ito.JumpFormula.gradient u s y i := by
    rw [← LevyStochCalc.Ito.JumpFormula.fderiv_apply_eq_sum_gradient, map_add]
    ring
  rw [halg, Real.norm_eq_abs, add_sub_cancel_left] at hmvt
  calc |u s (y + v) - u s y - ∑ i, v i * LevyStochCalc.Ito.JumpFormula.gradient u s y i|
      ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ * ‖v‖ := hmvt
    _ = (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by ring
end HessianBound

end LevyStochCalc.Ito.JumpFormula


