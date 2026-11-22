-- Prove2me | Definitions.Def_SourceProof_95728902748714b8e25fb455
-- name    : SourceProof_95728902748714b8e25fb455
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:39:44.301827+00:00
-- url     : https://prove2.me/theorems/0bb923d1-ccf7-4dc9-8850-713a9f7d8959
-- title:
--   LevyStochCalc source module: SourceProof_95728902748714b8e25fb455
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.exists_bound_on_box_c12` comes from the `LevyStochCalc.Ito.JumpFormulaContinuityC12` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000

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

end Derivatives

section GradientBound

end GradientBound

section HessianBound

end HessianBound

section MixedBounds

variable {E : Type v}

end MixedBounds

section BoxBounds


theorem _root_.Prove2MeSourceProof.h_95728902748714b8e25fb455 (hu : IsC12 u) (a b R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → |timeDeriv u s x| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i, |gradient u s x i| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i j, |hessian u s x i j| ≤ K) := by
  classical
  set B : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc a b ×ˢ Metric.closedBall (0 : Fin n → ℝ) R with hBdef
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M₀, hM₀⟩ := hBc.exists_bound_of_continuousOn hu.continuous_timeDeriv.continuousOn
  obtain ⟨M₁, hM₁⟩ :=
    hBc.exists_bound_of_continuousOn (LevyStochCalc.Ito.JumpFormula.continuous_sum_abs_gradient_c12 hu).continuousOn
  obtain ⟨M₂, hM₂⟩ :=
    hBc.exists_bound_of_continuousOn (LevyStochCalc.Ito.JumpFormula.continuous_sum_abs_hessian_c12 hu).continuousOn
  refine ⟨max 0 (max M₀ (max M₁ M₂)), le_max_left _ _, ?_, ?_, ?_⟩
  · intro s x hs hx
    have hmem : (s, x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have := hM₀ (s, x) hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro s x hs hx i
    have hmem : (s, x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have hsum := hM₁ (s, x) hmem
    rw [Real.norm_eq_abs] at hsum
    have hle : |LevyStochCalc.Ito.JumpFormula.gradient u s x i| ≤ ∑ k : Fin n, |LevyStochCalc.Ito.JumpFormula.gradient u s x k| :=
      Finset.single_le_sum (f := fun k : Fin n => |LevyStochCalc.Ito.JumpFormula.gradient u s x k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    refine hle.trans (le_trans (le_abs_self _) (hsum.trans ?_))
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · intro s x hs hx i j
    have hmem : (s, x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have hsum := hM₂ (s, x) hmem
    rw [Real.norm_eq_abs] at hsum
    have hle1 : |LevyStochCalc.Ito.JumpFormula.hessian u s x i j| ≤ ∑ l : Fin n, |LevyStochCalc.Ito.JumpFormula.hessian u s x i l| :=
      Finset.single_le_sum (f := fun l : Fin n => |LevyStochCalc.Ito.JumpFormula.hessian u s x i l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ j)
    have hle2 : (∑ l : Fin n, |LevyStochCalc.Ito.JumpFormula.hessian u s x i l|)
        ≤ ∑ k : Fin n, ∑ l : Fin n, |LevyStochCalc.Ito.JumpFormula.hessian u s x k l| :=
      Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, |LevyStochCalc.Ito.JumpFormula.hessian u s x k l|)
        (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i)
    refine (hle1.trans hle2).trans (le_trans (le_abs_self _) (hsum.trans ?_))
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
end BoxBounds

end LevyStochCalc.Ito.JumpFormula


