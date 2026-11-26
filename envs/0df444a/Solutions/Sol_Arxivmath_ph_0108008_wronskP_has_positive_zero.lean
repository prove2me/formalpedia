-- Prove2me | solution 1 for Arxivmath_ph_0108008.wronskP_has_positive_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:53:29.640859+00:00
-- url     : https://prove2.me/submissions/0c45407b-4d57-4ae2-8cad-2c828d16be36

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

set_option autoImplicit false

open Real

namespace S73WP
open Arxivmath_ph_0108008

lemma formula (r : ℝ) (hr : 0 < r) :
    wronskP r = 1 - (3 + 3 * Real.cos r ^ 2) / r ^ 2 + 3 * Real.sin (2 * r) / r ^ 3 := by
  have hr0 : r ≠ 0 := hr.ne'
  have h1 := ((((hasDerivAt_const r (3:ℝ)).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr0)).sub
    (hasDerivAt_const r (1:ℝ))).mul (Real.hasDerivAt_sin r)).sub
    (((hasDerivAt_const r (3:ℝ)).div (hasDerivAt_id' r) hr0).mul (Real.hasDerivAt_cos r))
  have hd : deriv riccatiU2 r = ((0 * r ^ 2 - 3 * (↑2 * r ^ (2 - 1))) / (r ^ 2) ^ 2 - 0) * Real.sin r +
      (3 / r ^ 2 - 1) * Real.cos r -
      ((0 * r - 3 * 1) / r ^ 2 * Real.cos r + 3 / r * -Real.sin r) := h1.deriv
  have hc : deriv (fun x => -Real.cos x) r = Real.sin r := by
    have := (Real.hasDerivAt_cos r).neg
    exact this.deriv.trans (neg_neg _)
  unfold wronskP
  rw [hd, hc]
  unfold riccatiU2
  rw [Real.sin_two_mul]
  field_simp
  have := Real.sin_sq_add_cos_sq r
  push_cast
  linear_combination (-3 * r ^ 2 + r ^ 4) * this

end S73WP

open Arxivmath_ph_0108008 S73WP in
theorem solution : ∃ R : ℝ, 0 < R ∧ wronskP R = 0 := by
  set F : ℝ → ℝ := fun r => 1 - (3 + 3 * Real.cos r ^ 2) / r ^ 2 + 3 * Real.sin (2 * r) / r ^ 3
  have hp := Real.pi_pos
  have hpi1 := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have hab : Real.pi / 2 ≤ Real.pi := by linarith
  have hcont : ContinuousOn F (Set.Icc (Real.pi / 2) Real.pi) := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    apply ContinuousAt.continuousWithinAt
    simp only [F]
    fun_prop (disch := exact pow_ne_zero _ hx0)
  have ha : F (Real.pi / 2) = 1 - 12 / Real.pi ^ 2 := by
    simp only [F]
    rw [Real.cos_pi_div_two, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    field_simp; ring
  have hb : F Real.pi = 1 - 6 / Real.pi ^ 2 := by
    simp only [F]
    rw [Real.cos_pi, Real.sin_two_mul, Real.sin_pi]
    field_simp; ring
  have ha' : F (Real.pi / 2) ≤ 0 := by
    rw [ha, sub_nonpos, le_div_iff₀ (by positivity)]; nlinarith
  have hb' : 0 ≤ F Real.pi := by
    rw [hb, sub_nonneg, div_le_one (by positivity)]; nlinarith
  obtain ⟨R, hR, hFR⟩ := intermediate_value_Icc hab hcont ⟨ha', hb'⟩
  have hR0 : 0 < R := by linarith [hR.1]
  exact ⟨R, hR0, by rw [formula R hR0]; exact hFR⟩
