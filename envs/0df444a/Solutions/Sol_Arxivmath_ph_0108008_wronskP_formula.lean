-- Prove2me | solution 1 for Arxivmath_ph_0108008.wronskP_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:52:50.157806+00:00
-- url     : https://prove2.me/submissions/8145335e-145f-432a-a1ed-c05c1e09840d

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
theorem solution (r : ℝ) (hr : 0 < r) :
    wronskP r = 1 - (3 + 3 * Real.cos r ^ 2) / r ^ 2 + 3 * Real.sin (2 * r) / r ^ 3 :=
  formula r hr
