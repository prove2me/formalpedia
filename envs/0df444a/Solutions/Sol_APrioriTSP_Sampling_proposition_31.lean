-- Prove2me | solution 1 for APrioriTSP.Sampling.proposition_31
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T21:10:39.191601+00:00
-- url     : https://prove2.me/submissions/2b66ab68-2770-4d6c-b5b2-4374bc632218

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace Queelius.APrioriTSP

theorem log_ratio (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    x / y - x < Real.log (1 - x) / Real.log (1 - y) ∧
      Real.log (1 - x) / Real.log (1 - y) < x / y := by
  have hy0 : 0 < y := hx.trans hxy
  have hx1 : x < 1 := hxy.trans hy
  have ha : 0 < 1 - x := by linarith
  have hb : 0 < 1 - y := by linarith
  have hlnx : Real.log (1 - x) < 0 := Real.log_neg ha (by linarith)
  have hlny : Real.log (1 - y) < 0 := Real.log_neg hb (by linarith)
  have hlowx : x < -Real.log (1 - x) := by
    have hh := Real.log_lt_sub_one_of_pos ha (by linarith : 1 - x ≠ 1)
    linarith
  have hupy : -Real.log (1 - y) < y / (1 - y) := by
    have hh := Real.log_lt_sub_one_of_pos (inv_pos.mpr hb)
      (by intro he; have he' := (inv_eq_one.mp he); linarith : (1 - y)⁻¹ ≠ 1)
    rw [Real.log_inv] at hh
    convert hh using 1
    field_simp
    ring
  constructor
  · rw [show Real.log (1 - x) / Real.log (1 - y) =
        (-Real.log (1 - x)) / (-Real.log (1 - y)) by ring,
      lt_div_iff₀ (neg_pos.mpr hlny)]
    have hfac : 0 < x / y - x := by
      have : x < x / y := (lt_div_iff₀ hy0).2 (by nlinarith)
      linarith
    have hh := mul_lt_mul_of_pos_left hupy hfac
    have heq : (x / y - x) * (y / (1 - y)) = x := by field_simp <;> ring
    rw [heq] at hh
    exact hh.trans hlowx
  · have hc := strictConcaveOn_log_Ioi.secant_strict_mono
      (a := (1 : ℝ)) (x := 1 - y) (y := 1 - x)
      (by norm_num) hb ha (by linarith) (by linarith) (by linarith)
    simp only [Real.log_one, sub_zero, sub_sub_cancel_left] at hc
    rw [div_lt_iff_of_neg hlny]
    have hs : Real.log (1 - x) / (-x) < Real.log (1 - y) / (-y) := by
      simpa using hc
    have hm : Real.log (1 - y) * x < Real.log (1 - x) * y := by
      have he := mul_lt_mul_of_pos_left hs (mul_pos hx hy0)
      field_simp at he
      nlinarith
    apply (mul_lt_mul_iff_left₀ hy0).mp
    calc
      (x / y * Real.log (1 - y)) * y = Real.log (1 - y) * x := by field_simp <;> ring
      _ < Real.log (1 - x) * y := hm

end Queelius.APrioriTSP

open APrioriTSP.Sampling

/-- Proposition 31 (p. 30): for `0 < x < y < 1`,
`x/y − x < ln(1 − x)/ln(1 − y) < x/y`. -/
theorem solution (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    x / y - x < Real.log (1 - x) / Real.log (1 - y) ∧
      Real.log (1 - x) / Real.log (1 - y) < x / y := by
  exact Queelius.APrioriTSP.log_ratio x y hx hxy hy

