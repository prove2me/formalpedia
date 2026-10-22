-- Prove2me | solution 1 for AccelVI.AVC.eq_5_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:27.148794+00:00
-- url     : https://prove2.me/submissions/9b6b5c09-8add-4c75-bb7d-11810aa9c89c

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

set_option autoImplicit false
open AccelVI.AVC

theorem solution (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    lam = theta lam + Real.sqrt (1 - lam) * (1 - Real.sqrt (1 - lam ^ 2)) / Real.sqrt (1 + lam) ∧
    0 < Real.sqrt (1 - lam) * (1 - Real.sqrt (1 - lam ^ 2)) := by
  have hm : 0 < 1 - lam := by linarith
  have hp : 0 < 1 + lam := by linarith
  have ha : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr hm
  have hb : 0 < Real.sqrt (1 + lam) := Real.sqrt_pos.mpr hp
  have ha2 : Real.sqrt (1 - lam) ^ 2 = 1 - lam := Real.sq_sqrt hm.le
  have hb2 : Real.sqrt (1 + lam) ^ 2 = 1 + lam := Real.sq_sqrt hp.le
  have hsq : Real.sqrt (1 - lam ^ 2) = Real.sqrt (1 - lam) * Real.sqrt (1 + lam) := by
    rw [← Real.sqrt_mul hm.le]; congr 1; ring
  have hth : theta lam = 1 - Real.sqrt (1 - lam) / Real.sqrt (1 + lam) := by
    unfold theta kappa
    rw [one_div_div, Real.sqrt_div hm.le]
  constructor
  · rw [hth, hsq]
    field_simp
    nlinarith [ha2, hb2]
  · apply mul_pos ha
    have : Real.sqrt (1 - lam ^ 2) < 1 := by
      rw [Real.sqrt_lt' one_pos]; nlinarith
    linarith
