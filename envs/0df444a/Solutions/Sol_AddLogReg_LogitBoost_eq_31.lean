-- Prove2me | solution 1 for AddLogReg.LogitBoost.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:54.163976+00:00
-- url     : https://prove2.me/submissions/81842c26-c2f0-479e-87ff-34ea94038e55

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

open AddLogReg.LogitBoost

private lemma logistic_form (t : ℝ) :
    symLogistic t = Real.exp (2 * t) / (1 + Real.exp (2 * t)) := by
  unfold symLogistic
  have he : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [two_mul, Real.exp_add]
  have hi : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  have h3 := Real.exp_pos (2 * t)
  field_simp
  rw [show t * 2 = 2 * t by ring, he]
  nlinarith


theorem solution (b : Bool) (t : ℝ) :
    2 * ystar b * t - Real.log (1 + Real.exp (2 * t)) =
      ystar b * Real.log (symLogistic t) + (1 - ystar b) * Real.log (1 - symLogistic t) := by
  have hd : 0 < 1 + Real.exp (2 * t) := by positivity
  have hc : 1 - symLogistic t = 1 / (1 + Real.exp (2 * t)) := by
    rw [logistic_form]
    field_simp
    ring
  rw [hc, logistic_form, Real.log_div (Real.exp_ne_zero _) (ne_of_gt hd),
    Real.log_exp, Real.log_div one_ne_zero (ne_of_gt hd), Real.log_one]
  cases b <;> simp [ystar]

#print axioms solution
