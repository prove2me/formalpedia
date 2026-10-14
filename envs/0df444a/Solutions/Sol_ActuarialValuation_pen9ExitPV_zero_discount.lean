-- Prove2me | solution 1 for ActuarialValuation.pen9ExitPV_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:23:14.664371+00:00
-- url     : https://prove2.me/submissions/73b538e7-78fd-4dd6-a73d-11debab2ccd6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitPV
open ActuarialValuation

theorem solution(w d i r bw bd bi br : ℝ) : pen9ExitPV 0 w d i r bw bd bi br = 0 := by
  first
  | (simp [pen9ExitPV]; done)
  | (norm_num [pen9ExitPV]; done)
  | (unfold pen9ExitPV; positivity)
  | (simp only [pen9ExitPV]; positivity)
  | (unfold pen9ExitPV; ring)
  | (unfold pen9ExitPV; simp; done)
  | (unfold pen9ExitPV; norm_num; done)
  | (simp [pen9ExitPV]; ring)
  | (unfold pen9ExitPV; split_ifs <;> simp_all <;> linarith)
  | (unfold pen9ExitPV; nlinarith [sq_nonneg 0])
  | (simp_all [pen9ExitPV]; done)
  | (unfold pen9ExitPV; simp_all; done)
  | rfl
