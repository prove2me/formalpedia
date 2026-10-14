-- Prove2me | solution 1 for ActuarialValuation.ulCharge_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:09:39.273862+00:00
-- url     : https://prove2.me/submissions/28bebfbb-27a0-431b-a167-e81dec763929

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCharge
open ActuarialValuation

theorem solution(fund rate : ℝ) (hf : 0≤fund) (hr : 0≤rate) : 0≤ulCharge fund rate := by
  first
  | (simp [ulCharge]; done)
  | (norm_num [ulCharge]; done)
  | (unfold ulCharge; positivity)
  | (simp only [ulCharge]; positivity)
  | (unfold ulCharge; ring)
  | (unfold ulCharge; simp; done)
  | (unfold ulCharge; norm_num; done)
  | (simp [ulCharge]; ring)
  | (unfold ulCharge; split_ifs <;> simp_all <;> linarith)
  | (unfold ulCharge; nlinarith [sq_nonneg 0])
  | (simp_all [ulCharge]; done)
  | (unfold ulCharge; simp_all; done)
  | rfl
