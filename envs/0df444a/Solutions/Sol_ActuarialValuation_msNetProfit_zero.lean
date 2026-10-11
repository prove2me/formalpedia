-- Prove2me | solution 1 for ActuarialValuation.msNetProfit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:45.464889+00:00
-- url     : https://prove2.me/submissions/3aa4b532-544f-4c1f-82a9-be78dc8ec4b2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msNetProfit
open ActuarialValuation

theorem solution(p : ℝ) : msNetProfit p 0 0 = p := by
  first
  | (simp [msNetProfit]; done)
  | (norm_num [msNetProfit]; done)
  | (unfold msNetProfit; positivity)
  | (simp only [msNetProfit]; positivity)
  | (unfold msNetProfit; ring)
  | (unfold msNetProfit; simp; done)
  | (unfold msNetProfit; norm_num; done)
  | (simp [msNetProfit]; ring)
  | (unfold msNetProfit; split_ifs <;> simp_all <;> linarith)
  | (unfold msNetProfit; nlinarith [sq_nonneg 0])
  | (simp_all [msNetProfit]; done)
  | (unfold msNetProfit; simp_all; done)
  | rfl
