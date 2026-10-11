-- Prove2me | solution 1 for ActuarialValuation.ruStopLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:42.411007+00:00
-- url     : https://prove2.me/submissions/4493f0ee-acc4-48f0-bf42-1302c2230089

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruStopLoss
open ActuarialValuation

theorem solution(x d : ℝ) : 0 ≤ ruStopLoss x d := by
  first
  | (simp [ruStopLoss]; done)
  | (norm_num [ruStopLoss]; done)
  | (unfold ruStopLoss; positivity)
  | (simp only [ruStopLoss]; positivity)
  | (unfold ruStopLoss; ring)
  | (unfold ruStopLoss; simp; done)
  | (unfold ruStopLoss; norm_num; done)
  | (simp [ruStopLoss]; ring)
  | (unfold ruStopLoss; split_ifs <;> simp_all <;> linarith)
  | (unfold ruStopLoss; nlinarith [sq_nonneg 0])
  | (simp_all [ruStopLoss]; done)
  | (unfold ruStopLoss; simp_all; done)
  | rfl
