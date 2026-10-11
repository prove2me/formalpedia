-- Prove2me | solution 1 for ActuarialValuation.tailLossMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:39:15.783793+00:00
-- url     : https://prove2.me/submissions/217e8e76-b481-4ad8-b1f7-7be7808401e6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailLossMean
open ActuarialValuation

theorem solution(p : ℕ → ℝ) : tailLossMean p 0 = 0 := by
  first
  | (simp [tailLossMean]; done)
  | (norm_num [tailLossMean]; done)
  | (unfold tailLossMean; positivity)
  | (simp only [tailLossMean]; positivity)
  | (unfold tailLossMean; ring)
  | (unfold tailLossMean; simp; done)
  | (unfold tailLossMean; norm_num; done)
  | (simp [tailLossMean]; ring)
  | (unfold tailLossMean; split_ifs <;> simp_all <;> linarith)
  | (unfold tailLossMean; nlinarith [sq_nonneg 0])
  | (simp_all [tailLossMean]; done)
  | (unfold tailLossMean; simp_all; done)
  | rfl
