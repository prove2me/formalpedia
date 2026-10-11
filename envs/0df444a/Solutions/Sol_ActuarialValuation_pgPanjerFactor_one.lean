-- Prove2me | solution 1 for ActuarialValuation.pgPanjerFactor_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:53:59.148653+00:00
-- url     : https://prove2.me/submissions/e049d1e1-d16f-4855-be09-c6cb233e1f12

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerFactor
open ActuarialValuation

theorem solution(a b : ℝ) : pgPanjerFactor a b 1=a+b := by
  first
  | (simp [pgPanjerFactor]; done)
  | (norm_num [pgPanjerFactor]; done)
  | (unfold pgPanjerFactor; positivity)
  | (simp only [pgPanjerFactor]; positivity)
  | (unfold pgPanjerFactor; ring)
  | (unfold pgPanjerFactor; simp; done)
  | (unfold pgPanjerFactor; norm_num; done)
  | (simp [pgPanjerFactor]; ring)
  | (unfold pgPanjerFactor; split_ifs <;> simp_all <;> linarith)
  | (unfold pgPanjerFactor; nlinarith [sq_nonneg 0])
  | (simp_all [pgPanjerFactor]; done)
  | (unfold pgPanjerFactor; simp_all; done)
  | rfl
