-- Prove2me | solution 1 for ActuarialValuation.pgPanjerFactor_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:49:10.492661+00:00
-- url     : https://prove2.me/submissions/681f4b78-f9ad-462e-ab92-0911eb036664

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerFactor
open ActuarialValuation

theorem solution(a b : ℝ) : pgPanjerFactor a b 2=a+b/2 := by
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
