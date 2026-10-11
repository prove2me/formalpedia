-- Prove2me | solution 1 for ActuarialValuation.pgPanjerLHS_zero_f0
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:26:12.808813+00:00
-- url     : https://prove2.me/submissions/be1477c1-27fb-4711-9a12-648eb978136f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerLHS
open ActuarialValuation

theorem solution(a g : ℝ) : pgPanjerLHS a 0 g=g := by
  first
  | (simp [pgPanjerLHS]; done)
  | (norm_num [pgPanjerLHS]; done)
  | (unfold pgPanjerLHS; positivity)
  | (simp only [pgPanjerLHS]; positivity)
  | (unfold pgPanjerLHS; ring)
  | (unfold pgPanjerLHS; simp; done)
  | (unfold pgPanjerLHS; norm_num; done)
  | (simp [pgPanjerLHS]; ring)
  | (unfold pgPanjerLHS; split_ifs <;> simp_all <;> linarith)
  | (unfold pgPanjerLHS; nlinarith [sq_nonneg 0])
  | (simp_all [pgPanjerLHS]; done)
  | (unfold pgPanjerLHS; simp_all; done)
  | rfl
