-- Prove2me | solution 1 for ActuarialValuation.pgPanjerLHS_no_a
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:40:41.491021+00:00
-- url     : https://prove2.me/submissions/8d40aaa8-0692-432b-a254-1d49cfc3afaa

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerLHS
open ActuarialValuation

theorem solution(f0 g : ℝ) : pgPanjerLHS 0 f0 g=g := by
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
