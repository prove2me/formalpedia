-- Prove2me | solution 1 for ActuarialValuation.ulPremiumAlloc_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:56:38.324101+00:00
-- url     : https://prove2.me/submissions/3e3467aa-4431-44a7-a7fe-5454b9fbf761

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPremiumAlloc
open ActuarialValuation

theorem solution(rate : ℝ) : ulPremiumAlloc 0 rate=0 := by
  first
  | (simp [ulPremiumAlloc]; done)
  | (norm_num [ulPremiumAlloc]; done)
  | (unfold ulPremiumAlloc; positivity)
  | (simp only [ulPremiumAlloc]; positivity)
  | (unfold ulPremiumAlloc; ring)
  | (unfold ulPremiumAlloc; simp; done)
  | (unfold ulPremiumAlloc; norm_num; done)
  | (simp [ulPremiumAlloc]; ring)
  | (unfold ulPremiumAlloc; split_ifs <;> simp_all <;> linarith)
  | (unfold ulPremiumAlloc; nlinarith [sq_nonneg 0])
  | (simp_all [ulPremiumAlloc]; done)
  | (unfold ulPremiumAlloc; simp_all; done)
  | rfl
