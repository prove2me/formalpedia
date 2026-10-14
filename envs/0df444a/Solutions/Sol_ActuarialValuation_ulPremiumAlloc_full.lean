-- Prove2me | solution 1 for ActuarialValuation.ulPremiumAlloc_full
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:24:13.382235+00:00
-- url     : https://prove2.me/submissions/676c3d33-082e-4fee-bf33-72275e869a0b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPremiumAlloc
open ActuarialValuation

theorem solution(premium : ℝ) : ulPremiumAlloc premium 1=premium := by
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
