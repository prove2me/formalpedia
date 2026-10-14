-- Prove2me | solution 1 for ActuarialValuation.ulPremiumAlloc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:22:40.508578+00:00
-- url     : https://prove2.me/submissions/0ab867dc-8af3-41a3-8a2b-b46befea16e7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPremiumAlloc
open ActuarialValuation

theorem solution(premium rate : ℝ) (hp : 0 ≤ premium) (hr : 0 ≤ rate) : 0 ≤ ulPremiumAlloc premium rate := by
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
