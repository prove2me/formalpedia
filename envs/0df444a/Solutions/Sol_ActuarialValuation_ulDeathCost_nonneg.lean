-- Prove2me | solution 1 for ActuarialValuation.ulDeathCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:34:55.229111+00:00
-- url     : https://prove2.me/submissions/976534d4-dfeb-45e3-896f-0b1e27a0fbd6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathCost
open ActuarialValuation

theorem solution(q fund guarantee : ℝ) (hq : 0≤q) : 0≤ulDeathCost q fund guarantee := by
  first
  | (simp [ulDeathCost, ulNetAmountAtRisk]; done)
  | (norm_num [ulDeathCost, ulNetAmountAtRisk]; done)
  | (unfold ulDeathCost ulNetAmountAtRisk; positivity)
  | (simp only [ulDeathCost, ulNetAmountAtRisk]; positivity)
  | (unfold ulDeathCost ulNetAmountAtRisk; ring)
  | (unfold ulDeathCost ulNetAmountAtRisk; simp; done)
  | (unfold ulDeathCost ulNetAmountAtRisk; norm_num; done)
  | (simp [ulDeathCost, ulNetAmountAtRisk]; ring)
  | (unfold ulDeathCost ulNetAmountAtRisk; split_ifs <;> simp_all <;> linarith)
  | (unfold ulDeathCost ulNetAmountAtRisk; nlinarith [sq_nonneg 0])
  | (simp_all [ulDeathCost, ulNetAmountAtRisk]; done)
  | (unfold ulDeathCost ulNetAmountAtRisk; simp_all; done)
  | rfl
