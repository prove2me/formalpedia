-- Prove2me | solution 1 for ActuarialValuation.ulNetAmountAtRisk_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:09:16.237979+00:00
-- url     : https://prove2.me/submissions/e6da9c60-9c45-4828-8c3f-950a36987af0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulNetAmountAtRisk
open ActuarialValuation

theorem solution(fund guarantee : ℝ) : 0≤ulNetAmountAtRisk fund guarantee := by
  first
  | (simp [ulNetAmountAtRisk]; done)
  | (norm_num [ulNetAmountAtRisk]; done)
  | (unfold ulNetAmountAtRisk; positivity)
  | (simp only [ulNetAmountAtRisk]; positivity)
  | (unfold ulNetAmountAtRisk; ring)
  | (unfold ulNetAmountAtRisk; simp; done)
  | (unfold ulNetAmountAtRisk; norm_num; done)
  | (simp [ulNetAmountAtRisk]; ring)
  | (unfold ulNetAmountAtRisk; split_ifs <;> simp_all <;> linarith)
  | (unfold ulNetAmountAtRisk; nlinarith [sq_nonneg 0])
  | (simp_all [ulNetAmountAtRisk]; done)
  | (unfold ulNetAmountAtRisk; simp_all; done)
  | rfl
