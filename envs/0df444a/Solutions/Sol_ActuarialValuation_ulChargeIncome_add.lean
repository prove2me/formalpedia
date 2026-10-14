-- Prove2me | solution 1 for ActuarialValuation.ulChargeIncome_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:21:12.913978+00:00
-- url     : https://prove2.me/submissions/821fb04c-48a7-47f6-8497-24f69b6653b5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulChargeIncome
open ActuarialValuation

theorem solution(a b c d : ℝ) : ulChargeIncome a b c d=a+b+c+d := by
  first
  | (simp [ulChargeIncome]; done)
  | (norm_num [ulChargeIncome]; done)
  | (unfold ulChargeIncome; positivity)
  | (simp only [ulChargeIncome]; positivity)
  | (unfold ulChargeIncome; ring)
  | (unfold ulChargeIncome; simp; done)
  | (unfold ulChargeIncome; norm_num; done)
  | (simp [ulChargeIncome]; ring)
  | (unfold ulChargeIncome; split_ifs <;> simp_all <;> linarith)
  | (unfold ulChargeIncome; nlinarith [sq_nonneg 0])
  | (simp_all [ulChargeIncome]; done)
  | (unfold ulChargeIncome; simp_all; done)
  | rfl
