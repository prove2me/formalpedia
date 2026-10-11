-- Prove2me | solution 1 for ActuarialValuation.irIndex_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:36.269225+00:00
-- url     : https://prove2.me/submissions/8d66f467-58cd-4913-bcd5-ef1d9760bf85

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irPriceIndex
open ActuarialValuation

theorem solution(base : ℝ) : irPriceIndex base 0=base := by
  first
  | (simp [irPriceIndex]; done)
  | (norm_num [irPriceIndex]; done)
  | (unfold irPriceIndex; positivity)
  | (simp only [irPriceIndex]; positivity)
  | (unfold irPriceIndex; ring)
  | (unfold irPriceIndex; simp; done)
  | (unfold irPriceIndex; norm_num; done)
  | (simp [irPriceIndex]; ring)
  | (unfold irPriceIndex; split_ifs <;> simp_all <;> linarith)
  | (unfold irPriceIndex; nlinarith [sq_nonneg 0])
  | (simp_all [irPriceIndex]; done)
  | (unfold irPriceIndex; simp_all; done)
  | rfl
