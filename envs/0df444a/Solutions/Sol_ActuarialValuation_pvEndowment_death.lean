-- Prove2me | solution 1 for ActuarialValuation.pvEndowment_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:57:08.710279+00:00
-- url     : https://prove2.me/submissions/8500b30a-84fc-434e-bbaf-d8b48f787783

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvEndowmentBenefit
open ActuarialValuation

theorem solution(death maturityDiscount : ℝ) : pvEndowmentBenefit death maturityDiscount True = death := by
  first
  | (simp [pvEndowmentBenefit]; done)
  | (norm_num [pvEndowmentBenefit]; done)
  | (unfold pvEndowmentBenefit; positivity)
  | (simp only [pvEndowmentBenefit]; positivity)
  | (unfold pvEndowmentBenefit; ring)
  | (unfold pvEndowmentBenefit; simp; done)
  | (unfold pvEndowmentBenefit; norm_num; done)
  | (simp [pvEndowmentBenefit]; ring)
  | (unfold pvEndowmentBenefit; split_ifs <;> simp_all <;> linarith)
  | (unfold pvEndowmentBenefit; nlinarith [sq_nonneg 0])
  | (simp_all [pvEndowmentBenefit]; done)
  | (unfold pvEndowmentBenefit; simp_all; done)
  | rfl
