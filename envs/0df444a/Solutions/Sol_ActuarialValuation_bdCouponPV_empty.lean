-- Prove2me | solution 1 for ActuarialValuation.bdCouponPV_empty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:19:28.735988+00:00
-- url     : https://prove2.me/submissions/7e67a9d0-2112-4f0f-952d-84f6516bcf1d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdCouponPV
open ActuarialValuation

theorem solution(D c : ℕ → ℝ) : bdCouponPV D c 0 = 0 := by
  first
  | (simp [bdCouponPV]; done)
  | (norm_num [bdCouponPV]; done)
  | (unfold bdCouponPV; positivity)
  | (simp only [bdCouponPV]; positivity)
  | (unfold bdCouponPV; ring)
  | (unfold bdCouponPV; simp; done)
  | (unfold bdCouponPV; norm_num; done)
  | (simp [bdCouponPV]; ring)
  | (unfold bdCouponPV; split_ifs <;> simp_all <;> linarith)
  | (unfold bdCouponPV; nlinarith [sq_nonneg 0])
  | (simp_all [bdCouponPV]; done)
  | (unfold bdCouponPV; simp_all; done)
  | rfl
