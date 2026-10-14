-- Prove2me | solution 1 for ActuarialValuation.bdCouponPV_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:58.640748+00:00
-- url     : https://prove2.me/submissions/1f4eee40-822c-44e7-bdaf-8e4d70a4885a

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdCouponPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D c : ℕ → ℝ) (n : ℕ) (a : ℝ) : bdCouponPV D (fun k => a*c k) n = a*bdCouponPV D c n := by
  unfold bdCouponPV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
