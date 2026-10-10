-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityImmediate_eq_discount_due
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:46.073168+00:00
-- url     : https://prove2.me/submissions/352d9e6e-35d8-481a-9f9b-1f8eccb95e9e

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1AnnuityDue
import Definitions.Def_actuarial_cm1AnnuityImmediate
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) : cm1AnnuityImmediate i n = cm1Discount i 1 * cm1AnnuityDue i n := by
  unfold cm1AnnuityImmediate cm1AnnuityDue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [cm1Discount, cm1Accum, pow_succ, one_div, mul_inv_rev, mul_comm]
