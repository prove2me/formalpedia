-- Prove2me | solution 1 for ActuarialValuation.perClaimDeductibleCeded_le_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:06:36.964767+00:00
-- url     : https://prove2.me/submissions/e0dd2a23-8ea8-4ade-baa7-aa2b14aaa835

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_perClaimDeductibleCeded
import Definitions.Def_actuarial_aggregateLossTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n d : ℕ) :
  perClaimDeductibleCeded x n d ≤ aggregateLossTotal x n := by
  unfold perClaimDeductibleCeded aggregateLossTotal
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.sub_le (x i) d
