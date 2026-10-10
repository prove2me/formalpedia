-- Prove2me | solution 1 for ActuarialValuation.perClaimDeductibleCeded_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:59:30.707554+00:00
-- url     : https://prove2.me/submissions/ac0a391a-260a-4294-b1c2-719ad2bcca93

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_perClaimDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n d : ℕ)
  (h : ∀ i ∈ Finset.range n, x i ≤ d) :
  perClaimDeductibleCeded x n d = 0 := by
  unfold perClaimDeductibleCeded
  apply Finset.sum_eq_zero
  intro i hi
  exact Nat.sub_eq_zero_of_le (h i hi)
