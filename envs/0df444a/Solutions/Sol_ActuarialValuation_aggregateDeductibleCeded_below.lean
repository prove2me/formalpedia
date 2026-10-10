-- Prove2me | solution 1 for ActuarialValuation.aggregateDeductibleCeded_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:57:53.407097+00:00
-- url     : https://prove2.me/submissions/d5e839ff-2a5c-412d-b00d-829355d914b0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n d : ℕ)
  (h : aggregateLossTotal x n ≤ d) :
  aggregateDeductibleCeded x n d = 0 := by
  simp [aggregateDeductibleCeded, Nat.sub_eq_zero_of_le h]
