-- Prove2me | solution 1 for ActuarialValuation.perClaimDeductibleCeded_le_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:06:54.204199+00:00
-- url     : https://prove2.me/submissions/0a04836c-b864-48b8-aa72-760b3d7dc8da

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_actuarial_aggregateDeductibleCeded
import Definitions.Def_actuarial_perClaimDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n d : ℕ) :
  perClaimDeductibleCeded x n d ≤ aggregateDeductibleCeded x n d := by
  induction n with
  | zero =>
      simp [perClaimDeductibleCeded, aggregateDeductibleCeded, aggregateLossTotal]
  | succ n ih =>
      change (∑ i ∈ Finset.range (n + 1), (x i - d)) ≤
        (∑ i ∈ Finset.range (n + 1), x i) - d
      simp only [Finset.sum_range_succ]
      have hprev : (∑ i ∈ Finset.range n, (x i - d)) ≤
          (∑ i ∈ Finset.range n, x i) - d := ih
      omega
