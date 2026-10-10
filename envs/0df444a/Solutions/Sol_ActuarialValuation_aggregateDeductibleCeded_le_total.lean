-- Prove2me | solution 1 for ActuarialValuation.aggregateDeductibleCeded_le_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:58:06.024227+00:00
-- url     : https://prove2.me/submissions/7e0fc1a6-df44-4bd7-8a30-81bc47195061

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n d : ℕ) :
  aggregateDeductibleCeded x n d ≤ aggregateLossTotal x n := by
  change aggregateLossTotal x n - d ≤ aggregateLossTotal x n
  exact Nat.sub_le _ _
