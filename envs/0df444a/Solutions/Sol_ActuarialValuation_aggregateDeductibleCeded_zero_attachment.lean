-- Prove2me | solution 1 for ActuarialValuation.aggregateDeductibleCeded_zero_attachment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:58:11.679516+00:00
-- url     : https://prove2.me/submissions/3f922796-9904-4274-8b2a-7592c41ee58e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n : ℕ) :
  aggregateDeductibleCeded x n 0 = aggregateLossTotal x n := by
  simp [aggregateDeductibleCeded]
