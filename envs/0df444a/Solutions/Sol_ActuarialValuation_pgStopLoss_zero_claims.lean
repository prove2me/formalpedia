-- Prove2me | solution 1 for ActuarialValuation.pgStopLoss_zero_claims
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T18:00:01.220995+00:00
-- url     : https://prove2.me/submissions/ff802d58-d535-4425-a523-77535dd63a01

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (m k : ℕ) :
    pgStopLoss p f m k 0 =
      ∑ j ∈ Finset.range (k+1), pgAggregate p f m j * (j:ℝ) := by
  unfold pgStopLoss
  apply Finset.sum_congr rfl
  intro j hj
  have hnonneg : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  simp [hnonneg]
