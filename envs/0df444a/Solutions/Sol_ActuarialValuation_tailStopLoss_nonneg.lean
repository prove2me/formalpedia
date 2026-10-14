-- Prove2me | solution 1 for ActuarialValuation.tailStopLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:22:50.252986+00:00
-- url     : https://prove2.me/submissions/bf5d5bfc-2c8e-4eb9-a3a0-768002c1bdc2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_tailStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (h : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    0 ≤ tailStopLoss p n t := by
  unfold tailStopLoss
  apply Finset.sum_nonneg
  intro k hk
  refine mul_nonneg ?_ (h k hk)
  first
  | (simp [tailExcess]; done)
  | (unfold tailExcess; positivity)
  | (simp only [tailExcess]; positivity)
  | (unfold tailExcess; simp; done)
