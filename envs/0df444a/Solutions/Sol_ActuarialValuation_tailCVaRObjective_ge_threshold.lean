-- Prove2me | solution 1 for ActuarialValuation.tailCVaRObjective_ge_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:44:15.900261+00:00
-- url     : https://prove2.me/submissions/f4cd4e2b-6fae-4895-a98c-e180ffb2d2dd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_actuarial_tailCVaRObjective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (a t : ℝ) (ha : a < 1)
    (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    t ≤ tailCVaRObjective p n a t := by
  unfold tailCVaRObjective
  have hSL : 0 ≤ tailStopLoss p n t := by
    unfold tailStopLoss
    apply Finset.sum_nonneg
    intro k hk
    refine mul_nonneg ?_ (hp k hk)
    first
    | (simp [tailExcess]; done)
    | (unfold tailExcess; positivity)
    | (simp only [tailExcess]; positivity)
    | (unfold tailExcess; simp; done)
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hdiv : (0 : ℝ) ≤ tailStopLoss p n t / (1 - a) := div_nonneg hSL h1a.le
  linarith
