-- Prove2me | solution 1 for ActuarialValuation.whFitPenalty_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:34:19.858678+00:00
-- url     : https://prove2.me/submissions/e56cb2a7-9d4f-4f31-9abd-befe6bd7300e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_whFitPenalty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w g q : ℕ → ℝ) (n : ℕ) (hw : ∀ i ∈ Finset.range n, 0 ≤ w i) : 0 ≤ whFitPenalty w g q n := by
  unfold whFitPenalty
  apply Finset.sum_nonneg
  intro i hi
  dsimp [whWeightedFit]
  exact mul_nonneg (hw i hi) (sq_nonneg _)
