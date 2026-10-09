-- Prove2me | solution 1 for ActuarialValuation.nextStateMass_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:35:52.116696+00:00
-- url     : https://prove2.me/submissions/fa65f0be-b2de-4a90-b7a9-bcdaf6bb2bb4

import Mathlib
import Definitions.Def_actuarial_nextStateMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hP : ∀ i j, 0 ≤ P i j) (j : S)
  :
  0 ≤ nextStateMass μ P j := by
  classical
  change 0 ≤ ∑ i : S, μ i * P i j
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hμ i) (hP i j)
