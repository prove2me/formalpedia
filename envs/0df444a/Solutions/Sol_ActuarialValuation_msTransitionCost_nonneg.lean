-- Prove2me | solution 1 for ActuarialValuation.msTransitionCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:18:23.219362+00:00
-- url     : https://prove2.me/submissions/c9748a75-c4de-4efd-90e9-ba15e4aa26ac

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTransitionCost

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (T : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ) (v : ℝ) (i : Fin 3) (hT : ∀ j, 0 ≤ T i j) (hb : ∀ j, 0 ≤ b j) (hv : 0 ≤ v) : 0 ≤ msTransitionCost T b v i := by
  unfold msTransitionCost
  apply mul_nonneg hv
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hT j) (hb j)
