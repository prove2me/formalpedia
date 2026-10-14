-- Prove2me | solution 1 for ActuarialValuation.msTransitionBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:17:41.903641+00:00
-- url     : https://prove2.me/submissions/fc9ee89a-37bb-4865-9e75-509f5366b14f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTransitionBenefit

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (v : ℝ) (hp : ∀ i, 0 ≤ p i) (hT : ∀ i j, 0 ≤ T i j) (hB : ∀ i j, 0 ≤ B i j) (hv : 0 ≤ v) : 0 ≤ msTransitionBenefit p T B v := by
  unfold msTransitionBenefit
  apply mul_nonneg hv
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hp i) (hT i j)) (hB i j)
