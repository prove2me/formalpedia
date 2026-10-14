-- Prove2me | solution 1 for ActuarialValuation.msStep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:00.885978+00:00
-- url     : https://prove2.me/submissions/531ba5d8-a15d-4ea5-83d6-7aeb54e46ae1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msStep

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (j : Fin 3) (hp : ∀ i, 0 ≤ p i) (hT : ∀ i, 0 ≤ T i j) : 0 ≤ msStep p T j := by
  unfold msStep
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp i) (hT i)
