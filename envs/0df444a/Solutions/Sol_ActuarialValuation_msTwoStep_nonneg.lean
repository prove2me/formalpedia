-- Prove2me | solution 1 for ActuarialValuation.msTwoStep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:13.457395+00:00
-- url     : https://prove2.me/submissions/eb675fc3-a561-4f3e-8082-84762f6e7d84

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTwoStep

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (T U : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) (hT : ∀ j, 0 ≤ T i j) (hU : ∀ j, 0 ≤ U j k) : 0 ≤ msTwoStep T U i k := by
  unfold msTwoStep
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hT j) (hU j)
