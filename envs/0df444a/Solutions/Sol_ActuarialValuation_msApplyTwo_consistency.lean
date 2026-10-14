-- Prove2me | solution 1 for ActuarialValuation.msApplyTwo_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:23.624396+00:00
-- url     : https://prove2.me/submissions/5e2805fa-4be2-4076-8527-506abc8cacd3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msStep
import Definitions.Def_actuarial_msTwoStep
import Definitions.Def_actuarial_msApplyTwo

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T U : Fin 3 → Fin 3 → ℝ) (k : Fin 3) : msApplyTwo p T U k = msStep p (msTwoStep T U) k := by
  unfold msApplyTwo msStep msTwoStep
  calc
    (∑ j : Fin 3, (∑ i : Fin 3, p i * T i j) * U j k)
        = ∑ j : Fin 3, ∑ i : Fin 3, (p i * T i j) * U j k := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, p i * (T i j * U j k) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i : Fin 3, p i * (∑ j : Fin 3, T i j * U j k) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
