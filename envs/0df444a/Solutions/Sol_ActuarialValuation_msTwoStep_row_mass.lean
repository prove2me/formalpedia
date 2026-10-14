-- Prove2me | solution 1 for ActuarialValuation.msTwoStep_row_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:19:31.554657+00:00
-- url     : https://prove2.me/submissions/cf7fef07-6d7e-40fe-a003-f5596ab34a96

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msRowMass
import Definitions.Def_actuarial_msTwoStep

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (T U : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (hU : ∀ j, msRowMass U j = 1) : msRowMass (msTwoStep T U) i = msRowMass T i := by
  unfold msRowMass msTwoStep
  calc
    (∑ k : Fin 3, ∑ j : Fin 3, T i j * U j k) =
        (∑ j : Fin 3, ∑ k : Fin 3, T i j * U j k) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin 3, T i j * (∑ k : Fin 3, U j k) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ j : Fin 3, T i j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hrow : (∑ k : Fin 3, U j k) = 1 := by
            simpa only [msRowMass] using hU j
          rw [hrow, mul_one]
