-- Prove2me | solution 1 for ActuarialValuation.msStep_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:21:23.805971+00:00
-- url     : https://prove2.me/submissions/139ba903-032a-4160-b03e-d9e96b7bc05f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
import Definitions.Def_actuarial_msRowMass
import Definitions.Def_actuarial_msStep

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (hT : ∀ i, msRowMass T i = 1) : msMass (fun j => msStep p T j) = msMass p := by
  unfold msMass msStep
  calc
    (∑ j : Fin 3, ∑ i : Fin 3, p i * T i j) =
        (∑ i : Fin 3, ∑ j : Fin 3, p i * T i j) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin 3, p i * (∑ j : Fin 3, T i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i : Fin 3, p i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hrow : (∑ j : Fin 3, T i j) = 1 := by
            simpa only [msRowMass] using hT i
          rw [hrow, mul_one]
