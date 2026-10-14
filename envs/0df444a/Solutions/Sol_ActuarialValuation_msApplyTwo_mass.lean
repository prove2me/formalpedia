-- Prove2me | solution 1 for ActuarialValuation.msApplyTwo_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:19:15.209907+00:00
-- url     : https://prove2.me/submissions/6cedc0a7-4c2d-45ca-95af-90ba9546b957

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
import Definitions.Def_actuarial_msRowMass
import Definitions.Def_actuarial_msApplyTwo

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T U : Fin 3 → Fin 3 → ℝ) (hT : ∀ i, msRowMass T i = 1) (hU : ∀ i, msRowMass U i = 1) : msMass (msApplyTwo p T U) = msMass p := by
  have hmass (r : Fin 3 → ℝ) (Q : Fin 3 → Fin 3 → ℝ)
      (hQ : ∀ i, msRowMass Q i = 1) :
      msMass (fun j => msStep r Q j) = msMass r := by
    unfold msMass msStep
    calc
      (∑ j : Fin 3, ∑ i : Fin 3, r i * Q i j) =
          (∑ i : Fin 3, ∑ j : Fin 3, r i * Q i j) := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, r i * (∑ j : Fin 3, Q i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ i : Fin 3, r i := by
            apply Finset.sum_congr rfl
            intro i hi
            have hrow : (∑ j : Fin 3, Q i j) = 1 := by
              simpa only [msRowMass] using hQ i
            rw [hrow, mul_one]
  unfold msApplyTwo
  calc
    msMass (fun k => msStep (fun j => msStep p T j) U k) =
        msMass (fun j => msStep p T j) := hmass _ U hU
    _ = msMass p := hmass p T hT
