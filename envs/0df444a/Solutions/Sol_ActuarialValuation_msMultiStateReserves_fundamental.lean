-- Prove2me | solution 1 for ActuarialValuation.msMultiStateReserves_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:36.380683+00:00
-- url     : https://prove2.me/submissions/55feb727-ce13-4ea5-a9f4-25cc2ea4a489

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
import Definitions.Def_actuarial_msRowMass
import Definitions.Def_actuarial_msStep
import Definitions.Def_actuarial_msTwoStep
import Definitions.Def_actuarial_msApplyTwo
import Definitions.Def_actuarial_msReserveOne
import Definitions.Def_actuarial_msTransitionCost
import Definitions.Def_actuarial_msSemiReserve

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p b V : Fin 3 → ℝ) (T U : Fin 3 → Fin 3 → ℝ) (discount : ℝ) (duration : ℕ) (Td : ℕ → Fin 3 → Fin 3 → ℝ) (hT : ∀ i, msRowMass T i=1) (hU : ∀ i, msRowMass U i=1) : (msMass (fun j => msStep p T j)=msMass p) ∧ (∀ k : Fin 3, msApplyTwo p T U k=msStep p (msTwoStep T U) k) ∧ (∀ i : Fin 3, msReserveOne b T V discount i=b i+msTransitionCost T V discount i) ∧ (∀ i : Fin 3, msSemiReserve b Td V discount duration i = msReserveOne b (Td duration) V discount i) := by
  have hmass : msMass (fun j => msStep p T j) = msMass p := by
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
  have hcompose (k : Fin 3) :
      msApplyTwo p T U k = msStep p (msTwoStep T U) k := by
    unfold msApplyTwo msStep msTwoStep
    calc
      (∑ j : Fin 3, (∑ i : Fin 3, p i * T i j) * U j k) =
          ∑ j : Fin 3, ∑ i : Fin 3, (p i * T i j) * U j k := by
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
  refine ⟨hmass, hcompose, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl
