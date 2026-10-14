-- Prove2me | solution 1 for ActuarialValuation.crRisk_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:25.419221+00:00
-- url     : https://prove2.me/submissions/f22edd87-039f-4f1b-85d7-43356220d6ca

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X Y : Fin n→ℝ) (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (hXY : ∀ i,X i≤Y i) : crScenarioRisk p q X≤crScenarioRisk p q Y := by
  unfold crScenarioRisk
  have he1 : crExpected p X ≤ crExpected p Y := by
    unfold crExpected
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hXY i) (hp i)
  have he2 : crExpected q X ≤ crExpected q Y := by
    unfold crExpected
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hXY i) (hq i)
  apply max_le
  · exact he1.trans (le_max_left _ _)
  · exact he2.trans (le_max_right _ _)
