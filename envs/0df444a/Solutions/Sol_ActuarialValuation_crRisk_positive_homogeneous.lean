-- Prove2me | solution 1 for ActuarialValuation.crRisk_positive_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:13:56.321117+00:00
-- url     : https://prove2.me/submissions/d682003b-f74c-42dc-aa56-2aab7044fc2f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

import Mathlib.Tactic.Ring

import Mathlib.Algebra.BigOperators.Ring.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) (c : ℝ) (hc : 0≤c) : crScenarioRisk p q (fun i=>c*X i) = c*crScenarioRisk p q X := by
  have hep : crExpected p (fun i => c * X i) = c * crExpected p X := by
    unfold crExpected
    calc
      (∑ i : Fin n, p i * (c * X i)) = ∑ i : Fin n, c * (p i * X i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin n, p i * X i := by rw [Finset.mul_sum]
  have heq : crExpected q (fun i => c * X i) = c * crExpected q X := by
    unfold crExpected
    calc
      (∑ i : Fin n, q i * (c * X i)) = ∑ i : Fin n, c * (q i * X i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin n, q i * X i := by rw [Finset.mul_sum]
  unfold crScenarioRisk
  rw [hep, heq]
  rcases le_total (crExpected p X) (crExpected q X) with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hc)]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h hc)]
