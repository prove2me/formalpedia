-- Prove2me | solution 1 for ActuarialValuation.crRisk_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:51.958132+00:00
-- url     : https://prove2.me/submissions/587f4da6-3575-4cd9-bcf8-8347ded81d05

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) (c : ℝ) (hp : (∑ i : Fin n,p i)=1) (hq : (∑ i : Fin n,q i)=1) : crScenarioRisk p q (fun i=>X i+c) = crScenarioRisk p q X+c := by
  have hcash (r : Fin n → ℝ) (hr : (∑ i : Fin n, r i) = 1) :
      crExpected r (fun i => X i + c) = crExpected r X + c := by
    unfold crExpected
    calc
      (∑ i : Fin n, r i * (X i + c)) =
          (∑ i : Fin n, r i * X i) + (∑ i : Fin n, r i * c) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = (∑ i : Fin n, r i * X i) + (∑ i : Fin n, r i) * c := by
        rw [Finset.sum_mul]
      _ = (∑ i : Fin n, r i * X i) + c := by rw [hr]; ring
  unfold crScenarioRisk
  rw [hcash p hp, hcash q hq]
  rcases le_total (crExpected p X) (crExpected q X) with h | h
  · rw [max_eq_right h]
    apply max_eq_right
    linarith
  · rw [max_eq_left h]
    apply max_eq_left
    linarith
