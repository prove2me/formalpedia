-- Prove2me | solution 1 for ActuarialValuation.crExpected_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:03:57.32538+00:00
-- url     : https://prove2.me/submissions/5d00756b-d39f-45a4-adb5-513ee6883858

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

import Mathlib.Tactic.Ring

import Mathlib.Algebra.BigOperators.Ring.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X : Fin n→ℝ) (c : ℝ) : crExpected p (fun i=>c*X i) = c*crExpected p X := by
  unfold crExpected
  calc
    (∑ i : Fin n, p i * (c * X i)) = ∑ i : Fin n, c * (p i * X i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i : Fin n, p i * X i := by rw [Finset.mul_sum]
