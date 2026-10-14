-- Prove2me | solution 1 for ActuarialValuation.msExpectedBenefit_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:16:53.549642+00:00
-- url     : https://prove2.me/submissions/0b577c39-d8d7-4039-88ca-6e282c161bc9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msExpectedBenefit

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p b : Fin 3 → ℝ) (c : ℝ) : msExpectedBenefit p (fun i => c*b i) = c*msExpectedBenefit p b := by
  unfold msExpectedBenefit
  calc
    (∑ i : Fin 3, p i * (c * b i)) = ∑ i : Fin 3, c * (p i * b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * (∑ i : Fin 3, p i * b i) := by rw [Finset.mul_sum]
