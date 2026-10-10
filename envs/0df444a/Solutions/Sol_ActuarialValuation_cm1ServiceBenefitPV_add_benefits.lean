-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_add_benefits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:30.455977+00:00
-- url     : https://prove2.me/submissions/4a571d35-70e4-45f8-95a3-349b0bd5798e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℕ → ℝ) (b c d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) : cm1ServiceBenefitPV v (fun t j => b t j + c t j) d l N m = cm1ServiceBenefitPV v b d l N m + cm1ServiceBenefitPV v c d l N m := by
  unfold cm1ServiceBenefitPV
  calc
    (∑ t ∈ Finset.range N, ∑ j ∈ Finset.range m,
      v t * (b t j + c t j) * cm1ServiceCohortCause l d t j) =
      ∑ t ∈ Finset.range N,
        ((∑ j ∈ Finset.range m, v t * b t j * cm1ServiceCohortCause l d t j) +
         (∑ j ∈ Finset.range m, v t * c t j * cm1ServiceCohortCause l d t j)) := by
           apply Finset.sum_congr rfl
           intro t ht
           rw [← Finset.sum_add_distrib]
           apply Finset.sum_congr rfl
           intro j hj
           ring
    _ = (∑ t ∈ Finset.range N, ∑ j ∈ Finset.range m,
           v t * b t j * cm1ServiceCohortCause l d t j) +
        (∑ t ∈ Finset.range N, ∑ j ∈ Finset.range m,
           v t * c t j * cm1ServiceCohortCause l d t j) := by
           rw [Finset.sum_add_distrib]
