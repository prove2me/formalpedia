-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:37.2461+00:00
-- url     : https://prove2.me/submissions/231ebb73-8a05-444c-a1e8-607fb508fc09

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

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) (c : ℝ) : cm1ServiceBenefitPV v (fun t j => c * b t j) d l N m = c * cm1ServiceBenefitPV v b d l N m := by
  unfold cm1ServiceBenefitPV
  calc
    (∑ t ∈ Finset.range N, ∑ j ∈ Finset.range m,
      v t * (c * b t j) * cm1ServiceCohortCause l d t j) =
      ∑ t ∈ Finset.range N,
        c * (∑ j ∈ Finset.range m,
          v t * b t j * cm1ServiceCohortCause l d t j) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = c * (∑ t ∈ Finset.range N, ∑ j ∈ Finset.range m,
          v t * b t j * cm1ServiceCohortCause l d t j) := by
          rw [Finset.mul_sum]
