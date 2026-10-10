-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:16.945976+00:00
-- url     : https://prove2.me/submissions/7869f7e4-20cf-42c6-b3d2-8c8f063ef928

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

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) (h0 : 0 < l 0) (hv : ∀ t ∈ Finset.range N, 0 ≤ v t) (hb : ∀ t ∈ Finset.range N, ∀ j ∈ Finset.range m, 0 ≤ b t j) (hd : ∀ t ∈ Finset.range N, ∀ j ∈ Finset.range m, 0 ≤ d t j) : 0 ≤ cm1ServiceBenefitPV v b d l N m := by
  unfold cm1ServiceBenefitPV
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.sum_nonneg
  intro j hj
  have hc : 0 ≤ cm1ServiceCohortCause l d t j := by
    unfold cm1ServiceCohortCause
    exact div_nonneg (hd t ht j hj) (le_of_lt h0)
  exact mul_nonneg (mul_nonneg (hv t ht) (hb t ht j hj)) hc
