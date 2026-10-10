-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceCohortValuation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:59:17.575668+00:00
-- url     : https://prove2.me/submissions/405b112c-3d8b-41b0-b2b7-44287eec5fb0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceValid
import Definitions.Def_actuarial_cm1ServiceTotalExits
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Definitions.Def_actuarial_cm1ServiceConditionalPV
import Definitions.Def_actuarial_cm1ServiceTerminalMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d b : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (N m : ℕ) (valid : cm1ServiceValid l d N m) (h0 : 0 < l 0) (hpos : ∀ t ∈ Finset.range N, 0 < l t) (hv : ∀ t ∈ Finset.range N, 0 ≤ v t) (hb : ∀ t ∈ Finset.range N, ∀ j ∈ Finset.range m, 0 ≤ b t j) (hd : ∀ t ∈ Finset.range N, ∀ j ∈ Finset.range m, 0 ≤ d t j) : (cm1ServiceTerminalMass l N + cm1ServiceTotalExits d N m / l 0 = 1) ∧ (cm1ServiceBenefitPV v b d l N m = cm1ServiceConditionalPV v b d l N m) ∧ (0 ≤ cm1ServiceBenefitPV v b d l N m) := by
  have htelescope :
      ∀ n, cm1ServiceValid l d n m →
        cm1ServiceTotalExits d n m + l n = l 0 := by
    intro n
    induction n with
    | zero =>
        intro h
        simp [cm1ServiceTotalExits]
    | succ k ih =>
        intro h
        have hp : cm1ServiceValid l d k m := by
          intro t ht
          exact h t (Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self k)))
        have hs : l (k+1) + cm1ServiceAnnualExit d k m = l k :=
          h k (Finset.mem_range.mpr (Nat.lt_succ_self k))
        have hi := ih hp
        change (∑ t ∈ Finset.range k, cm1ServiceAnnualExit d t m) + l k = l 0 at hi
        change (∑ t ∈ Finset.range (k+1), cm1ServiceAnnualExit d t m) +
          l (k+1) = l 0
        rw [Finset.sum_range_succ]
        linarith
  have hmass : cm1ServiceTerminalMass l N +
      cm1ServiceTotalExits d N m / l 0 = 1 := by
    have hsum := htelescope N valid
    unfold cm1ServiceTerminalMass
    field_simp [ne_of_gt h0]
    linarith
  have heq : cm1ServiceBenefitPV v b d l N m =
      cm1ServiceConditionalPV v b d l N m := by
    unfold cm1ServiceBenefitPV cm1ServiceConditionalPV
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro j hj
    have htne : l t ≠ 0 := ne_of_gt (hpos t ht)
    unfold cm1ServiceCohortCause cm1ServiceSurvivalMass cm1ServiceConditionalCause
    field_simp [ne_of_gt h0, htne]
  have hnonneg : 0 ≤ cm1ServiceBenefitPV v b d l N m := by
    unfold cm1ServiceBenefitPV
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro j hj
    have hc : 0 ≤ cm1ServiceCohortCause l d t j := by
      unfold cm1ServiceCohortCause
      exact div_nonneg (hd t ht j hj) (le_of_lt h0)
    exact mul_nonneg (mul_nonneg (hv t ht) (hb t ht j hj)) hc
  exact ⟨hmass, heq, hnonneg⟩
