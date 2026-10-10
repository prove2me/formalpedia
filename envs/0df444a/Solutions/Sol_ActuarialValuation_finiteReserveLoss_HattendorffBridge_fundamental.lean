-- Prove2me | solution 1 for ActuarialValuation.finiteReserveLoss_HattendorffBridge_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:38:37.130708+00:00
-- url     : https://prove2.me/submissions/3c159fc3-4f30-428c-8d7a-5d38cf4751da

import Mathlib
import Definitions.Def_actuarial_finiteReserveAnnualBalance
import Definitions.Def_actuarial_finiteReserveInnovationValue
import Definitions.Def_actuarial_finiteReserveLossAtIssue
import Theorems.Thm_ActuarialValuation_finiteReserveLossAtIssue_zero
import Theorems.Thm_ActuarialValuation_finiteReserveInnovationValue_zero
import Theorems.Thm_ActuarialValuation_finiteReserveLossAtIssue_succ
import Theorems.Thm_ActuarialValuation_finiteReserveInnovationValue_succ
import Theorems.Thm_ActuarialValuation_finiteReserveLoss_oneYearRiskIdentity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K n : ℕ) (v : ℝ) (reserve premium benefit p q : ℕ → ℝ)
    (hPQ : ∀ t ∈ Finset.range n, p t + q t = 1)
    (hR : ∀ t ∈ Finset.range n, finiteReserveAnnualBalance v reserve premium benefit p q t) :
    finiteReserveLossAtIssue K n v premium benefit reserve =
      reserve 0 + finiteReserveInnovationValue K n v benefit reserve q := by
  suffices h : ∀ m : ℕ,
      (∀ t ∈ Finset.range m, p t + q t = 1) →
      (∀ t ∈ Finset.range m,
        finiteReserveAnnualBalance v reserve premium benefit p q t) →
      finiteReserveLossAtIssue K m v premium benefit reserve =
        reserve 0 + finiteReserveInnovationValue K m v benefit reserve q by
    exact h n hPQ hR
  intro m
  induction m with
  | zero =>
      intro _ _
      rw [finiteReserveLossAtIssue_zero, finiteReserveInnovationValue_zero]
      ring
  | succ n ih =>
      intro hPQ hR
      have hPQn : ∀ t ∈ Finset.range n, p t + q t = 1 := by
        intro t ht
        exact hPQ t (Finset.mem_range.mpr
          (Nat.lt_succ_of_lt (Finset.mem_range.mp ht)))
      have hRn : ∀ t ∈ Finset.range n,
          finiteReserveAnnualBalance v reserve premium benefit p q t := by
        intro t ht
        exact hR t (Finset.mem_range.mpr
          (Nat.lt_succ_of_lt (Finset.mem_range.mp ht)))
      have hPQlast : p n + q n = 1 :=
        hPQ n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have hRlast : finiteReserveAnnualBalance v reserve premium benefit p q n :=
        hR n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      rw [finiteReserveLossAtIssue_succ, finiteReserveInnovationValue_succ]
      rw [ih hPQn hRn]
      have hOne := finiteReserveLoss_oneYearRiskIdentity
        K n v reserve premium benefit p q hPQlast hRlast
      linear_combination hOne
