-- Prove2me | solution 1 for ActuarialValuation.bnPutCall_price_parity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:35.898722+00:00
-- url     : https://prove2.me/submissions/7b139952-01f3-44da-9e55-f430d93c2011

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice
import Definitions.Def_actuarial_bnRiskNeutralProb
import Definitions.Def_actuarial_bnCall
import Definitions.Def_actuarial_bnPut

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d R k : ℝ) (h : u ≠ d) (hR : R ≠ 0) : bnOnePeriodPrice R (bnRiskNeutralProb u d R) (bnCall (s*u) k) (bnCall (s*d) k) - bnOnePeriodPrice R (bnRiskNeutralProb u d R) (bnPut (s*u) k) (bnPut (s*d) k) = s - k/R := by
  have hterminal (x : ℝ) : bnCall x k - bnPut x k = x-k := by
    unfold bnCall bnPut
    rcases le_total x k with hx | hx
    · rw [max_eq_right (by linarith : x-k ≤ (0:ℝ))]
      rw [max_eq_left (by linarith : (0:ℝ) ≤ k-x)]
      ring
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x-k)]
      rw [max_eq_right (by linarith : k-x ≤ (0:ℝ))]
      ring
  unfold bnOnePeriodPrice bnExpectedPayoff
  calc
    _ = (bnRiskNeutralProb u d R *
          (bnCall (s*u) k - bnPut (s*u) k) +
          (1 - bnRiskNeutralProb u d R) *
          (bnCall (s*d) k - bnPut (s*d) k)) / R := by ring
    _ = (bnRiskNeutralProb u d R * (s*u-k) +
          (1 - bnRiskNeutralProb u d R) * (s*d-k)) / R := by
      rw [hterminal (s*u), hterminal (s*d)]
    _ = s - k/R := by
      unfold bnRiskNeutralProb
      field_simp [hR, sub_ne_zero.mpr h] <;> ring
