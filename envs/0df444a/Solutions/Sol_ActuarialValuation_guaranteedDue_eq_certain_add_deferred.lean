-- Prove2me | solution 1 for ActuarialValuation.guaranteedDue_eq_certain_add_deferred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:33:26.932883+00:00
-- url     : https://prove2.me/submissions/523b560b-4f05-430b-b2a1-215209ac9609

import Mathlib
import Definitions.Def_actuarial_annuityCertainDuePV
import Definitions.Def_actuarial_annuityCertainImmediatePV
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

private theorem sum_range_max_split (f : ℕ → ℝ) (a n : ℕ) :
    (∑ k ∈ Finset.range (max a n), f k) =
      (∑ k ∈ Finset.range n, f k) +
      (∑ k ∈ Finset.range a, if n ≤ k then f k else 0) := by
  by_cases h : a ≤ n
  · rw [max_eq_right h]
    have hzero :
        (∑ k ∈ Finset.range a, if n ≤ k then f k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkn : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) h
      simp [Nat.not_le.mpr hkn]
    simp [hzero]
  · have hn : n ≤ a := by omega
    have ha : a = n + (a - n) := by omega
    rw [max_eq_left hn, ha]
    simp only [Finset.sum_range_add]
    have hzero :
        (∑ k ∈ Finset.range n, if n ≤ k then f k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [Nat.not_le.mpr (Finset.mem_range.mp hk)]
    rw [hzero, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simp

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityDuePV K v n ω =
      annuityCertainDuePV v n + deferredAnnuityDuePV K v n ω := by
  change (∑ k ∈ Finset.range (max (K ω + 1) n), v ^ k) =
    (∑ k ∈ Finset.range n, v ^ k) +
    (∑ k ∈ Finset.range (K ω + 1), if n ≤ k then v ^ k else 0)
  exact sum_range_max_split (fun k => v ^ k) (K ω + 1) n
