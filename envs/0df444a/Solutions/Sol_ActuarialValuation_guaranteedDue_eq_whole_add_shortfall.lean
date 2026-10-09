-- Prove2me | solution 1 for ActuarialValuation.guaranteedDue_eq_whole_add_shortfall
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:45:10.58508+00:00
-- url     : https://prove2.me/submissions/817e2748-4cd8-4c34-9722-c38ba993f7c6

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
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
      wholeLifeAnnuityDuePV K v ω +
      (∑ k ∈ Finset.range n, if K ω < k then v ^ k else 0) := by
  change (∑ k ∈ Finset.range (max (K ω + 1) n), v ^ k) =
    (∑ k ∈ Finset.range (K ω + 1), v ^ k) +
    (∑ k ∈ Finset.range n, if K ω < k then v ^ k else 0)
  calc
    (∑ k ∈ Finset.range (max (K ω + 1) n), v ^ k) =
      (∑ k ∈ Finset.range (K ω + 1), v ^ k) +
      (∑ k ∈ Finset.range n, if (K ω + 1) ≤ k then v ^ k else 0) := by
        have h := sum_range_max_split (fun k => v ^ k) n (K ω + 1)
        rw [max_comm n (K ω + 1)] at h
        exact h
    _ = _ := by
      congr 1
