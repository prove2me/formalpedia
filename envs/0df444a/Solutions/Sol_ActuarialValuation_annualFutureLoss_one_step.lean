-- Prove2me | solution 1 for ActuarialValuation.annualFutureLoss_one_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:46:53.178992+00:00
-- url     : https://prove2.me/submissions/a7bac666-79d8-434d-9978-af972c9b4142

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ)
    (n t : ℕ) (b π : ℝ) (ω : Ω) (ht : t < n) :
    annualFutureLoss K v n t b π ω +
        (if t ≤ K ω then π else 0) =
      (if K ω = t then v * b else 0) +
        v * annualFutureLoss K v n (t + 1) b π ω := by
  classical
  let k := K ω
  have hp (j : ℕ) :
      (if t ≤ j ∧ j ≤ k then v ^ (j - t) else (0 : ℝ)) =
      (if j = t ∧ t ≤ k then (1 : ℝ) else 0) +
        v * (if t + 1 ≤ j ∧ j ≤ k then v ^ (j - (t + 1)) else 0) := by
    by_cases hj : j < t
    · have ha : ¬ t ≤ j := by omega
      have hb : ¬ t + 1 ≤ j := by omega
      have hc : j ≠ t := by omega
      simp [ha, hb, hc]
    · by_cases he : j = t
      · subst j
        have ha : ¬ t + 1 ≤ t := by omega
        by_cases hkt : t ≤ k
        · simp [ha, hkt]
        · simp [ha, hkt]
      · have hj' : t + 1 ≤ j := by omega
        have hexp : j - t = (j - (t + 1)) + 1 := by omega
        by_cases hkj : j ≤ k
        · have hle : t ≤ j := by omega
          simp [hle, hj', hkj, he, hexp, pow_succ]
          ring
        · simp [hkj, he]
  have hsingle :
      (∑ j ∈ Finset.range n,
        if j = t ∧ t ≤ k then (1 : ℝ) else 0) =
      if t ≤ k then 1 else 0 := by
    have hmem : t ∈ Finset.range n := Finset.mem_range.mpr ht
    rw [Finset.sum_eq_single t]
    · simp
    · intro j hj hne
      simp [hne]
    · intro hnot
      exact (hnot hmem).elim
  have hsum :
      (∑ j ∈ Finset.range n,
        if t ≤ j ∧ j ≤ k then v ^ (j - t) else 0) =
      (if t ≤ k then 1 else 0) +
        v * (∑ j ∈ Finset.range n,
          if t + 1 ≤ j ∧ j ≤ k then v ^ (j - (t + 1)) else 0) := by
    calc
      _ = ∑ j ∈ Finset.range n,
          ((if j = t ∧ t ≤ k then (1 : ℝ) else 0) +
            v * (if t + 1 ≤ j ∧ j ≤ k then
              v ^ (j - (t + 1)) else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hp j
      _ = (∑ j ∈ Finset.range n,
            if j = t ∧ t ≤ k then (1 : ℝ) else 0) +
            v * (∑ j ∈ Finset.range n,
              if t + 1 ≤ j ∧ j ≤ k then
                v ^ (j - (t + 1)) else 0) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hsingle]
  have hc :
      (if t ≤ k ∧ k < n then b * v ^ (k + 1 - t) else 0) =
      (if k = t then v * b else 0) +
        v * (if t + 1 ≤ k ∧ k < n then
          b * v ^ (k + 1 - (t + 1)) else 0) := by
    by_cases he : k = t
    · rw [he]
      have hn : t < n := ht
      have ha : ¬ t + 1 ≤ t := by omega
      have hb : t ≤ t := le_refl t
      have hpow : t + 1 - t = 1 := by omega
      simp [hn, ha, hb, hpow]
      ring
    · by_cases hk : t + 1 ≤ k
      · by_cases hn : k < n
        · have hexp : k + 1 - t = (k + 1 - (t + 1)) + 1 := by omega
          have hle : t ≤ k := by omega
          simp [he, hk, hn, hle, hexp, pow_succ]
          ring
        · simp [he, hn]
      · have ha : ¬ t ≤ k := by omega
        simp [he, hk, ha]
  dsimp [k] at hsum hc
  unfold annualFutureLoss
  change (if t ≤ k ∧ k < n then b * v ^ (k + 1 - t) else 0) -
      π * (∑ j ∈ Finset.range n,
        if t ≤ j ∧ j ≤ k then v ^ (j - t) else 0) +
      (if t ≤ k then π else 0) =
      (if k = t then v * b else 0) +
      v * ((if t + 1 ≤ k ∧ k < n then
        b * v ^ (k + 1 - (t + 1)) else 0) -
        π * (∑ j ∈ Finset.range n,
          if t + 1 ≤ j ∧ j ≤ k then v ^ (j - (t + 1)) else 0))
  rw [hc, hsum]
  have hπ : (if t ≤ K ω then π else 0) =
      π * (if t ≤ K ω then (1 : ℝ) else 0) := by
    split_ifs <;> ring
  rw [hπ]
  ring
