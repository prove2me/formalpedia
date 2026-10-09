-- Prove2me | solution 1 for ActuarialValuation.annualFutureLoss_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:24:55.477232+00:00
-- url     : https://prove2.me/submissions/4f26b15a-82ec-4eed-bef4-51e09625baab

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ)
  (hK : Measurable K) (v : ℝ) (n t : ℕ) (b π : ℝ) :
  Integrable (annualFutureLoss K v n t b π) P := by
  classical
  have hite (s : Set Ω) (hs : MeasurableSet s) (c : ℝ) :
      Integrable (fun ω : Ω => if ω ∈ s then c else 0) P := by
    have hc : Integrable (fun _ : Ω => c) P := integrable_const _
    have heq : (fun ω : Ω => if ω ∈ s then c else 0) =
        s.indicator (fun _ : Ω => c) := by
      funext ω
      by_cases h : ω ∈ s <;> simp [Set.indicator, h]
    rw [heq]
    exact hc.indicator hs
  have hpay (j : ℕ) :
      Integrable (fun ω : Ω =>
        if t ≤ j ∧ j ≤ K ω then v ^ (j - t) else 0) P := by
    have hs : MeasurableSet {ω : Ω | t ≤ j ∧ j ≤ K ω} := by
      by_cases hj : t ≤ j
      · simp only [hj, true_and]
        change MeasurableSet (K ⁻¹' Set.Ici j)
        exact hK measurableSet_Ici
      · simp [hj]
    simpa only [Set.mem_setOf_eq] using
      hite {ω : Ω | t ≤ j ∧ j ≤ K ω} hs (v ^ (j - t))
  have hpays : Integrable (fun ω : Ω =>
      ∑ j ∈ Finset.range n,
        if t ≤ j ∧ j ≤ K ω then v ^ (j - t) else 0) P :=
    integrable_finset_sum (Finset.range n) (fun j hj => hpay j)
  have hclaim (k : ℕ) :
      Integrable (fun ω : Ω =>
        if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0) P := by
    have hs : MeasurableSet {ω : Ω | t ≤ k ∧ K ω = k} := by
      by_cases hk : t ≤ k
      · simp only [hk, true_and]
        change MeasurableSet (K ⁻¹' {k})
        exact hK (measurableSet_singleton k)
      · simp [hk]
    simpa only [Set.mem_setOf_eq] using
      hite {ω : Ω | t ≤ k ∧ K ω = k} hs (b * v ^ (k + 1 - t))
  have hclaims : Integrable (fun ω : Ω =>
      ∑ k ∈ Finset.range n,
        if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0) P :=
    integrable_finset_sum (Finset.range n) (fun k hk => hclaim k)
  have heq (ω : Ω) :
      (if t ≤ K ω ∧ K ω < n then b * v ^ (K ω + 1 - t) else 0) =
        ∑ k ∈ Finset.range n,
          if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0 := by
    by_cases ht : t ≤ K ω
    · by_cases hn : K ω < n
      · have hm : (K ω) ∈ Finset.range n := Finset.mem_range.mpr hn
        have hsum : (∑ k ∈ Finset.range n,
              if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0) =
            (if t ≤ K ω ∧ K ω = K ω then
              b * v ^ (K ω + 1 - t) else 0) := by
          apply Finset.sum_eq_single (K ω)
          · intro k hk hne
            have he : K ω ≠ k := Ne.symm hne
            simp [he]
          · intro hnot
            exact (hnot hm).elim
        simpa [ht, hn] using hsum.symm
      · have hzero : (∑ k ∈ Finset.range n,
              if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hk : k < n := Finset.mem_range.mp hk
          have hneq : K ω ≠ k := by omega
          simp [hneq]
        simp [hn, hzero]
    · have hzero : (∑ k ∈ Finset.range n,
            if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        by_cases he : K ω = k
        · have hnk : ¬ t ≤ k := by omega
          simp [hnk]
        · simp [he]
      simp [ht, hzero]
  have hclaimInt : Integrable
      (fun ω : Ω =>
        if t ≤ K ω ∧ K ω < n then b * v ^ (K ω + 1 - t) else 0) P := by
    have hfun : (fun ω : Ω =>
        if t ≤ K ω ∧ K ω < n then b * v ^ (K ω + 1 - t) else 0) =
        (fun ω : Ω => ∑ k ∈ Finset.range n,
          if t ≤ k ∧ K ω = k then b * v ^ (k + 1 - t) else 0) := by
      funext ω
      exact heq ω
    rw [hfun]
    exact hclaims
  unfold annualFutureLoss
  exact hclaimInt.sub (hpays.const_mul π)
