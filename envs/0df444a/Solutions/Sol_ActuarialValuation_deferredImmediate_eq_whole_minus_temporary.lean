-- Prove2me | solution 1 for ActuarialValuation.deferredImmediate_eq_whole_minus_temporary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:31:55.275821+00:00
-- url     : https://prove2.me/submissions/98e6d469-38f3-4a68-8923-d3d95f1a57ce

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityImmediatePV K v n ω = wholeLifeAnnuityImmediatePV K v ω -
      (∑ k ∈ Finset.range n, v ^ (k + 1) *
        (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω) := by
  classical
  let m := K ω
  have hind (k : ℕ) :
      (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω =
        if k < m then 1 else 0 := by
    by_cases hk : k < m
    · have hm : ω ∈ curtateSurvivalEvent K (k + 1) := by
        change k + 1 ≤ K ω
        dsimp [m] at hk
        omega
      simp [Set.indicator, hk, hm]
    · have hm : ω ∉ curtateSurvivalEvent K (k + 1) := by
        change ¬ k + 1 ≤ K ω
        dsimp [m] at hk
        omega
      simp [Set.indicator, hk, hm]
  have hprefix :
      (∑ k ∈ Finset.range n, v ^ (k + 1) *
        (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω) =
        ∑ k ∈ Finset.range m, if k < n then v ^ (k + 1) else 0 := by
    simp_rw [hind]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hpoint (k : ℕ) :
      (if n ≤ k then v ^ (k + 1) else 0) =
        v ^ (k + 1) - (if k < n then v ^ (k + 1) else 0) := by
    by_cases h : n ≤ k
    · simp [h, Nat.not_lt.mpr h]
    · have hk : k < n := Nat.lt_of_not_ge h
      simp [h, hk]
  calc
    deferredAnnuityImmediatePV K v n ω =
        ∑ k ∈ Finset.range m, if n ≤ k then v ^ (k + 1) else 0 := by
          rfl
    _ = ∑ k ∈ Finset.range m, (v ^ (k + 1) - (if k < n then v ^ (k + 1) else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hpoint k
    _ = (∑ k ∈ Finset.range m, v ^ (k + 1)) -
        (∑ k ∈ Finset.range m, if k < n then v ^ (k + 1) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = wholeLifeAnnuityImmediatePV K v ω -
        (∑ k ∈ Finset.range n, v ^ (k + 1) *
          (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω) := by
          rw [hprefix]
          rfl