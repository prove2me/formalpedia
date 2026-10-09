-- Prove2me | solution 1 for ActuarialValuation.deferredDue_eq_survival_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:39:48.986929+00:00
-- url     : https://prove2.me/submissions/f14b4674-fce4-491b-b683-f3a6946852a2

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityDuePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityDuePV K v n ω = ∑' k : ℕ, if n ≤ k then v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω else 0 := by
  classical
  have hzero :
      ∀ k ∉ Finset.range (K ω + 1),
        (if n ≤ k then v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω else 0) = 0 := by
    intro k hk
    have hnot : ω ∉ curtateSurvivalEvent K k := by
      change ¬ k ≤ K ω
      have hs : ¬ k < K ω + 1 := by simpa only [Finset.mem_range] using hk
      omega
    simp [Set.indicator, hnot]
  rw [tsum_eq_sum hzero]
  unfold deferredAnnuityDuePV
  apply Finset.sum_congr rfl
  intro k hk
  have hmem : ω ∈ curtateSurvivalEvent K k := by
    change k ≤ K ω
    have hlt : k < K ω + 1 := Finset.mem_range.mp hk
    omega
  simp [Set.indicator, hmem]