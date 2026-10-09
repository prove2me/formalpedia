-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_eq_survival_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:26:11.056295+00:00
-- url     : https://prove2.me/submissions/a2bb9e53-c4c0-4dec-bd10-dad92fbbd7b1

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (ω : Ω)
    :
    wholeLifeAnnuityDuePV K v ω = ∑' k : ℕ, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  have hzero :
      ∀ k ∉ Finset.range (K ω + 1),
        v ^ k * (curtateSurvivalEvent K k).indicator
          (fun _ : Ω => (1 : ℝ)) ω = 0 := by
    intro k hk
    have hlt : K ω < k := by
      have hs : ¬ k < K ω + 1 := by simpa only [Finset.mem_range] using hk
      omega
    have hnot : ω ∉ curtateSurvivalEvent K k := by
      change ¬ k ≤ K ω
      omega
    simp [Set.indicator, hnot]
  rw [tsum_eq_sum hzero]
  unfold wholeLifeAnnuityDuePV
  apply Finset.sum_congr rfl
  intro k hk
  have hle : k ≤ K ω := by
    have hlt : k < K ω + 1 := Finset.mem_range.mp hk
    omega
  have hmem : ω ∈ curtateSurvivalEvent K k := hle
  simp [Set.indicator, hmem]
