-- Prove2me | solution 1 for ActuarialValuation.wholeLifeImmediate_eq_survival_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:28:04.28142+00:00
-- url     : https://prove2.me/submissions/8e4f80bc-6bf5-4394-9e6e-f6492f7ec743

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (ω : Ω)
    :
    wholeLifeAnnuityImmediatePV K v ω = ∑' k : ℕ, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  have hzero :
      ∀ k ∉ Finset.range (K ω),
        v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω = 0 := by
    intro k hk
    have hnot : ω ∉ curtateSurvivalEvent K (k + 1) := by
      change ¬ (k + 1) ≤ K ω
      have hs : ¬ k < K ω := by simpa only [Finset.mem_range] using hk
      omega
    simp [Set.indicator, hnot]
  rw [tsum_eq_sum hzero]
  unfold wholeLifeAnnuityImmediatePV
  apply Finset.sum_congr rfl
  intro k hk
  have hmem : ω ∈ curtateSurvivalEvent K (k + 1) := by
    change (k + 1) ≤ K ω
    have hlt : k < K ω := Finset.mem_range.mp hk
    omega
  simp [Set.indicator, hmem]
