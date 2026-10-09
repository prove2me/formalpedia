-- Prove2me | solution 1 for ActuarialValuation.deferredImmediate_eq_survival_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:39:53.149973+00:00
-- url     : https://prove2.me/submissions/b4bca79e-9545-487e-98d4-1d0a3e70e834

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityImmediatePV K v n ω = ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω else 0 := by
  classical
  have hzero :
      ∀ k ∉ Finset.range (K ω),
        (if n ≤ k then v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω else 0) = 0 := by
    intro k hk
    have hnot : ω ∉ curtateSurvivalEvent K (k + 1) := by
      change ¬ (k + 1) ≤ K ω
      have hs : ¬ k < K ω := by simpa only [Finset.mem_range] using hk
      omega
    simp [Set.indicator, hnot]
  rw [tsum_eq_sum hzero]
  unfold deferredAnnuityImmediatePV
  apply Finset.sum_congr rfl
  intro k hk
  have hmem : ω ∈ curtateSurvivalEvent K (k + 1) := by
    change (k + 1) ≤ K ω
    have hlt : k < K ω := Finset.mem_range.mp hk
    omega
  simp [Set.indicator, hmem]