-- Prove2me | solution 1 for ActuarialValuation.multiStateTermCashflowPV_zero_cashflows
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:56.143977+00:00
-- url     : https://prove2.me/submissions/cf42d5db-044f-4de6-a326-c440bf4faee5

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ) (v : ℝ) (n : ℕ)
  :
  multiStateTermCashflowPV μ P (fun _ _ _ => 0) (fun _ _ => 0) v n = 0 := by
  classical
  simp [multiStateTermCashflowPV, occupationStageReward, transitionStageReward]
