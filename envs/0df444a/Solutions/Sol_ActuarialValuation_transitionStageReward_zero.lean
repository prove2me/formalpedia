-- Prove2me | solution 1 for ActuarialValuation.transitionStageReward_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:05.067109+00:00
-- url     : https://prove2.me/submissions/30c83b2f-e6ec-477e-9d17-a07de24df276

import Mathlib
import Definitions.Def_actuarial_transitionStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ)
  :
  transitionStageReward μ P (fun _ _ => 0) = 0 := by
  classical
  simp [transitionStageReward]
