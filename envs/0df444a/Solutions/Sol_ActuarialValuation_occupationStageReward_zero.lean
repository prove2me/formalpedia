-- Prove2me | solution 1 for ActuarialValuation.occupationStageReward_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:11.030923+00:00
-- url     : https://prove2.me/submissions/65d70af5-b611-47d5-a7c7-1501b25eee06

import Mathlib
import Definitions.Def_actuarial_occupationStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ)
  :
  occupationStageReward μ (fun _ => 0) = 0 := by
  classical
  simp [occupationStageReward]
