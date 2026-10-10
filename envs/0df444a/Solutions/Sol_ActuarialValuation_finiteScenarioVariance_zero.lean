-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioVariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:02.563418+00:00
-- url     : https://prove2.me/submissions/ffce85d3-076b-47e3-9d1f-1e6640caa3d1

import Mathlib
import Definitions.Def_actuarial_finiteScenarioVariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) :
    finiteScenarioVariance w (fun _ => 0) = 0 := by
  simp [finiteScenarioVariance, finiteScenarioExpectation]
