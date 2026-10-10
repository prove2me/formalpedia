-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioExpectation_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:02:41.447658+00:00
-- url     : https://prove2.me/submissions/c19042ae-378e-4b41-89af-a7b8f0adedf1

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) :
    finiteScenarioExpectation w (fun _ => 0) = 0 := by
  unfold finiteScenarioExpectation
  simp
