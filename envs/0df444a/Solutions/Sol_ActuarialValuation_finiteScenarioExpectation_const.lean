-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioExpectation_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:16.223773+00:00
-- url     : https://prove2.me/submissions/f1bd2f06-29fd-4ffc-8bc2-c6b438368722

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : (∑ ω : Ω, w ω) = 1) (a : ℝ) :
    finiteScenarioExpectation w (fun _ => a) = a := by
  unfold finiteScenarioExpectation
  simp only [← Finset.sum_mul, hw, one_mul]
