-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioExpectation_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:25.914857+00:00
-- url     : https://prove2.me/submissions/5f62c94b-4745-4d20-acaa-bb61f5834fef

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (X Y : Ω → ℝ) (a : ℝ) :
    finiteScenarioExpectation w (fun ω => X ω + a * Y ω) =
    finiteScenarioExpectation w X + a * finiteScenarioExpectation w Y := by
  unfold finiteScenarioExpectation
  calc
    (∑ ω : Ω, w ω * (X ω + a * Y ω)) =
        ∑ ω : Ω, (w ω * X ω + a * (w ω * Y ω)) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = (∑ ω : Ω, w ω * X ω) + a * (∑ ω : Ω, w ω * Y ω) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
