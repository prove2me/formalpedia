-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioVariance_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:52:22.760719+00:00
-- url     : https://prove2.me/submissions/6903d81c-62c6-4242-a5aa-ecdb1cd2621c

import Mathlib
import Definitions.Def_actuarial_finiteScenarioVariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (X : Ω → ℝ) (a : ℝ)
    (hw : (∑ ω : Ω, w ω) = 1) :
    finiteScenarioVariance w (fun ω => X ω + a) =
      finiteScenarioVariance w X := by
  have hmean : finiteScenarioExpectation w (fun ω => X ω + a) =
      finiteScenarioExpectation w X + a := by
    unfold finiteScenarioExpectation
    calc
      (∑ ω : Ω, w ω * (X ω + a)) =
        (∑ ω : Ω, w ω * X ω) + (∑ ω : Ω, w ω * a) := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = (∑ ω : Ω, w ω * X ω) + a := by
          rw [← Finset.sum_mul, hw]
          ring
  unfold finiteScenarioVariance
  rw [hmean]
  apply Finset.sum_congr rfl
  intro ω _
  ring
