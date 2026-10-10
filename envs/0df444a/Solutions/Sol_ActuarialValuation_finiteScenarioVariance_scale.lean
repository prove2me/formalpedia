-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioVariance_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:52:17.27646+00:00
-- url     : https://prove2.me/submissions/18a37195-7c11-4d63-ad9f-46f906b4aa04

import Mathlib
import Definitions.Def_actuarial_finiteScenarioVariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (X : Ω → ℝ) (a : ℝ) :
    finiteScenarioVariance w (fun ω => a * X ω) =
      a ^ 2 * finiteScenarioVariance w X := by
  have hmean : finiteScenarioExpectation w (fun ω => a * X ω) =
      a * finiteScenarioExpectation w X := by
    unfold finiteScenarioExpectation
    calc
      (∑ ω : Ω, w ω * (a * X ω)) =
        ∑ ω : Ω, a * (w ω * X ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
      _ = a * (∑ ω : Ω, w ω * X ω) := by
        rw [Finset.mul_sum]
  unfold finiteScenarioVariance
  rw [hmean]
  calc
    (∑ ω : Ω, w ω * (a * X ω - a * finiteScenarioExpectation w X) ^ 2) =
      ∑ ω : Ω, a ^ 2 * (w ω * (X ω - finiteScenarioExpectation w X) ^ 2) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
    _ = a ^ 2 * (∑ ω : Ω, w ω * (X ω - finiteScenarioExpectation w X) ^ 2) := by
      rw [Finset.mul_sum]
