-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioVariance_pair_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:54:20.565168+00:00
-- url     : https://prove2.me/submissions/fbcbaf8b-7826-4881-9eb2-069ad62b5a8e

import Mathlib
import Definitions.Def_actuarial_finiteScenarioCovariance
import Definitions.Def_actuarial_finiteScenarioVariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (X Y : Ω → ℝ)
    (hcov : finiteScenarioCovariance w X Y = 0) :
    finiteScenarioVariance w (fun ω => X ω + Y ω) =
      finiteScenarioVariance w X + finiteScenarioVariance w Y := by
  have hmean : finiteScenarioExpectation w (fun ω => X ω + Y ω) =
      finiteScenarioExpectation w X + finiteScenarioExpectation w Y := by
    unfold finiteScenarioExpectation
    calc
      (∑ ω : Ω, w ω * (X ω + Y ω)) =
        ∑ ω : Ω, (w ω * X ω + w ω * Y ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
      _ = (∑ ω : Ω, w ω * X ω) + (∑ ω : Ω, w ω * Y ω) := by
        rw [Finset.sum_add_distrib]
  have hc := hcov
  unfold finiteScenarioCovariance at hc
  unfold finiteScenarioVariance
  rw [hmean]
  calc
    (∑ ω : Ω, w ω * ((X ω + Y ω) -
      (finiteScenarioExpectation w X + finiteScenarioExpectation w Y)) ^ 2) =
      ∑ ω : Ω,
        (w ω * (X ω - finiteScenarioExpectation w X) ^ 2 +
         w ω * (Y ω - finiteScenarioExpectation w Y) ^ 2 +
         2 * (w ω * (X ω - finiteScenarioExpectation w X) *
           (Y ω - finiteScenarioExpectation w Y))) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = (∑ ω : Ω, w ω * (X ω - finiteScenarioExpectation w X) ^ 2) +
        (∑ ω : Ω, w ω * (Y ω - finiteScenarioExpectation w Y) ^ 2) +
        2 * (∑ ω : Ω,
          w ω * (X ω - finiteScenarioExpectation w X) *
            (Y ω - finiteScenarioExpectation w Y)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ ω : Ω, w ω * (X ω - finiteScenarioExpectation w X) ^ 2) +
        (∑ ω : Ω, w ω * (Y ω - finiteScenarioExpectation w Y) ^ 2) := by
          rw [hc]
          ring
