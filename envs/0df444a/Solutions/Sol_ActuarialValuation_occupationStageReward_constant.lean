-- Prove2me | solution 1 for ActuarialValuation.occupationStageReward_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:37.214099+00:00
-- url     : https://prove2.me/submissions/fb466f17-e452-434c-a751-883ad2889ebb

import Mathlib
import Definitions.Def_actuarial_occupationStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (hμ : (∑ i : S, μ i) = 1) (a : ℝ)
  :
  occupationStageReward μ (fun _ => a) = a := by
  classical
  change (∑ i : S, μ i * a) = a
  calc
    (∑ i : S, μ i * a) = (∑ i : S, μ i) * a := by rw [Finset.sum_mul]
    _ = a := by rw [hμ]; ring
