-- Prove2me | solution 1 for ActuarialValuation.xlExpectedValueCostLoading
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:08:37.349629+00:00
-- url     : https://prove2.me/submissions/502816ed-8d53-4b19-b8db-e40b788b3928

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a θ : ℝ)
  :
  xlExpectedValuePremiumCost w z a θ =
    xlExpectedLoss w z + θ * xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) := by
  classical
  have hsplit :
      xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) a) +
      xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) =
      xlExpectedLoss w z := by
    change (∑ ω : Ω, w ω * xlRetainedLoss (z ω) a) +
      (∑ ω : Ω, w ω * xlCededLoss (z ω) a) =
      ∑ ω : Ω, w ω * z ω
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    simp only [xlRetainedLoss, xlCededLoss]
    ring
  unfold xlExpectedValuePremiumCost
  calc
    xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) a) +
        (1 + θ) * xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) =
      (xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) a) +
       xlExpectedLoss w (fun ω => xlCededLoss (z ω) a)) +
       θ * xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) := by ring
    _ = xlExpectedLoss w z +
        θ * xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) := by rw [hsplit]
