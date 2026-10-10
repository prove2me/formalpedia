-- Prove2me | solution 1 for ActuarialValuation.xlExpectedSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:08:29.723476+00:00
-- url     : https://prove2.me/submissions/85159930-5012-4da5-ae43-1349d41b2119

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlRetainedLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ)
  :
  xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) a) +
  xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) = xlExpectedLoss w z := by
  classical
  change (∑ ω : Ω, w ω * xlRetainedLoss (z ω) a) +
      (∑ ω : Ω, w ω * xlCededLoss (z ω) a) =
      ∑ ω : Ω, w ω * z ω
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  simp only [xlRetainedLoss, xlCededLoss]
  ring
