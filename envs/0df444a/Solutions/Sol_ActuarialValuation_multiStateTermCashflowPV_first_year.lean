-- Prove2me | solution 1 for ActuarialValuation.multiStateTermCashflowPV_first_year
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:32.257226+00:00
-- url     : https://prove2.me/submissions/b90960bd-74ad-4d5f-8afe-eb0e576f5d7e

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
import Definitions.Def_actuarial_occupationStageReward
import Definitions.Def_actuarial_transitionStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) 
  :
  multiStateTermCashflowPV μ P b c v 1 =
    occupationStageReward (μ 0) (c 0) +
      v * transitionStageReward (μ 0) (P 0) (b 0) := by
  classical
  simp [multiStateTermCashflowPV]
