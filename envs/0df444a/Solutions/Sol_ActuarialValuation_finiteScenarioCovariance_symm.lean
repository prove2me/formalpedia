-- Prove2me | solution 1 for ActuarialValuation.finiteScenarioCovariance_symm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:07.051743+00:00
-- url     : https://prove2.me/submissions/fb85232e-a13d-4282-89e8-9dec16895433

import Mathlib
import Definitions.Def_actuarial_finiteScenarioCovariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (X Y : Ω → ℝ) :
    finiteScenarioCovariance w X Y =
      finiteScenarioCovariance w Y X := by
  unfold finiteScenarioCovariance
  apply Finset.sum_congr rfl
  intro ω _
  ring
