-- Prove2me | solution 1 for ActuarialValuation.csCauseInsurancePV_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:00:56.556039+00:00
-- url     : https://prove2.me/submissions/8c4ea00a-39dc-49d9-9ffb-db1108472df4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csCauseInsurancePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    (disc a1 a2 az b1 b2 bz : ℝ) :
    csCauseInsurancePV μ U V Z disc (a1+b1) (a2+b2) (az+bz) =
      csCauseInsurancePV μ U V Z disc a1 a2 az +
      csCauseInsurancePV μ U V Z disc b1 b2 bz := by
  unfold csCauseInsurancePV
  ring
