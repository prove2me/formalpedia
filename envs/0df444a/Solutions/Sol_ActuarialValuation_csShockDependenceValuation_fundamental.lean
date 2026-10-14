-- Prove2me | solution 1 for ActuarialValuation.csShockDependenceValuation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:06:38.598983+00:00
-- url     : https://prove2.me/submissions/4712c1b8-176b-400f-b678-e08c10adc2ab

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseOne
import Definitions.Def_actuarial_csCauseTwo
import Definitions.Def_actuarial_csShockCause
import Definitions.Def_actuarial_csPrimitiveTie
import Definitions.Def_actuarial_csJointIndependentExp
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csCauseInsurancePV
import Theorems.Thm_ActuarialValuation_csCausePartition
import Theorems.Thm_ActuarialValuation_csJointExp_strict_dependence
import Theorems.Thm_ActuarialValuation_csBenefit_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (disc b1 b2 bz a b c t : ℝ) (hU : Measurable U) (hV : Measurable V) (hZ : Measurable Z) (htie : csPrimitiveTie μ U V Z = 0) (hc : 0 < c) (ht : 0 < t) (hd : 0 ≤ disc) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hbz : 0 ≤ bz) : (csCauseOne μ U V Z + csCauseTwo μ U V Z + csShockCause μ U V Z = 1) ∧ (csJointIndependentExp a b c t < csJointExp a b c t t) ∧ (0 ≤ csCauseInsurancePV μ U V Z disc b1 b2 bz) := by
  refine ⟨?_, ?_, ?_⟩
  · exact csCausePartition μ U V Z hU hV hZ htie
  · exact csJointExp_strict_dependence a b c t hc ht
  · exact csBenefit_nonneg μ U V Z disc b1 b2 bz hd hb1 hb2 hbz
