-- Prove2me | solution 1 for ActuarialValuation.csBenefit_all_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:31.810386+00:00
-- url     : https://prove2.me/submissions/ebe903e0-4107-440d-ba67-7d726452cb50

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csCauseInsurancePV
import Definitions.Def_actuarial_csPrimitiveTie
import Theorems.Thm_ActuarialValuation_csCausePartition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (disc b : ℝ) (hU : Measurable U) (hV : Measurable V)
    (hZ : Measurable Z) (htie : csPrimitiveTie μ U V Z = 0) :
    csCauseInsurancePV μ U V Z disc b b b = disc * b := by
  let x : ENNReal := csCauseOne μ U V Z
  let y : ENNReal := csCauseTwo μ U V Z
  let z : ENNReal := csShockCause μ U V Z
  have hpart : x + y + z = 1 := by
    dsimp [x, y, z]
    exact csCausePartition μ U V Z hU hV hZ htie
  have hxyz : x + y + z ≠ ⊤ := by
    rw [hpart]
    simp
  have hxy : x + y ≠ ⊤ := by
    intro h
    apply hxyz
    simp [h]
  have hx : x ≠ ⊤ := by
    intro h
    apply hxy
    simp [h]
  have hy : y ≠ ⊤ := by
    intro h
    apply hxy
    simp [h]
  have hz : z ≠ ⊤ := by
    intro h
    apply hxyz
    simp [h]
  have hto : (x + y + z).toReal =
      x.toReal + y.toReal + z.toReal := by
    rw [ENNReal.toReal_add hxy hz, ENNReal.toReal_add hx hy]
  have hsum : x.toReal + y.toReal + z.toReal = 1 := by
    have h := congrArg ENNReal.toReal hpart
    rw [hto] at h
    simpa using h
  change disc * (b * x.toReal + b * y.toReal + b * z.toReal) =
    disc * b
  calc
    disc * (b * x.toReal + b * y.toReal + b * z.toReal) =
        disc * (b * (x.toReal + y.toReal + z.toReal)) := by ring
    _ = disc * b := by rw [hsum]; ring
