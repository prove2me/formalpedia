-- Prove2me | solution 1 for ActuarialValuation.nhIntensity_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:22.339709+00:00
-- url     : https://prove2.me/submissions/1d3e8213-b06b-45d3-af75-3555ef0fe74f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b t h : ℝ) : nhIntensity a b (t+h)=nhIntensity a b t+b*h := by
  unfold nhIntensity
  ring
