-- Prove2me | solution 1 for ActuarialValuation.nhExitOne_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:34:56.773855+00:00
-- url     : https://prove2.me/submissions/e80dee0a-a97b-4d7b-acf7-375969b41655

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhExitOne

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p s t : ℝ) (hp : 0≤p) (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hst : s≤t) : 0≤nhExitOne a b p s t := by
  unfold nhExitOne
  apply mul_nonneg hp
  have hcum : 0 ≤ nhCumulative a b t-nhCumulative a b s := by
    unfold nhCumulative
    have hts : 0 ≤ t-s := sub_nonneg.mpr hst
    have hsum : 0 ≤ t+s := by linarith
    have hprod : 0 ≤ (t-s)*(t+s) := mul_nonneg hts hsum
    have h1 : 0 ≤ a*(t-s) := mul_nonneg ha hts
    have h2 : 0 ≤ b*((t-s)*(t+s)) := mul_nonneg hb hprod
    nlinarith
  unfold nhSurvival
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
