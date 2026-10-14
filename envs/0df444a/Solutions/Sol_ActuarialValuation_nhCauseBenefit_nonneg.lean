-- Prove2me | solution 1 for ActuarialValuation.nhCauseBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:30:20.946746+00:00
-- url     : https://prove2.me/submissions/ace284d0-cb64-4674-9762-77d0f808704a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhCauseBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p B1 B2 : ℝ) (hp : 0≤p) (hq : p≤1) (h1 : 0≤B1) (h2 : 0≤B2) : 0≤nhCauseBenefit p B1 B2 := by
  unfold nhCauseBenefit
  exact add_nonneg (mul_nonneg hp h1) (mul_nonneg (sub_nonneg.mpr hq) h2)
