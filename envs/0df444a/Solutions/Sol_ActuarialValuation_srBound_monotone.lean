-- Prove2me | solution 1 for ActuarialValuation.srBound_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:09:09.201516+00:00
-- url     : https://prove2.me/submissions/223744fa-a2b2-46b9-95d5-0277a2778f88

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srLundbergBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R u v : ℝ) (hR : 0≤R) (h : u≤v) : srLundbergBound R v≤srLundbergBound R u := by
  unfold srLundbergBound
  apply Real.exp_le_exp.mpr
  have hh : R * u ≤ R * v := mul_le_mul_of_nonneg_left h hR
  simpa only [neg_mul] using (neg_le_neg hh)
