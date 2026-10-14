-- Prove2me | solution 1 for ActuarialValuation.srAdjustment_lt_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:02:38.496839+00:00
-- url     : https://prove2.me/submissions/eae3ff8c-bfe3-4151-8c25-eb28df386670

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srAdjustment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ) (hl : 0<lambda) (hc : 0<c) : srAdjustment lambda c beta<beta := by
  simpa only [srAdjustment] using
    (sub_lt_self beta (div_pos hl hc))
