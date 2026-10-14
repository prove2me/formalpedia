-- Prove2me | solution 1 for ActuarialValuation.srAdjustment_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:03:19.568529+00:00
-- url     : https://prove2.me/submissions/056bfeef-d06a-4cd9-b6d9-12b3d3a43b55

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

theorem solution (lambda c beta : ℝ) (hc : 0<c) (hbeta : 0<beta) (hn : lambda<c*beta) : 0<srAdjustment lambda c beta := by
  change 0 < beta - lambda / c
  apply sub_pos.mpr
  exact (div_lt_iff₀ hc).2 (by simpa only [mul_comm] using hn)
