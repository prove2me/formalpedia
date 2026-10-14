-- Prove2me | solution 1 for ActuarialValuation.svMakeham_hazard_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:39.201979+00:00
-- url     : https://prove2.me/submissions/8a69e4bb-7255-4164-8f28-5317c84ddfeb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svMakehamHazard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ svMakehamHazard a b c t := by
  unfold svMakehamHazard svGompertzHazard
  exact add_nonneg ha (mul_nonneg hb (le_of_lt (Real.exp_pos _)))
