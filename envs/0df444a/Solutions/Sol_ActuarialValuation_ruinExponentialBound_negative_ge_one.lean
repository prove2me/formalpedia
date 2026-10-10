-- Prove2me | solution 1 for ActuarialValuation.ruinExponentialBound_negative_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:52.550959+00:00
-- url     : https://prove2.me/submissions/029dd721-b823-4072-8d02-d63f1a135091

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (R : ℝ) (u : ℤ) (hR : 0 ≤ R) (hu : u < 0) :
  1 ≤ ruinExponentialBound R u := by
  unfold ruinExponentialBound
  apply Real.one_le_exp_iff.mpr
  apply neg_nonneg.mpr
  exact mul_nonpos_of_nonneg_of_nonpos hR (by exact_mod_cast le_of_lt hu)
