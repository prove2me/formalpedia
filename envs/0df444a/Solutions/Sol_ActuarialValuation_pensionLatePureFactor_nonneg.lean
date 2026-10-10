-- Prove2me | solution 1 for ActuarialValuation.pensionLatePureFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:12:04.917494+00:00
-- url     : https://prove2.me/submissions/567ea016-7a83-4c3d-9211-fb0361442470

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePureFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N D p v m A : ℝ)
  (hN : D ≤ N) (hden : 0 < p * v * m * A) :
  0 ≤ pensionLatePureFactor N D p v m A := by
  change 0 ≤ (N - D) / (p * v * m * A)
  exact div_nonneg (sub_nonneg.mpr hN) (le_of_lt hden)
