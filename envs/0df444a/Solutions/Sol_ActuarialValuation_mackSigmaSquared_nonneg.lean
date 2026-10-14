-- Prove2me | solution 1 for ActuarialValuation.mackSigmaSquared_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.276325+00:00
-- url     : https://prove2.me/submissions/511220fe-bf64-4ca8-af97-828461c5e840

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSigmaSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v df : ℝ) (hv : 0 ≤ v) (hdf : 0 < df) : 0 ≤ mackSigmaSquared v df := by
  unfold mackSigmaSquared
  exact div_nonneg hv (le_of_lt hdf)
