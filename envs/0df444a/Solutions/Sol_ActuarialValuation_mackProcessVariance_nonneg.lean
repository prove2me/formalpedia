-- Prove2me | solution 1 for ActuarialValuation.mackProcessVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:46.941804+00:00
-- url     : https://prove2.me/submissions/28dcb6dd-3d0e-49c0-98e9-8d09df658877

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProcessVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s c : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c) : 0 ≤ mackProcessVariance s c := by
  unfold mackProcessVariance
  exact mul_nonneg hs hc
