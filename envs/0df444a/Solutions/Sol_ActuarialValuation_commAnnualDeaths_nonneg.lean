-- Prove2me | solution 1 for ActuarialValuation.commAnnualDeaths_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:04:39.432045+00:00
-- url     : https://prove2.me/submissions/5065430f-7d68-4b65-8752-17dbbf860f3a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commAnnualDeaths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x : ℕ) (h : l (x+1) ≤ l x) : 0 ≤ commAnnualDeaths l x := by
  unfold commAnnualDeaths
  exact sub_nonneg.mpr h
