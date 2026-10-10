-- Prove2me | solution 1 for ActuarialValuation.cm1LastSurvivorAnnuity_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:56.337621+00:00
-- url     : https://prove2.me/submissions/56390688-8eed-4086-8ece-59750a160c1d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LastSurvivorAnnuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pX pY both : ℕ → ℝ) : cm1LastSurvivorAnnuity discount pX pY both 0 = 0 := by
  simp [cm1LastSurvivorAnnuity]
