-- Prove2me | solution 1 for ActuarialValuation.cm1DeathStrainAtRisk_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:00.889487+00:00
-- url     : https://prove2.me/submissions/7fe0b327-5224-459a-b6ad-dc4af4b863f0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DeathStrainAtRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (S : ℝ) : cm1DeathStrainAtRisk S 0 = S := by
  simp [cm1DeathStrainAtRisk]
