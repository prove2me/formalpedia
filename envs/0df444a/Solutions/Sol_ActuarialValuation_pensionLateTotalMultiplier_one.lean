-- Prove2me | solution 1 for ActuarialValuation.pensionLateTotalMultiplier_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:12:23.613435+00:00
-- url     : https://prove2.me/submissions/efab2fef-cda2-4d47-8cb3-00692b8430ee

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLateTotalMultiplier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℝ) :
  pensionLateTotalMultiplier 1 f = f := by
  simp [pensionLateTotalMultiplier]
