-- Prove2me | solution 1 for ActuarialValuation.cm1NominalInterest_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:58.683394+00:00
-- url     : https://prove2.me/submissions/cbc863de-7402-4143-a972-afc5769f4515

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1NominalInterest
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (j m : ℝ) : cm1NominalInterest j m = m*j := by
  rfl
