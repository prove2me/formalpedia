-- Prove2me | solution 1 for ActuarialValuation.pfExperienceAttribution_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:27:20.995223+00:00
-- url     : https://prove2.me/submissions/ff543d96-a419-4646-8bef-5785819f1119

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfExperienceAttribution
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c : ℝ) : pfExperienceAttribution a c=pfExperienceAttribution a b+pfExperienceAttribution b c := by
  unfold pfExperienceAttribution
  ring
