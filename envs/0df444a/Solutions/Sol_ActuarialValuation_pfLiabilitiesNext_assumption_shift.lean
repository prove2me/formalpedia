-- Prove2me | solution 1 for ActuarialValuation.pfLiabilitiesNext_assumption_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:32:03.565896+00:00
-- url     : https://prove2.me/submissions/c5b46773-c743-403f-9f16-9b4b56bdeeb8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfLiabilitiesNext
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (liability s i b experience extra : ℝ) : pfLiabilitiesNext liability s i b (experience+extra)=pfLiabilitiesNext liability s i b experience+extra := by
  unfold pfLiabilitiesNext
  ring
