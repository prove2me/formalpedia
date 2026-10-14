-- Prove2me | solution 1 for ActuarialValuation.bnTwoStep_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:31.463898+00:00
-- url     : https://prove2.me/submissions/65ad1bc6-7932-46bc-8ec2-c2391581ae3a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepPrice

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q uu ud du dd : ℝ) : bnTwoStepPrice R q uu ud du dd = bnTwoStepPrice R q uu du ud dd := by
  unfold bnTwoStepPrice
  ring
