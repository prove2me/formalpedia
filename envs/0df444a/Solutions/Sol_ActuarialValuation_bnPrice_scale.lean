-- Prove2me | solution 1 for ActuarialValuation.bnPrice_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:37.599673+00:00
-- url     : https://prove2.me/submissions/872d4b82-496c-4bd2-a4ea-6de8161885ae

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q xu xd c : ℝ) : bnOnePeriodPrice R q (c*xu) (c*xd) = c*bnOnePeriodPrice R q xu xd := by
  unfold bnOnePeriodPrice bnExpectedPayoff
  ring
