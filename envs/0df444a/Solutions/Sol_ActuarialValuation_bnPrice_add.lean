-- Prove2me | solution 1 for ActuarialValuation.bnPrice_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:26.143386+00:00
-- url     : https://prove2.me/submissions/f499f6bd-661a-494e-a13b-5723fe9345c0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q xu xd yu yd : ℝ) : bnOnePeriodPrice R q (xu+yu) (xd+yd) = bnOnePeriodPrice R q xu xd + bnOnePeriodPrice R q yu yd := by
  unfold bnOnePeriodPrice bnExpectedPayoff
  ring
