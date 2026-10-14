-- Prove2me | solution 1 for ActuarialValuation.ulSurrenderValue_le_fund
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:24:13.076498+00:00
-- url     : https://prove2.me/submissions/f6678702-b432-414d-8b66-10daa84f9579

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulSurrenderValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fund charge : ℝ) (hf : 0≤fund) (hc : 0≤charge) : ulSurrenderValue fund charge≤fund := by
  unfold ulSurrenderValue
  exact max_le hf (sub_le_self fund hc)
