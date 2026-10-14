-- Prove2me | solution 1 for ActuarialValuation.bnRiskNeutralUnique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:33.222386+00:00
-- url     : https://prove2.me/submissions/fce630eb-2508-41c4-ac56-ae2656b6aadb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d R q : ℝ) (hud : u ≠ d) (h : q*u+(1-q)*d=R) : q=bnRiskNeutralProb u d R := by
  unfold bnRiskNeutralProb
  apply (eq_div_iff (sub_ne_zero.mpr hud)).2
  nlinarith [h]
