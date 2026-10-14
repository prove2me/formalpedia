-- Prove2me | solution 1 for ActuarialValuation.bnProb_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:56.303807+00:00
-- url     : https://prove2.me/submissions/172b9fa7-e211-4840-b412-33971f3fdb5e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d R : ℝ) (h1 : d < R) (h2 : R < u) : bnRiskNeutralProb u d R < 1 := by
  unfold bnRiskNeutralProb
  apply (div_lt_one (sub_pos.mpr (lt_trans h1 h2))).2
  linarith
