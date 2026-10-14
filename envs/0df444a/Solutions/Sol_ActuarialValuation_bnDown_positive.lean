-- Prove2me | solution 1 for ActuarialValuation.bnDown_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:08.082302+00:00
-- url     : https://prove2.me/submissions/04debe77-63fd-4612-866c-94774c29222d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralDown

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d R : ℝ) (h1 : d < R) (h2 : R < u) : 0 < bnRiskNeutralDown u d R := by
  unfold bnRiskNeutralDown bnRiskNeutralProb
  have hden : 0 < u - d := sub_pos.mpr (lt_trans h1 h2)
  have hq : (R - d) / (u - d) < 1 := (div_lt_one hden).2 (by linarith)
  linarith
