-- Prove2me | solution 1 for ActuarialValuation.bnProb_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:54.25968+00:00
-- url     : https://prove2.me/submissions/71a8bc32-dfc1-4d2e-af3e-04eab012d3be

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d R : ℝ) (h1 : d < R) (h2 : R < u) : 0 < bnRiskNeutralProb u d R := by
  unfold bnRiskNeutralProb
  exact div_pos (sub_pos.mpr h1) (sub_pos.mpr (lt_trans h1 h2))
