-- Prove2me | solution 1 for ActuarialValuation.pucUnfundedLiability_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:26:32.873381+00:00
-- url     : https://prove2.me/submissions/cf9cf4cc-0b89-4fe1-bbd0-f7b9002b6677

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucUnfundedLiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (al1 al2 assets : ℝ) (h : al1 ≤ al2) : pucUnfundedLiability al1 assets ≤ pucUnfundedLiability al2 assets := by
  unfold pucUnfundedLiability
  exact sub_le_sub_right h assets
