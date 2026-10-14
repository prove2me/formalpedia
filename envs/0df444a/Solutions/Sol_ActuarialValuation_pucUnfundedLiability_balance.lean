-- Prove2me | solution 1 for ActuarialValuation.pucUnfundedLiability_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.701998+00:00
-- url     : https://prove2.me/submissions/c99c33bb-a838-4807-829f-6763c9b432c3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pucUnfundedLiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (al assets : ℝ) : pucUnfundedLiability al assets + assets = al := by
  unfold pucUnfundedLiability
  ring
