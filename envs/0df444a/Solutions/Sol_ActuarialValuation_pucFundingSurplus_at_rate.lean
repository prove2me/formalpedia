-- Prove2me | solution 1 for ActuarialValuation.pucFundingSurplus_at_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.470133+00:00
-- url     : https://prove2.me/submissions/0276e10d-4e21-4f28-9986-4f28a2e5d2c6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pucUnfundedLiability
import Definitions.Def_actuarial_pucAmortisationRate
import Definitions.Def_actuarial_pucFundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a al base : ℝ) (hb : base ≠ 0) : pucFundingSurplus a (pucAmortisationRate (pucUnfundedLiability al a) base) base al = 0 := by
  unfold pucFundingSurplus pucAmortisationRate pucUnfundedLiability
  field_simp [hb] <;> ring
