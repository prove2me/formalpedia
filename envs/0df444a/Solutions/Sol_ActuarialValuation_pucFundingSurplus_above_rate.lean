-- Prove2me | solution 1 for ActuarialValuation.pucFundingSurplus_above_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:26.296977+00:00
-- url     : https://prove2.me/submissions/74ac24d1-87e5-439b-8962-398c2a97e0ce

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pucUnfundedLiability
import Definitions.Def_actuarial_pucAmortisationRate
import Definitions.Def_actuarial_pucFundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a al base c : ℝ) (hb : 0 < base) (h : pucAmortisationRate (pucUnfundedLiability al a) base ≤ c) : 0 ≤ pucFundingSurplus a c base al := by
  have hbase : base ≠ 0 := ne_of_gt hb
  unfold pucAmortisationRate pucUnfundedLiability at h
  unfold pucFundingSurplus
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hb)
  have hcancel : ((al - a) / base) * base = al - a := by
    field_simp [hbase] <;> ring
  rw [hcancel] at hmul
  linarith
