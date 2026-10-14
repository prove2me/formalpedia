-- Prove2me | solution 1 for ActuarialValuation.pfAggregateRate_fund_increases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:24:02.09265+00:00
-- url     : https://prove2.me/submissions/63a1cccc-e12d-460e-9c09-fe7eb7643e1a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAggregateRate
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit asset1 asset2 payroll : ℝ) (h : asset1≤asset2) (hp : 0<payroll) : pfAggregateRate benefit asset2 payroll≤pfAggregateRate benefit asset1 payroll := by
  unfold pfAggregateRate
  exact div_le_div_of_nonneg_right (by linarith) hp.le
