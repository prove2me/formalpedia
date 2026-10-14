-- Prove2me | solution 1 for ActuarialValuation.ctAliveReserve_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:29.677653+00:00
-- url     : https://prove2.me/submissions/d85ded52-3f5f-4633-819b-f1805ba31e83

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (delta mu b death maturity : ℝ) (h : ctRiskRate delta mu ≠ 0) : ctAliveReserve delta mu b death maturity maturity = 0 := by
  simp [ctAliveReserve]
