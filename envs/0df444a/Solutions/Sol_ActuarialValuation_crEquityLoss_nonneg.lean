-- Prove2me | solution 1 for ActuarialValuation.crEquityLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:52:32.680402+00:00
-- url     : https://prove2.me/submissions/828adeb0-bc6a-47af-a52e-1ba0462a6767

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crEquityLoss
open ActuarialValuation

theorem solution(assets debt : ℝ) : 0≤crEquityLoss assets debt := by
  unfold crEquityLoss crDebtPayoff
  linarith [min_le_right assets debt]
