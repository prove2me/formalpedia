-- Prove2me | solution 1 for ActuarialValuation.crEquityPayoff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:00:56.802301+00:00
-- url     : https://prove2.me/submissions/5a9d2e6d-480c-49ef-bc16-726090c8a279

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crEquityPayoff
open ActuarialValuation

theorem solution(assets debt : ℝ) : 0≤crEquityPayoff assets debt := by
  unfold crEquityPayoff
  exact le_max_left _ _
