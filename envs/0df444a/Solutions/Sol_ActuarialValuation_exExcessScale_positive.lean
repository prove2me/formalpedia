-- Prove2me | solution 1 for ActuarialValuation.exExcessScale_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:44:18.305139+00:00
-- url     : https://prove2.me/submissions/57ff3a3d-63f1-473e-8679-e094cd90a96f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exExcessScale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma threshold : ℝ) (hx : 0≤threshold) (hxi : 0≤xi) (hs : 0<sigma) : 0<exExcessScale xi sigma threshold := by
  unfold exExcessScale
  have hnum : 0 ≤ xi * threshold := mul_nonneg hxi hx
  exact add_pos_of_pos_of_nonneg hs hnum
