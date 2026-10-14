-- Prove2me | solution 1 for ActuarialValuation.mackDenominator_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:33:35.271675+00:00
-- url     : https://prove2.me/submissions/beae3dd0-32e1-407f-b44b-5dadf1ed93ac

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackDenominator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) : mackDenominator c (m+1) j = mackDenominator c m j + c m j := by
  simp [mackDenominator, Finset.sum_range_succ]
