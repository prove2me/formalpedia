-- Prove2me | solution 1 for ActuarialValuation.pucFutureNormalCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:10.338824+00:00
-- url     : https://prove2.me/submissions/3a212ed2-9af5-4116-b292-cef78ef5ab54

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucFutureNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n : ℕ) (f : ℝ) : pucFutureNormalCost u n 0 f = 0 := by
  simp [pucFutureNormalCost, pucFutureBenefit]
