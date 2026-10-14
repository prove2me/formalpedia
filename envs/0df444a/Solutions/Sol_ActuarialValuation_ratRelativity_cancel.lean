-- Prove2me | solution 1 for ActuarialValuation.ratRelativity_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:33.502304+00:00
-- url     : https://prove2.me/submissions/76d8f994-f9c4-49cd-9248-d77dadb6ee6d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRelativity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c base : ℝ) (hb : base ≠ 0) :
    ratRelativity c base * base = c := by
  unfold ratRelativity
  exact div_mul_cancel₀ c hb
