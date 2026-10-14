-- Prove2me | solution 1 for ActuarialValuation.cxMass_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:45:00.709332+00:00
-- url     : https://prove2.me/submissions/c6c2703a-9056-4278-89df-effc7f17bb43

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) : cxMass f (n+1) = cxMass f n + f n := by
  simp [cxMass, Finset.sum_range_succ]
