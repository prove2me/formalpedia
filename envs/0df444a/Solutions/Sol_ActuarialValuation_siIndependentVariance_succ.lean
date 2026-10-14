-- Prove2me | solution 1 for ActuarialValuation.siIndependentVariance_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:08:11.451688+00:00
-- url     : https://prove2.me/submissions/f1bd4646-2847-4612-9f5e-7a4453f54725

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siIndependentVariance

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (m s : ℝ) (n : ℕ) : siIndependentVariance m s (n+1)=s*(siIndependentVariance m s n)+(s-m^2)*(m^n)^2 := by
  unfold siIndependentVariance
  simp only [pow_succ]
  ring
