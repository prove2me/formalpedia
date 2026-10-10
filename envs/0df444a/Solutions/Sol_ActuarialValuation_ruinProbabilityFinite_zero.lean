-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:42:53.547985+00:00
-- url     : https://prove2.me/submissions/a9f2b1d7-bfc3-441d-bcd2-7fec4f38e780

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c : ℕ) (u : ℤ) :
  ruinProbabilityFinite w B c 0 u = (if u < 0 then 1 else 0) := by
  rfl
