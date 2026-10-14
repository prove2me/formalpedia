-- Prove2me | solution 1 for ActuarialValuation.pvBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:00.38362+00:00
-- url     : https://prove2.me/submissions/c2411f80-0e67-4b65-acbf-0c7c1f36014d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (benefit discount : Fin n → ℝ) (i : Fin n) (hb : 0 ≤ benefit i) (hd : 0 ≤ discount i) : 0 ≤ pvBenefit benefit discount i := by
  unfold pvBenefit
  exact mul_nonneg hb hd
