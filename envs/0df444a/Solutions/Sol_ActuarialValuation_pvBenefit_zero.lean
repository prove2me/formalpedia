-- Prove2me | solution 1 for ActuarialValuation.pvBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:52:49.389203+00:00
-- url     : https://prove2.me/submissions/1ce50548-f933-42a4-91e8-ed17ae2521f2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (discount : Fin n → ℝ) (i : Fin n) : pvBenefit (fun _ => 0) discount i = 0 := by
  simp [pvBenefit]
