-- Prove2me | solution 1 for ActuarialValuation.pvAdequacy_above_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:49:30.059258+00:00
-- url     : https://prove2.me/submissions/c633ecb1-f04f-4bf6-acad-fcdec2831607

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf
import Definitions.Def_actuarial_pvLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (P α : ℝ) (hα : α ≤ pvAdequacy p benefit annuity P) : α ≤ pvCdf p (pvLoss benefit annuity P) 0 := by
  simpa [pvAdequacy, pvCdf, pvLoss, pvPremium, sub_nonpos] using hα
