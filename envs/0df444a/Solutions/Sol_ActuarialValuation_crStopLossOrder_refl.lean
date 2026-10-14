-- Prove2me | solution 1 for ActuarialValuation.crStopLossOrder_refl
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:40.955452+00:00
-- url     : https://prove2.me/submissions/fb9c25b6-6a08-499e-9f45-922f1978c76c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossOrdered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X : Fin n→ℝ) : crStopLossOrdered p X X := by
  unfold crStopLossOrdered
  intro d
  exact le_refl _
