-- Prove2me | solution 1 for ActuarialValuation.pvPremium_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:22.987624+00:00
-- url     : https://prove2.me/submissions/a4e9a1c4-9eac-4a57-8daa-449d1a445029

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (annuity : Fin n → ℝ) (p a : ℝ) (i : Fin n) : pvPremium annuity (a*p) i = a * pvPremium annuity p i := by
  unfold pvPremium
  ring
