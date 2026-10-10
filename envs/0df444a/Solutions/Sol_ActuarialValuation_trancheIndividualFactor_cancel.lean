-- Prove2me | solution 1 for ActuarialValuation.trancheIndividualFactor_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:10.565933+00:00
-- url     : https://prove2.me/submissions/d68892ec-f726-4d41-9167-fa6b1540f2ba

import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_trancheIndividualFactor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (A D : ℕ → ℝ) (i : ℕ)
  (hA : A i ≠ 0) :
  trancheIndividualFactor A D i * A i = D i := by
  dsimp [trancheIndividualFactor]
  field_simp [hA]
