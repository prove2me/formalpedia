-- Prove2me | solution 1 for ActuarialValuation.trancheAdjustedPV_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:33.640559+00:00
-- url     : https://prove2.me/submissions/49650878-a112-43b9-bf02-ef881d96c40f

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_trancheAdjustedPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) (i : ℕ)
  (hA : A i ≠ 0) : trancheAdjustedPV P A D i = P i * D i := by
  dsimp [trancheAdjustedPV, trancheAdjustedPension, trancheIndividualFactor]
  field_simp [hA] <;> ring
