-- Prove2me | solution 1 for ActuarialValuation.bdStatePV_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:32.520553+00:00
-- url     : https://prove2.me/submissions/a7ae7603-ce5b-4473-ac9f-eb6759b7881f

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p discount X Y : Fin m → ℝ) : bdStatePV p discount (fun ω => X ω + Y ω) = bdStatePV p discount X + bdStatePV p discount Y := by
  unfold bdStatePV
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  ring
