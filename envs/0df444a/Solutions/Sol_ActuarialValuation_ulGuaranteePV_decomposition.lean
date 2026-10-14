-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteePV_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:23:59.016883+00:00
-- url     : https://prove2.me/submissions/81b0928d-c7da-4445-9672-357a587a7c11

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedPV
import Definitions.Def_actuarial_ulAccountPV
import Definitions.Def_actuarial_ulShortfallPV
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (prob discount account floor : Fin m→ℝ) : ulGuaranteedPV prob discount account floor = ulAccountPV prob discount account + ulShortfallPV prob discount account floor := by
  have hmax (a b : ℝ) : max a b = a + max (b - a) 0 := by
    rcases le_total b a with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
  unfold ulGuaranteedPV ulAccountPV ulShortfallPV
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  change prob ω * discount ω * max (account ω) (floor ω) =
    prob ω * discount ω * account ω +
      prob ω * discount ω * max (floor ω - account ω) 0
  rw [hmax]
  ring
