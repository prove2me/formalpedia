-- Prove2me | solution 1 for ActuarialValuation.ruMean_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:53.644541+00:00
-- url     : https://prove2.me/submissions/21d9ccab-040b-45e9-966a-1775886b77e2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X Y : Fin m → ℝ) :
    ruMean p (fun ω => X ω + Y ω) = ruMean p X + ruMean p Y := by
  unfold ruMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  exact mul_add _ _ _
