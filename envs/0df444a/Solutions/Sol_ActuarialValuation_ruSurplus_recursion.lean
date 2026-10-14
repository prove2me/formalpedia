-- Prove2me | solution 1 for ActuarialValuation.ruSurplus_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:18:22.252298+00:00
-- url     : https://prove2.me/submissions/d03b03b9-158a-42e5-a970-7ee858d0c575

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (u : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) :
    ruSurplus u G (k+1) ω = ruSurplus u G k ω + G k ω := by
  unfold ruSurplus
  rw [Finset.sum_range_succ]
  ring
