-- Prove2me | solution 1 for ActuarialValuation.ruExponentialSurplus_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:06:08.622325+00:00
-- url     : https://prove2.me/submissions/d5c257ab-21d5-4cad-a74f-af0d65badd18

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruExponentialSurplus
import Definitions.Def_actuarial_ruExponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (u R : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) :
    ruExponentialSurplus u R G (k+1) ω
      = ruExponentialSurplus u R G k ω * ruExponential R (G k ω) := by
  have hS : ruSurplus u G (k+1) ω = ruSurplus u G k ω + G k ω := by
    unfold ruSurplus
    rw [Finset.sum_range_succ]
    ring
  unfold ruExponentialSurplus ruExponential
  rw [hS, mul_add, Real.exp_add]
