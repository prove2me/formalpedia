-- Prove2me | solution 1 for ActuarialValuation.ruSurplus_initial_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:20:59.737616+00:00
-- url     : https://prove2.me/submissions/595e887e-f511-483c-8eda-6921de217bf4

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

theorem solution {m : ℕ} (u v : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) :
    ruSurplus (u+v) G k ω = ruSurplus u G k ω + v := by
  unfold ruSurplus
  ring
