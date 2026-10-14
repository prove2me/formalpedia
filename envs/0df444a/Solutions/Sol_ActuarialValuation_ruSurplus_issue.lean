-- Prove2me | solution 1 for ActuarialValuation.ruSurplus_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:30:33.951934+00:00
-- url     : https://prove2.me/submissions/5e44b254-302c-482c-bf2a-64d50a23cc81

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (u : ℝ) (G : ℕ → Fin m → ℝ) (ω : Fin m) :
    ruSurplus u G 0 ω = u := by
  first
  | (unfold ruSurplus; simp)
  | (simp [ruSurplus])
