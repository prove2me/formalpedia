-- Prove2me | solution 1 for ActuarialValuation.ruRuinProb_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:47:33.150161+00:00
-- url     : https://prove2.me/submissions/05abfe01-9478-41cd-b76a-bbad67a6ea27

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) :
    ruRuinProbability p (fun _ => False) = 0 := by
  first
  | (unfold ruRuinProbability; simp)
  | (simp [ruRuinProbability])
