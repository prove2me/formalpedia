-- Prove2me | solution 1 for ActuarialValuation.ruRuinProb_certain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:52:51.881828+00:00
-- url     : https://prove2.me/submissions/2a4fd47b-077d-4595-980a-91fef87a460f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (hn : (∑ ω : Fin m, p ω) = 1) :
    ruRuinProbability p (fun _ => True) = 1 := by
  first
  | (unfold ruRuinProbability; simp only [if_true]; exact hn)
  | (simp [ruRuinProbability, hn])
