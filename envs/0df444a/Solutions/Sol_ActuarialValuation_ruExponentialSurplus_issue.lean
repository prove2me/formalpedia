-- Prove2me | solution 1 for ActuarialValuation.ruExponentialSurplus_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:07:10.237361+00:00
-- url     : https://prove2.me/submissions/45358106-d10a-438f-9fae-13962ed90284

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponentialSurplus
import Definitions.Def_actuarial_ruExponential
import Definitions.Def_actuarial_ruSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (u R : ℝ) (G : ℕ → Fin m → ℝ) (ω : Fin m) :
    ruExponentialSurplus u R G 0 ω = ruExponential R u := by
  first
  | (unfold ruExponentialSurplus ruExponential ruSurplus; simp)
  | (unfold ruExponentialSurplus ruExponential
     have hS : ruSurplus u G 0 ω = u := by
       unfold ruSurplus
       simp
     rw [hS])
