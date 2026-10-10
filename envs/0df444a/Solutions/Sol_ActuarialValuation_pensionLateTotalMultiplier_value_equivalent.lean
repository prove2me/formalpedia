-- Prove2me | solution 1 for ActuarialValuation.pensionLateTotalMultiplier_value_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:09.989984+00:00
-- url     : https://prove2.me/submissions/20417346-74d8-4b6e-8b24-aea438ee3ac3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePureFactor
import Definitions.Def_actuarial_pensionLateTotalMultiplier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N D p v m A : ℝ)
  (hden : p * v * m * A ≠ 0) :
  D + p * v * A * pensionLateTotalMultiplier m (pensionLatePureFactor N D p v m A) = N := by
  let c : ℝ := p * v * m * A
  have hc : c ≠ 0 := hden
  change D + p * v * A * (m * ((N - D) / c)) = N
  have hcancel : ((N - D) / c) * c = N - D :=
    (eq_div_iff hc).mp rfl
  calc
    D + p * v * A * (m * ((N - D) / c)) =
      D + ((N - D) / c) * c := by dsimp [c]; ring
    _ = D + (N - D) := by rw [hcancel]
    _ = N := by ring
