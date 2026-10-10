-- Prove2me | solution 1 for ActuarialValuation.pensionLatePostponedValue_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:57.317764+00:00
-- url     : https://prove2.me/submissions/715dca9c-6d75-4fa7-88cd-c739a0560c1d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePostponedValue
import Definitions.Def_actuarial_pensionLatePureFactor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N D p v m A : ℝ)
  (hden : p * v * m * A ≠ 0) :
  pensionLatePostponedValue D p v m A (pensionLatePureFactor N D p v m A) = N := by
  let c : ℝ := p * v * m * A
  have hc : c ≠ 0 := hden
  change D + c * ((N - D) / c) = N
  have hcancel : ((N - D) / c) * c = N - D :=
    (eq_div_iff hc).mp rfl
  calc
    D + c * ((N - D) / c) = D + ((N - D) / c) * c := by ring
    _ = D + (N - D) := by rw [hcancel]
    _ = N := by ring
