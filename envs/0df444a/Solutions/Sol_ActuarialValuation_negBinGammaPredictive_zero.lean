-- Prove2me | solution 1 for ActuarialValuation.negBinGammaPredictive_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:31.632696+00:00
-- url     : https://prove2.me/submissions/d445d2c9-cb62-4e82-9199-350b5a76a9ea

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (b : ℝ)
  (hr : 0 < r) (hb : 0 < b) :
  negBinGammaPredictive r b 0 =
    (b / (b + 1)) ^ r := by
  have hden : b + 1 ≠ 0 := by
    linarith
  have hcomp : 1 - 1 / (b + 1) = b / (b + 1) := by
    field_simp [hden]
    ring
  simpa [negBinGammaPredictive, negBinCountMass, negBinGammaProbability,
    Nat.choose_zero_right, div_eq_mul_inv] using
    congrArg (fun x : ℝ => x ^ r) hcomp
