-- Prove2me | solution 1 for ActuarialValuation.cm1DeferredDeath_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:06:57.063297+00:00
-- url     : https://prove2.me/submissions/e4f7905d-2a38-46c0-b1d2-bc6a3ddd7a00

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1DeferredDeath
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x k n : ℕ) (hx : l x ≠ 0) (hk : l (x+k) ≠ 0) :
    cm1DeferredDeath l x k n = (l (x+k) - l (x+k+n)) / l x := by
  unfold cm1DeferredDeath cm1LifeMortality cm1LifeSurvival
  have ht : (l (x + k) / l x) * (l (x + k + n) / l (x + k)) =
      l (x + k + n) / l x := by
    simp only [div_eq_mul_inv]
    calc
      (l (x+k) * (l x)⁻¹) * (l (x+k+n) * (l (x+k))⁻¹) =
          (l (x+k) * (l (x+k))⁻¹) * (l (x+k+n) * (l x)⁻¹) := by ring
      _ = l (x+k+n) * (l x)⁻¹ := by
        rw [mul_inv_cancel₀ hk]
        ring
  rw [mul_sub, mul_one, ht, sub_div]
