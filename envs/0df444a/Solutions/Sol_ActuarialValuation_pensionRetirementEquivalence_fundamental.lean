-- Prove2me | solution 1 for ActuarialValuation.pensionRetirementEquivalence_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:19.722581+00:00
-- url     : https://prove2.me/submissions/bed26083-e8cb-42dc-8c38-79ea330bef49

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyAdjustedValue
import Definitions.Def_actuarial_pensionLatePostponedValue
import Definitions.Def_actuarial_pensionLatePureFactor
import Definitions.Def_actuarial_pensionLateTotalMultiplier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (E Ae N D p v m Al : ℝ)
  (hAe : Ae ≠ 0) (hden : p * v * m * Al ≠ 0) :
  (pensionEarlyAdjustedValue E Ae = E) ∧
  (pensionLatePostponedValue D p v m Al (pensionLatePureFactor N D p v m Al) = N) ∧
  (D + p * v * Al * pensionLateTotalMultiplier m (pensionLatePureFactor N D p v m Al) = N) := by
  refine ⟨?_, ?_, ?_⟩
  · change (E / Ae) * Ae = E
    field_simp [hAe] <;> ring
  · let c : ℝ := p * v * m * Al
    have hc : c ≠ 0 := hden
    change D + c * ((N - D) / c) = N
    have hcancel : ((N - D) / c) * c = N - D :=
      (eq_div_iff hc).mp rfl
    calc
      D + c * ((N - D) / c) = D + ((N - D) / c) * c := by ring
      _ = D + (N - D) := by rw [hcancel]
      _ = N := by ring
  · let c : ℝ := p * v * m * Al
    have hc : c ≠ 0 := hden
    change D + p * v * Al * (m * ((N - D) / c)) = N
    have hcancel : ((N - D) / c) * c = N - D :=
      (eq_div_iff hc).mp rfl
    calc
      D + p * v * Al * (m * ((N - D) / c)) =
        D + ((N - D) / c) * c := by dsimp [c]; ring
      _ = D + (N - D) := by rw [hcancel]
      _ = N := by ring
