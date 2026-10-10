-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:44.891172+00:00
-- url     : https://prove2.me/submissions/b1eb807d-9495-4fb7-900b-72c2f8899b3e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinClaimMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ)
  (hw : ∀ k, 0 ≤ w k) (hm : ruinClaimMass w B = 1) :
  ruinProbabilityFinite w B c n u ≤ 1 := by
  induction n generalizing u with
  | zero =>
      by_cases hu : u < 0 <;> simp [ruinProbabilityFinite, hu]
  | succ n ih =>
      by_cases hu : u < 0
      · simp [ruinProbabilityFinite, hu]
      · simp only [ruinProbabilityFinite, if_neg hu]
        calc
          (∑ k ∈ Finset.range (B + 1),
              w k * ruinProbabilityFinite w B c n
                (ruinNextSurplus u c k))
              ≤ ∑ k ∈ Finset.range (B + 1), w k := by
                apply Finset.sum_le_sum
                intro k hk
                simpa using mul_le_mul_of_nonneg_left
                  (ih (ruinNextSurplus u c k)) (hw k)
          _ = 1 := by simpa [ruinClaimMass] using hm
