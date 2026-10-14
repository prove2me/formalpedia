-- Prove2me | solution 1 for ActuarialValuation.ruRuinBy_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:35:32.027231+00:00
-- url     : https://prove2.me/submissions/3bb1e915-8b55-4e4a-9d10-4d37401c7f65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruRuinBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruRuinBy u c x (n+1) ↔
      ruRuinBy u c x n ∨ ruRuinAt u c x (n+1) := by
  constructor
  · rintro ⟨k, hk, hru⟩
    by_cases hkn : k ≤ n
    · left
      exact ⟨k, hkn, hru⟩
    · right
      have hnlt : n < k := lt_of_not_ge hkn
      have heq : k = n+1 := le_antisymm hk (Nat.succ_le_iff.mpr hnlt)
      simpa only [heq] using hru
  · intro h
    rcases h with ⟨k, hk, hru⟩ | hru
    · exact ⟨k, le_trans hk (Nat.le_succ n), hru⟩
    · exact ⟨n+1, le_refl _, hru⟩
