-- Prove2me | solution 1 for ActuarialAnnuities.micro_mass_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:30:24.14529+00:00
-- url     : https://prove2.me/submissions/a4e27107-6ae0-4cd0-bb31-b0e48c276f26

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bUDDMicroMass
open ActuarialAnnuities

theorem solution(h m q : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hm : 0 < m) : 0 ≤ bUDDMicroMass h m p q := by
  unfold bUDDMicroMass
  split_ifs <;> first | exact div_nonneg (hp _) (Nat.cast_nonneg _) | exact hp h | exact le_rfl
