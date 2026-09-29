-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_112
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:44:59.783326+00:00
-- url     : https://prove2.me/submissions/55196933-c93f-46f5-a0f4-a3529fca1802

import Mathlib


theorem solution (n : ℤ) : 11 ∣ n ^ 2001 - n ^ 4 ↔ n ≡ 0 [ZMOD 11] ∨ n ≡ 1 [ZMOD 11] := by
  have hdec : ∀ x : ZMod 11, (x - x ^ 4 = 0 ↔ x = 0 ∨ x = 1) := by decide
  have key : ∀ x : ZMod 11, x ^ 2001 = x := by
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    intro x
    have h11 : x ^ 11 = x := ZMod.pow_card x
    have hm : ∀ m : ℕ, x ^ (10 * m + 1) = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc x ^ (10 * (m + 1) + 1) = x ^ (10 * m) * x ^ 11 := by ring
          _ = x ^ (10 * m) * x := by rw [h11]
          _ = x ^ (10 * m + 1) := by ring
          _ = x := ih
    simpa using hm 200
  have hmod : ∀ x : ZMod 11, (x ^ 2001 - x ^ 4 = 0 ↔ x = 0 ∨ x = 1) := by
    intro x
    rw [key x]
    exact hdec x
  have e : ∀ a : ℤ, (11 : ℤ) ∣ a ↔ (a : ZMod 11) = 0 := by
    intro a
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  have e1 : ∀ a b : ℤ, a ≡ b [ZMOD 11] ↔ (a : ZMod 11) = (b : ZMod 11) := by
    intro a b
    rw [ZMod.intCast_eq_intCast_iff]
    norm_num
  rw [e, e1, e1]
  push_cast
  exact hmod _
