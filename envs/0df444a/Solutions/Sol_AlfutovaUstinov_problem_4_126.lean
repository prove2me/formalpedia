-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_126
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:27.737752+00:00
-- url     : https://prove2.me/submissions/34e184e7-7316-496f-a536-2d8cf44a1488

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x : ℤ) (hx : (p : ℤ) ∣ x ^ 2 + 1) :
    ∃ k : ℕ, p = 4 * k + 1 := by
  have := Fact.mk hp
  have h1 : ((x ^ 2 + 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hx
  push_cast at h1
  have hsq : IsSquare (-1 : ZMod p) := ⟨(x : ZMod p), by linear_combination -h1⟩
  have h3 := ZMod.exists_sq_eq_neg_one_iff.1 hsq
  have h2 : p % 2 = 1 := Nat.odd_iff.1 hodd
  exact ⟨p / 4, by omega⟩
