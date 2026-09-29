-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_116
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:05.478986+00:00
-- url     : https://prove2.me/submissions/32fd36f0-81be-4da7-b72b-796e1e260c6c

import Mathlib


theorem solution (a b c d e f : ℤ)
    (h : 13 ∣ a ^ 12 + b ^ 12 + c ^ 12 + d ^ 12 + e ^ 12 + f ^ 12) :
    13 ^ 6 ∣ a * b * c * d * e * f := by
  have cast0 : ∀ x : ℤ, (13 : ℤ) ∣ x ↔ (x : ZMod 13) = 0 := by
    intro x
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  have key : ∀ x : ZMod 13, x ^ 12 = 0 ∨ x ^ 12 = 1 := by decide
  have key0 : ∀ x : ZMod 13, x ^ 12 = 0 → x = 0 := by decide
  have hz := (cast0 _).1 h
  push_cast at hz
  have hall : ∀ u1 u2 u3 u4 u5 u6 : ZMod 13, (u1 = 0 ∨ u1 = 1) → (u2 = 0 ∨ u2 = 1) →
      (u3 = 0 ∨ u3 = 1) → (u4 = 0 ∨ u4 = 1) → (u5 = 0 ∨ u5 = 1) → (u6 = 0 ∨ u6 = 1) →
      u1 + u2 + u3 + u4 + u5 + u6 = 0 →
      u1 = 0 ∧ u2 = 0 ∧ u3 = 0 ∧ u4 = 0 ∧ u5 = 0 ∧ u6 = 0 := by
    intro u1 u2 u3 u4 u5 u6 h1 h2 h3 h4 h5 h6
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
      rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl <;> rcases h6 with rfl | rfl <;>
      decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    hall _ _ _ _ _ _ (key (a : ZMod 13)) (key (b : ZMod 13)) (key (c : ZMod 13))
      (key (d : ZMod 13)) (key (e : ZMod 13)) (key (f : ZMod 13)) hz
  obtain ⟨ka, rfl⟩ := (cast0 a).2 (key0 _ h1)
  obtain ⟨kb, rfl⟩ := (cast0 b).2 (key0 _ h2)
  obtain ⟨kc, rfl⟩ := (cast0 c).2 (key0 _ h3)
  obtain ⟨kd, rfl⟩ := (cast0 d).2 (key0 _ h4)
  obtain ⟨ke, rfl⟩ := (cast0 e).2 (key0 _ h5)
  obtain ⟨kf, rfl⟩ := (cast0 f).2 (key0 _ h6)
  exact ⟨ka * kb * kc * kd * ke * kf, by ring⟩
