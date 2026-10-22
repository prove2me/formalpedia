-- Prove2me | solution 1 for AdDataSharing.Topics.proposition_7_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:20:41.075001+00:00
-- url     : https://prove2.me/submissions/d847247a-ac93-4b6a-9aa3-e3f511e3ea16

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

set_option autoImplicit false

open AdDataSharing.Topics
open AdDataSharing.Base (Exchange)

lemma adt_forall (p : Exchange → Prop) : (∀ y, p y) ↔ p .adx1 ∧ p .adx2 := by
  constructor
  · intro h; exact ⟨h _, h _⟩
  · rintro ⟨h1, h2⟩ y; cases y <;> assumption

lemma adt_ne_iff (P : Params) (x y : Exchange) :
    IsNE P x y ↔ ((payoff P .adx1 y ≤ payoff P x y ∧ payoff P .adx2 y ≤ payoff P x y) ∧
      (payoff P .adx1 x ≤ payoff P y x ∧ payoff P .adx2 x ≤ payoff P y x)) := by
  have : IsNE P x y ↔ (∀ y₁ : Exchange, payoff P y₁ y ≤ payoff P x y) ∧
      (∀ y₂ : Exchange, payoff P y₂ x ≤ payoff P y x) := Iff.rfl
  rw [this, adt_forall, adt_forall]

lemma adt_dn (P : Params) (hP : P.Standing) : 0 < P.τ * (1 + P.η₂) - P.σ * (1 - P.α) := by
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  nlinarith [mul_nonneg hσ0 hα0.le, mul_pos (sub_pos.2 hτ) (by linarith : (0:ℝ) < 1 + P.η₂)]

lemma adt_p11 (P : Params) : payoff P .adx1 .adx1 = (1 + P.η₂) * (P.C - P.τ * P.w) := rfl
lemma adt_p22 (P : Params) : payoff P .adx2 .adx2 =
    P.σ * (P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w) := rfl
lemma adt_p12 (P : Params) : payoff P .adx1 .adx2 =
    (1 + P.η₂) * P.M - P.σ * (1 - P.α) * (P.M - P.C) - (1 + P.η₂) * P.τ * P.w := rfl
lemma adt_p21 (P : Params) : payoff P .adx2 .adx1 = P.σ * (1 - P.α) * (P.C - P.w) := rfl

lemma adt_ne11 (P : Params) :
    IsNE P .adx1 .adx1 ↔ payoff P .adx2 .adx1 ≤ payoff P .adx1 .adx1 := by
  rw [adt_ne_iff]
  constructor
  · rintro ⟨⟨_, h⟩, _⟩; exact h
  · intro h; exact ⟨⟨le_rfl, h⟩, le_rfl, h⟩

lemma adt_ne22 (P : Params) :
    IsNE P .adx2 .adx2 ↔ payoff P .adx1 .adx2 ≤ payoff P .adx2 .adx2 := by
  rw [adt_ne_iff]
  constructor
  · rintro ⟨⟨h, _⟩, _⟩; exact h
  · intro h; exact ⟨⟨h, le_rfl⟩, h, le_rfl⟩

lemma adt_ne12 (P : Params) :
    IsNE P .adx1 .adx2 ↔ (payoff P .adx2 .adx2 ≤ payoff P .adx1 .adx2 ∧
      payoff P .adx1 .adx1 ≤ payoff P .adx2 .adx1) := by
  rw [adt_ne_iff]
  constructor
  · rintro ⟨⟨_, h1⟩, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨le_rfl, h1⟩, h2, le_rfl⟩

lemma adt_ne21 (P : Params) :
    IsNE P .adx2 .adx1 ↔ (payoff P .adx2 .adx2 ≤ payoff P .adx1 .adx2 ∧
      payoff P .adx1 .adx1 ≤ payoff P .adx2 .adx1) := by
  rw [adt_ne_iff]
  constructor
  · rintro ⟨⟨h2, _⟩, _, h1⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2, le_rfl⟩, le_rfl, h1⟩

lemma adt_tt_eq (P : Params) (hP : P.Standing) :
    tauTilde P = (((1 + P.η₂) - P.σ * (1 - P.α)) * P.C + P.σ * (1 - P.α) * P.w) /
      (P.w * (1 + P.η₂)) := by
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  unfold tauTilde
  have h1 : P.w ≠ 0 := hw0.ne'
  have h2 : (1 + P.η₂) ≠ 0 := by linarith
  field_simp

-- w ≤ w₁  ↔ payoff condition
lemma adt_A_le (P : Params) (hP : P.Standing) :
    payoff P .adx2 .adx1 ≤ payoff P .adx1 .adx1 ↔ P.w ≤ w₁ P := by
  have hd := adt_dn P hP
  unfold w₁
  rw [le_div_iff₀ hd, adt_p21, adt_p11]
  constructor <;> intro h <;> nlinarith

lemma adt_A_lt (P : Params) (hP : P.Standing) :
    payoff P .adx2 .adx1 < payoff P .adx1 .adx1 ↔ P.w < w₁ P := by
  have hd := adt_dn P hP
  unfold w₁
  rw [lt_div_iff₀ hd, adt_p21, adt_p11]
  constructor <;> intro h <;> nlinarith

lemma adt_A_ge (P : Params) (hP : P.Standing) :
    payoff P .adx1 .adx1 ≤ payoff P .adx2 .adx1 ↔ w₁ P ≤ P.w := by
  have hd := adt_dn P hP
  unfold w₁
  rw [div_le_iff₀ hd, adt_p21, adt_p11]
  constructor <;> intro h <;> nlinarith

lemma adt_B_ge (P : Params) (hP : P.Standing) :
    payoff P .adx1 .adx2 ≤ payoff P .adx2 .adx2 ↔ w₂ P ≤ P.w := by
  have hd := adt_dn P hP
  unfold w₂
  rw [div_le_iff₀ hd, adt_p12, adt_p22]
  constructor <;> intro h <;> nlinarith

lemma adt_B_le (P : Params) (hP : P.Standing) :
    payoff P .adx2 .adx2 ≤ payoff P .adx1 .adx2 ↔ P.w ≤ w₂ P := by
  have hd := adt_dn P hP
  unfold w₂
  rw [le_div_iff₀ hd, adt_p12, adt_p22]
  constructor <;> intro h <;> nlinarith

lemma adt_tau_le (P : Params) (hP : P.Standing) :
    payoff P .adx2 .adx1 ≤ payoff P .adx1 .adx1 ↔ P.τ ≤ tauTilde P := by
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  have hP' : P.Standing := ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩
  have hpos : 0 < P.w * (1 + P.η₂) := mul_pos hw0 (by linarith)
  rw [adt_tt_eq P hP', le_div_iff₀ hpos, adt_p21, adt_p11]
  constructor <;> intro h <;> nlinarith

lemma adt_tau_lt (P : Params) (hP : P.Standing) :
    payoff P .adx2 .adx1 < payoff P .adx1 .adx1 ↔ P.τ < tauTilde P := by
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  have hP' : P.Standing := ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩
  have hpos : 0 < P.w * (1 + P.η₂) := mul_pos hw0 (by linarith)
  rw [adt_tt_eq P hP', lt_div_iff₀ hpos, adt_p21, adt_p11]
  constructor <;> intro h <;> nlinarith

lemma adt_tau_ge (P : Params) (hP : P.Standing) :
    payoff P .adx1 .adx1 ≤ payoff P .adx2 .adx1 ↔ tauTilde P ≤ P.τ := by
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  have hP' : P.Standing := ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩
  have hpos : 0 < P.w * (1 + P.η₂) := mul_pos hw0 (by linarith)
  rw [adt_tt_eq P hP', div_le_iff₀ hpos, adt_p21, adt_p11]
  constructor <;> intro h <;> nlinarith

lemma adt_w12 (P : Params) (hP : P.Standing) : w₁ P < w₂ P := by
  have hd := adt_dn P hP
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  unfold w₁ w₂
  rw [div_lt_div_iff_of_pos_right hd]
  have h1 : 0 < (1 + P.η₂ - P.σ) := by linarith
  nlinarith [mul_pos h1 (sub_pos.2 hCM)]

theorem solution (P : Params) (hP : P.Standing) (σ' : ℝ) (hσ'0 : 0 ≤ σ')
    (hσ' : σ' < P.σ) :
    tauTilde P < tauTilde { P with σ := σ' } := by
  obtain ⟨hα0, hα1, hw0, hwC, hCM, hM2C, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  have hw : P.w ≠ 0 := hw0.ne'
  have hη' : (1 + P.η₂) ≠ 0 := by linarith
  have key : ∀ s : ℝ, ((1 + P.η₂) - s * (1 - P.α)) * P.C / (P.w * (1 + P.η₂)) +
      s * (1 - P.α) / (1 + P.η₂) = P.C / P.w - s * (1 - P.α) * (P.C - P.w) / (P.w * (1 + P.η₂)) := by
    intro s; field_simp; ring
  show ((1 + P.η₂) - P.σ * (1 - P.α)) * P.C / (P.w * (1 + P.η₂)) + P.σ * (1 - P.α) / (1 + P.η₂) <
    ((1 + P.η₂) - σ' * (1 - P.α)) * P.C / (P.w * (1 + P.η₂)) + σ' * (1 - P.α) / (1 + P.η₂)
  rw [key, key]
  have hpos : 0 < P.w * (1 + P.η₂) := mul_pos hw0 (by linarith)
  have : 0 < (P.σ - σ') * (1 - P.α) * (P.C - P.w) := mul_pos (mul_pos (sub_pos.2 hσ') (by linarith)) (sub_pos.2 hwC)
  have h2 : P.σ * (1 - P.α) * (P.C - P.w) / (P.w * (1 + P.η₂)) -
      σ' * (1 - P.α) * (P.C - P.w) / (P.w * (1 + P.η₂)) > 0 := by
    rw [← sub_div]
    refine div_pos ?_ hpos
    nlinarith
  linarith
