-- Prove2me | solution 1 for AuditWhistle.Intensity.auditor_best_response
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:26.447639+00:00
-- url     : https://prove2.me/submissions/e0b213bf-d3ad-4e88-a856-8b1678092488

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
set_option autoImplicit false
open AuditWhistle.Intensity

theorem abr_aux_BB (M : Model) (P a : ℝ) (hP : P ∈ Set.Ioc (0:ℝ) 1) :
    IsAuditorBR M P a ↔ a = M.D / M.k * (1 - M.p) * P := by
  have hk := M.hk
  have hD := M.hD
  have hp0 := M.hp0
  have hp1 := M.hp1
  have hDk := M.hDk
  obtain ⟨hP0, hP1⟩ := hP
  set a0 : ℝ := M.D / M.k * (1 - M.p) * P with ha0
  have h1p : 0 < 1 - M.p := by linarith
  have ha0pos : 0 < a0 := by positivity
  have ha0lt : a0 < 1 := by
    have h1 : M.D / M.k * (1 - M.p) < 1 := (lt_div_iff₀ h1p).1 hDk
    calc a0 = M.D / M.k * (1 - M.p) * P := rfl
      _ ≤ M.D / M.k * (1 - M.p) * 1 := by gcongr
      _ < 1 := by linarith
  have hloss : ∀ a' : ℝ, auditorLoss M P a' = auditorLoss M P a0 + M.k / 2 * (a' - a0) ^ 2 := by
    intro a'
    unfold auditorLoss
    have : M.D = M.k * a0 / ((1 - M.p) * P) := by
      rw [ha0]; field_simp
    rw [this]
    field_simp
    ring
  constructor
  · rintro ⟨_, hmin⟩
    have := hmin a0 ⟨ha0pos, ha0lt⟩
    rw [hloss a] at this
    have h2 : M.k / 2 * (a - a0) ^ 2 ≤ 0 := by linarith
    have h3 : (a - a0) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have : 0 < M.k / 2 * (a - a0) ^ 2 := by positivity
      linarith
    have : a - a0 = 0 := by nlinarith [sq_nonneg (a - a0)]
    linarith
  · intro h
    rw [h]
    refine ⟨⟨ha0pos, ha0lt⟩, fun a' _ => ?_⟩
    rw [hloss a']
    have : 0 ≤ M.k / 2 * (a' - a0) ^ 2 := by positivity
    linarith

theorem solution (M : Model) :
    (∀ P a : ℝ, P ∈ Set.Ioc (0:ℝ) 1 →
      (IsAuditorBR M P a ↔ a = M.D / M.k * (1 - M.p) * P)) ∧
    (∀ τ e1 e0 a : ℝ, τ ∈ Set.Ioo (0:ℝ) 1 → e1 ∈ Set.Icc (0:ℝ) 1 → e0 ∈ Set.Ioc (0:ℝ) 1 →
      (IsAuditorBR M (detectProb M τ e1 e0) a ↔
        a = M.D / M.k * (1 - M.p) * (M.β * τ * e1 + (1 - M.β * τ) * e0))) := by
  refine ⟨fun P a hP => abr_aux_BB M P a hP, ?_⟩
  intro τ e1 e0 a hτ he1 he0
  have hβ0 := M.hβ0
  have hβ1 := M.hβ1
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨he10, he11⟩ := he1
  obtain ⟨he00, he01⟩ := he0
  have hbt0 : 0 < M.β * τ := by positivity
  have hbt1 : M.β * τ < 1 := by nlinarith
  have hP : detectProb M τ e1 e0 ∈ Set.Ioc (0:ℝ) 1 := by
    unfold detectProb
    constructor
    · have : 0 < (1 - M.β * τ) * e0 := by apply mul_pos <;> linarith
      nlinarith [mul_nonneg hbt0.le he10]
    · nlinarith [mul_le_mul_of_nonneg_left he11 hbt0.le, mul_le_mul_of_nonneg_left he01 (by linarith : (0:ℝ) ≤ 1 - M.β * τ)]
  rw [abr_aux_BB M _ a hP]
  rfl
