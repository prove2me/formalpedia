-- Prove2me | solution 1 for AuditWhistle.Intensity.enforcer_best_response
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:45:32.625028+00:00
-- url     : https://prove2.me/submissions/44aed1bd-db6b-437d-9027-edc0b4a405be

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
set_option autoImplicit false
open AuditWhistle.Intensity

theorem EE_br (M : Model) (q e : ℝ) (hq : 0 ≤ q) :
    IsEnforcerBR M q e ↔ e = min 1 (M.R / M.γ * q) := by
  have hγ := M.hγ
  have hR := M.hR
  set s : ℝ := M.R / M.γ * q with hs
  have hs0 : 0 ≤ s := by positivity
  have hobj : ∀ e' : ℝ, enforcerObj M q e' = M.γ / 2 * (s ^ 2 - (e' - s) ^ 2) := by
    intro e'
    unfold enforcerObj
    rw [hs]
    field_simp
    ring
  have hm : min 1 s ∈ Set.Icc (0:ℝ) 1 := ⟨le_min zero_le_one hs0, min_le_left _ _⟩
  constructor
  · rintro ⟨he, hmax⟩
    have h := hmax _ hm
    rw [hobj, hobj] at h
    have h2 : (e - s) ^ 2 ≤ (min 1 s - s) ^ 2 := by
      have : M.γ / 2 * (s ^ 2 - (min 1 s - s) ^ 2) ≤ M.γ / 2 * (s ^ 2 - (e - s) ^ 2) := h
      have h3 : s ^ 2 - (min 1 s - s) ^ 2 ≤ s ^ 2 - (e - s) ^ 2 := by
        have := (mul_le_mul_iff_of_pos_left (by positivity : (0:ℝ) < M.γ / 2)).1 this
        exact this
      linarith
    obtain ⟨he0, he1⟩ := he
    rcases le_total s 1 with hs1 | hs1
    · rw [min_eq_right hs1] at h2 ⊢
      nlinarith [sq_nonneg (e - s)]
    · rw [min_eq_left hs1] at h2 ⊢
      nlinarith [sq_nonneg (e - 1)]
  · intro h
    rw [h]
    refine ⟨hm, fun e' he' => ?_⟩
    rw [hobj, hobj]
    have : (min 1 s - s) ^ 2 ≤ (e' - s) ^ 2 := by
      obtain ⟨he0, he1⟩ := he'
      rcases le_total s 1 with hs1 | hs1
      · rw [min_eq_right hs1]; nlinarith [sq_nonneg (e' - s)]
      · rw [min_eq_left hs1]; nlinarith
    have h3 : 0 ≤ M.γ / 2 * ((e' - s) ^ 2 - (min 1 s - s) ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    linarith

theorem solution (M : Model) (τ â : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1)
    (hâ : â ∈ Set.Ioo (0:ℝ) 1) :
    (∀ e : ℝ, IsEnforcerBR M (postW1 M τ â) e ↔
      e = min 1 (M.R / M.γ * ((1 - M.p) * (1 - â) * M.β /
        ((1 - M.p) * (1 - â) * M.β + M.p * (1 - M.β))))) ∧
    (∀ e : ℝ, IsEnforcerBR M (postW0 M τ â) e ↔
      e = M.R / M.γ * ((1 - M.p) * (1 - â) * (1 - M.β * τ) /
        ((1 - M.p) * (1 - â) * (1 - M.β * τ) + M.p * (1 - (1 - M.β) * τ)))) ∧
    (∀ e1 e0 : ℝ, IsEnforcerBR M (postW1 M τ â) e1 → IsEnforcerBR M (postW0 M τ â) e0 →
      e0 < e1) ∧
    postW0 M τ â < 1 - M.p ∧
    (∀ e0 : ℝ, IsEnforcerBR M (postW0 M τ â) e0 → e0 < 1) := by
  have hp0 := M.hp0
  have hp1 := M.hp1
  have hβ0 := M.hβ0
  have hβ1 := M.hβ1
  have hR := M.hR
  have hγ := M.hγ
  have hRγ := M.hRγ
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨hâ0, hâ1⟩ := hâ
  have h1p : 0 < 1 - M.p := by linarith
  have h1a : 0 < 1 - â := by linarith
  have hX : 0 < (1 - M.p) * (1 - â) := mul_pos h1p h1a
  have hbt0 : 0 < M.β * τ := by positivity
  have hbt1 : M.β * τ < 1 := by nlinarith
  have hc0 : 0 < 1 - M.β * τ := by linarith
  have hc1 : 0 < 1 - (1 - M.β) * τ := by nlinarith
  have hb1 : 0 < 1 - M.β := by linarith
  set X := (1 - M.p) * (1 - â) with hXdef
  -- the posteriors in closed form
  have hq1 : postW1 M τ â = X * M.β / (X * M.β + M.p * (1 - M.β)) := by
    unfold postW1 jointBW1 jointGW1
    rw [hXdef]
    have : (1 - M.p) * (1 - â) * M.β + M.p * (1 - M.β) ≠ 0 := by positivity
    field_simp
  have hq0 : postW0 M τ â = X * (1 - M.β * τ) / (X * (1 - M.β * τ) + M.p * (1 - (1 - M.β) * τ)) := by
    unfold postW0 jointBW0 jointGW0
    rw [hXdef]
  have hq1pos : 0 ≤ postW1 M τ â := by rw [hq1]; positivity
  have hq0pos : 0 ≤ postW0 M τ â := by rw [hq0]; positivity
  have hq0lt : postW0 M τ â < 1 - M.p := by
    rw [hq0, div_lt_iff₀ (by positivity)]
    have : (1 - â) * (1 - M.β * τ) < 1 - (1 - M.β) * τ := by nlinarith
    have h2 : M.p * (1 - M.p) * ((1 - â) * (1 - M.β * τ)) < M.p * (1 - M.p) * (1 - (1 - M.β) * τ) :=
      mul_lt_mul_of_pos_left this (by positivity)
    rw [hXdef]; nlinarith
  have hq01 : postW0 M τ â < postW1 M τ â := by
    rw [hq0, hq1, div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (1 - M.β * τ) * (1 - M.β) < M.β * (1 - (1 - M.β) * τ) := by nlinarith
    have h2 : X * M.p * ((1 - M.β * τ) * (1 - M.β)) < X * M.p * (M.β * (1 - (1 - M.β) * τ)) :=
      mul_lt_mul_of_pos_left this (by positivity)
    nlinarith
  have hRq : M.R / M.γ * postW0 M τ â < 1 := by
    have h1 : M.R / M.γ * (1 - M.p) < 1 := by
      have := (lt_div_iff₀ h1p).1 hRγ
      exact this
    have : 0 < M.R / M.γ := by positivity
    nlinarith [mul_lt_mul_of_pos_left hq0lt this]
  have hB1 := fun e => EE_br M (postW1 M τ â) e hq1pos
  have hB0 := fun e => EE_br M (postW0 M τ â) e hq0pos
  have hgq : M.R / M.γ * postW0 M τ â < M.R / M.γ * postW1 M τ â :=
    mul_lt_mul_of_pos_left hq01 (by positivity)
  refine ⟨?_, ?_, ?_, hq0lt, ?_⟩
  · intro e; rw [hB1, hq1]
  · intro e; rw [hB0, min_eq_right hRq.le, hq0]
  · intro e1 e0 h1 h0
    rw [hB1] at h1; rw [hB0] at h0
    rw [h1, h0]
    exact lt_min (lt_of_le_of_lt (min_le_right _ _) hRq)
      (lt_of_le_of_lt (min_le_right _ _) hgq)
  · intro e0 h0
    rw [hB0] at h0
    rw [h0]
    exact lt_of_le_of_lt (min_le_right _ _) hRq
