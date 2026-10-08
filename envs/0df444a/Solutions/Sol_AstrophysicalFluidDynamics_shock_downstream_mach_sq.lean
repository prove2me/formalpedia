-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_downstream_mach_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:07:48.089113+00:00
-- url     : https://prove2.me/submissions/c455e030-d5f8-4ecd-a433-7a5417b16b05

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open AstrophysicalFluidDynamics Filter Topology in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    (machNumber γ ρ₂ u₂ p₂) ^ 2 = shockDownstreamMachSq γ (machNumber γ ρ₁ u₁ p₁) := by
  obtain ⟨h1, h2, h3⟩ := hRH
  unfold perfectGasEnthalpy at h3
  have hg : (0:ℝ) < γ - 1 := by linarith
  have hγ0 : (0:ℝ) < γ := by linarith
  have hE2 : 2 * (γ - 1) * (ρ₂ * u₂ * (u₂ ^ 2 / 2 + γ / (γ - 1) * (p₂ / ρ₂)))
      = (γ - 1) * (ρ₂ * u₂) * u₂ ^ 2 + 2 * γ * p₂ * u₂ := by
    field_simp
  have hE1 : 2 * (γ - 1) * (ρ₁ * u₁ * (u₁ ^ 2 / 2 + γ / (γ - 1) * (p₁ / ρ₁)))
      = (γ - 1) * (ρ₁ * u₁) * u₁ ^ 2 + 2 * γ * p₁ * u₁ := by
    field_simp
  have E : (γ - 1) * (ρ₁ * u₁) * u₂ ^ 2 + 2 * γ * p₂ * u₂
      = (γ - 1) * (ρ₁ * u₁) * u₁ ^ 2 + 2 * γ * p₁ * u₁ := by
    rw [← h1, ← hE2, h3, hE1, h1]
  have hu : u₂ ≠ u₁ := by
    intro he
    apply hshock
    have hr : ρ₂ = ρ₁ := by
      rw [he] at h1
      exact mul_right_cancel₀ hu₁.ne' h1
    have hp : p₂ = p₁ := by
      rw [he, hr] at h2; linarith
    rw [hr, he, hp]
  have hA : ρ₂ * u₂ ^ 2 = ρ₁ * u₁ * u₂ := by rw [← h1]; ring
  have hp2 : p₂ = p₁ + ρ₁ * u₁ ^ 2 - ρ₁ * u₁ * u₂ := by linarith
  have F : (u₂ - u₁) * (2 * γ * (p₁ + ρ₁ * u₁ ^ 2) - (γ + 1) * (ρ₁ * u₁) * (u₁ + u₂)) = 0 := by
    rw [hp2] at E
    linear_combination E
  have G : 2 * γ * (p₁ + ρ₁ * u₁ ^ 2) - (γ + 1) * (ρ₁ * u₁) * (u₁ + u₂) = 0 := by
    rcases mul_eq_zero.mp F with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h
  have hM1 : machNumber γ ρ₁ u₁ p₁ ^ 2 = ρ₁ * u₁ ^ 2 / (γ * p₁) := by
    unfold machNumber soundSpeed soundSpeedSq
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hM2 : machNumber γ ρ₂ u₂ p₂ ^ 2 = ρ₂ * u₂ ^ 2 / (γ * p₂) := by
    unfold machNumber soundSpeed soundSpeedSq
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  unfold shockDownstreamMachSq
  rw [hM1, hM2]
  set X := ρ₁ * u₁ ^ 2 / (γ * p₁) with hXdef
  have hX : X * (γ * p₁) = ρ₁ * u₁ ^ 2 := by
    rw [hXdef]; field_simp
  have hden : (2 * γ * X - (γ - 1)) * p₁ = (γ + 1) * p₂ := by
    have hX' : γ * X * p₁ = ρ₁ * u₁ ^ 2 := by linear_combination hX
    rw [hp2]
    linear_combination 2 * hX' - G
  have hD : 2 * γ * X - (γ - 1) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hden
    nlinarith
  rw [div_eq_div_iff (by positivity) hD]
  have key : (ρ₂ * u₂ ^ 2 * (2 * γ * X - (γ - 1))) * (γ * p₁)
      = ((2 + (γ - 1) * X) * (γ * p₂)) * (γ * p₁) := by
    linear_combination (2 * γ * (ρ₂ * u₂ ^ 2) - γ * (γ - 1) * p₂) * hX
      + (2 * γ * (ρ₁ * u₁ ^ 2) - (γ - 1) * γ * p₁) * hA
      - γ * (2 * γ * p₁ + (γ - 1) * (ρ₁ * u₁ ^ 2)) * hp2
      - γ * (ρ₁ * u₁ ^ 2 + p₁) * G
  exact mul_right_cancel₀ (by positivity) key
