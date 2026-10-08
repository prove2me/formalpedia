-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_pressure_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:06:10.812662+00:00
-- url     : https://prove2.me/submissions/3922fe0a-c2ef-4d7d-baba-da3de8b3175a

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open AstrophysicalFluidDynamics Filter Topology in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    p₂ / p₁ = shockPressureRatio γ (machNumber γ ρ₁ u₁ p₁) := by
  obtain ⟨h1, h2, h3⟩ := hRH
  unfold perfectGasEnthalpy at h3
  have hg : (0:ℝ) < γ - 1 := by linarith
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
  have F : (u₂ - u₁) * (2 * γ * (p₁ + ρ₁ * u₁ ^ 2) - (γ + 1) * (ρ₁ * u₁) * (u₁ + u₂)) = 0 := by
    have hp2 : p₂ = p₁ + ρ₁ * u₁ ^ 2 - ρ₁ * u₁ * u₂ := by
      have : ρ₂ * u₂ ^ 2 = ρ₁ * u₁ * u₂ := by rw [← h1]; ring
      linarith
    rw [hp2] at E
    linear_combination E
  have G : 2 * γ * (p₁ + ρ₁ * u₁ ^ 2) - (γ + 1) * (ρ₁ * u₁) * (u₁ + u₂) = 0 := by
    rcases mul_eq_zero.mp F with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h
  have hp2 : p₂ = p₁ + ρ₁ * u₁ ^ 2 - ρ₁ * u₁ * u₂ := by
    have : ρ₂ * u₂ ^ 2 = ρ₁ * u₁ * u₂ := by rw [← h1]; ring
    linarith
  have hM : machNumber γ ρ₁ u₁ p₁ ^ 2 = ρ₁ * u₁ ^ 2 / (γ * p₁) := by
    unfold machNumber soundSpeed soundSpeedSq
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  unfold shockPressureRatio
  rw [hM, hp2]
  have hγ0 : (0:ℝ) < γ := by linarith
  rw [div_eq_div_iff hp₁.ne' (by linarith : (γ + 1) ≠ 0)]
  have hK : 2 * γ * (ρ₁ * u₁ ^ 2 / (γ * p₁)) * p₁ = 2 * ρ₁ * u₁ ^ 2 := by
    field_simp
  linear_combination G - hK
