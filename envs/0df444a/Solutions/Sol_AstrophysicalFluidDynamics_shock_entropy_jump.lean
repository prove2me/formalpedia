-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_entropy_jump
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:25:35.275539+00:00
-- url     : https://prove2.me/submissions/a22ced6e-fb8f-445a-b055-98e49ffa2d3a

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open Filter Topology

open AstrophysicalFluidDynamics in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂) :
    entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂ =
      Real.log (p₂ / p₁) -
        γ * Real.log (((γ + 1) * (p₂ / p₁) + (γ - 1)) / ((γ - 1) * (p₂ / p₁) + (γ + 1))) := by
  obtain ⟨h1, h2, h3⟩ := hRH
  unfold perfectGasEnthalpy at h3
  have hγ1 : (0:ℝ) < γ - 1 := by linarith
  set m := ρ₁ * u₁ with hm
  have hmpos : 0 < m := mul_pos hρ₁ hu₁
  have e1 : u₁ = m / ρ₁ := by rw [hm]; field_simp
  have e2 : u₂ = m / ρ₂ := by rw [← h1]; field_simp
  rw [h1, e1, e2] at h3
  rw [e1, e2] at h2
  have h3'' := mul_left_cancel₀ hmpos.ne' h3
  have hρ₁' := hρ₁.ne'
  have hρ₂' := hρ₂.ne'
  have hγ1' := hγ1.ne'
  have A : (γ - 1) * m ^ 2 * (ρ₁ ^ 2 - ρ₂ ^ 2) = 2 * γ * ρ₁ * ρ₂ * (p₁ * ρ₂ - p₂ * ρ₁) := by
    field_simp at h3''
    linear_combination h3''
  have B : m ^ 2 * (ρ₁ - ρ₂) = (p₁ - p₂) * ρ₁ * ρ₂ := by
    field_simp at h2
    linear_combination h2
  have E : ρ₁ * ρ₂ * ((γ - 1) * (p₁ - p₂) * (ρ₁ + ρ₂) - 2 * γ * (p₁ * ρ₂ - p₂ * ρ₁)) = 0 := by
    linear_combination (-(γ - 1) * (ρ₁ + ρ₂)) * B + A
  have E' : (γ - 1) * (p₁ - p₂) * (ρ₁ + ρ₂) - 2 * γ * (p₁ * ρ₂ - p₂ * ρ₁) = 0 := by
    rcases mul_eq_zero.mp E with h | h
    · exact absurd h (mul_pos hρ₁ hρ₂).ne'
    · exact h
  have hden : 0 < (γ - 1) * (p₂ / p₁) + (γ + 1) := by positivity
  have key : ρ₂ / ρ₁ = ((γ + 1) * (p₂ / p₁) + (γ - 1)) / ((γ - 1) * (p₂ / p₁) + (γ + 1)) := by
    rw [div_eq_div_iff hρ₁' hden.ne']
    field_simp
    linear_combination (-1:ℝ) * E'
  unfold entropyJumpOverCv
  rw [key]
