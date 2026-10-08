-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_density_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:17:03.805656+00:00
-- url     : https://prove2.me/submissions/e82eb1b1-dd82-46f4-8065-cda7fbb9bd8a

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open Filter Topology

open AstrophysicalFluidDynamics in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    ρ₂ / ρ₁ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    u₁ / u₂ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) := by
  obtain ⟨h1, h2, h3⟩ := hRH
  have hg1 : γ - 1 ≠ 0 := by linarith
  have e1 : perfectGasEnthalpy γ p₁ ρ₁ * ρ₁ * (γ - 1) = γ * p₁ := by
    unfold perfectGasEnthalpy; field_simp
  have e2 : perfectGasEnthalpy γ p₂ ρ₂ * ρ₂ * (γ - 1) = γ * p₂ := by
    unfold perfectGasEnthalpy; field_simp
  have hG : (u₂ - u₁) * ((γ - 1) * ρ₁ * u₁ * u₁ + 2 * γ * p₁ - (γ + 1) * ρ₁ * u₁ * u₂) = 0 := by
    linear_combination 2 * (γ - 1) * h3 - 2 * u₂ * e2 + 2 * u₁ * e1 - 2 * γ * u₂ * h2
      + (γ + 1) * u₂ ^ 2 * h1
  have hne : u₂ - u₁ ≠ 0 := by
    intro h
    have hu : u₂ = u₁ := by linarith
    subst hu
    have hr : ρ₂ = ρ₁ := by
      have := h1
      exact mul_right_cancel₀ (ne_of_gt hu₂) this
    subst hr
    have hp : p₂ = p₁ := by linarith
    exact hshock (by rw [hp])
  have key : (γ + 1) * ρ₁ * u₁ * u₂ = (γ - 1) * ρ₁ * u₁ * u₁ + 2 * γ * p₁ := by
    have := (mul_eq_zero.mp hG).resolve_left hne
    linarith
  have hM : machNumber γ ρ₁ u₁ p₁ ^ 2 = ρ₁ * u₁ ^ 2 / (γ * p₁) := by
    unfold machNumber soundSpeed soundSpeedSq
    have hpos : 0 ≤ γ * p₁ / ρ₁ := by positivity
    rw [div_pow, Real.sq_sqrt hpos]
    field_simp
  have hρ2 : ρ₂ = ρ₁ * u₁ / u₂ := by
    field_simp; linarith
  have hγ0 : 0 < γ := by linarith
  have hden : (γ - 1) * (ρ₁ * u₁ ^ 2) + 2 * (γ * p₁) ≠ 0 := by
    have : 0 < (γ - 1) * (ρ₁ * u₁ ^ 2) := by
      apply mul_pos <;> [linarith; positivity]
    positivity
  have hR : u₁ / u₂ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) := by
    have hgp : γ * p₁ ≠ 0 := by positivity
    have hrw : shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁)
        = (γ + 1) * (ρ₁ * u₁ ^ 2) / ((γ - 1) * (ρ₁ * u₁ ^ 2) + 2 * (γ * p₁)) := by
      unfold shockDensityRatio
      rw [hM]
      field_simp
    rw [hrw, div_eq_div_iff (ne_of_gt hu₂) hden]
    linear_combination (-u₁) * key
  refine ⟨?_, hR⟩
  rw [← hR, hρ2]
  field_simp
