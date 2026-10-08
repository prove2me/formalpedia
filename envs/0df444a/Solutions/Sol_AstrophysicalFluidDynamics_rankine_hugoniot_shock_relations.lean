-- Prove2me | solution 1 for AstrophysicalFluidDynamics.rankine_hugoniot_shock_relations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:31:50.703763+00:00
-- url     : https://prove2.me/submissions/152a6152-9722-4bff-9f79-c9e8c57ed4ce

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open Filter Topology

open AstrophysicalFluidDynamics in
theorem rh19441381_density
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

open AstrophysicalFluidDynamics in
theorem rh19441381_pressure
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

open AstrophysicalFluidDynamics in
theorem rh19441381_machSq (γ ρ u p : ℝ) (hρ : 0 < ρ) (hp : 0 < p) (hγ : 0 < γ) :
    machNumber γ ρ u p ^ 2 = ρ * u ^ 2 / (γ * p) := by
  unfold machNumber soundSpeed soundSpeedSq
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp

open Filter Topology in
open AstrophysicalFluidDynamics in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    ρ₂ / ρ₁ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    u₁ / u₂ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    p₂ / p₁ = shockPressureRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    (machNumber γ ρ₂ u₂ p₂) ^ 2 = shockDownstreamMachSq γ (machNumber γ ρ₁ u₁ p₁) := by
  obtain ⟨hD1, hD2⟩ := rh19441381_density γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ hγ hρ₁ hu₁ hp₁ hρ₂ hu₂ hp₂ hRH hshock
  have hP := rh19441381_pressure γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ hγ hρ₁ hu₁ hp₁ hρ₂ hu₂ hp₂ hRH hshock
  refine ⟨hD1, hD2, hP, ?_⟩
  have h1 : ρ₂ * u₂ = ρ₁ * u₁ := hRH.1
  have hγ0 : 0 < γ := by linarith
  have hM1 := rh19441381_machSq γ ρ₁ u₁ p₁ hρ₁ hp₁ hγ0
  have hM2 := rh19441381_machSq γ ρ₂ u₂ p₂ hρ₂ hp₂ hγ0
  unfold shockDensityRatio at hD2
  unfold shockPressureRatio at hP
  unfold shockDownstreamMachSq
  rw [hM2]
  generalize hm : machNumber γ ρ₁ u₁ p₁ ^ 2 = m at hD2 hP hM1 ⊢
  have hmpos : 0 < m := by rw [hM1]; positivity
  have hA : 0 < (γ - 1) * m + 2 := by nlinarith
  have hg1 : (0:ℝ) < γ + 1 := by linarith
  have hPpos : 0 < (2 * γ * m - (γ - 1)) / (γ + 1) := by rw [← hP]; positivity
  have hB : 0 < 2 * γ * m - (γ - 1) := (div_pos_iff_of_pos_right hg1).mp hPpos
  have E1 : u₁ * ((γ - 1) * m + 2) = u₂ * ((γ + 1) * m) := by
    rw [div_eq_div_iff hu₂.ne' hA.ne'] at hD2; linarith
  have E2 : p₂ * (γ + 1) = p₁ * (2 * γ * m - (γ - 1)) := by
    rw [div_eq_div_iff hp₁.ne' hg1.ne'] at hP; linarith
  have hu2 : u₂ = u₁ * ((γ - 1) * m + 2) / ((γ + 1) * m) := by
    rw [eq_div_iff (by positivity)]; linarith
  have hp2 : p₂ = p₁ * (2 * γ * m - (γ - 1)) / (γ + 1) := by
    rw [eq_div_iff hg1.ne']; linarith
  have hX : ρ₁ = m * (γ * p₁) / u₁ ^ 2 := by
    rw [hM1]; field_simp
  have hY : ρ₂ * u₂ ^ 2 = ρ₁ * u₁ * u₂ := by rw [← h1]; ring
  rw [hY, hp2, hu2, hX]
  have hBn := hB.ne'
  have hAn := hA.ne'
  field_simp
  ring
