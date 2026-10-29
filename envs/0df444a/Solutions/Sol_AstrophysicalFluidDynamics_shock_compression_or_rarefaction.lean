-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_compression_or_rarefaction
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-29T01:12:24.773066+00:00
-- url     : https://prove2.me/submissions/7683e2d8-2db6-4b7b-b3ad-6ddc99d2b98b

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open Filter Topology
open AstrophysicalFluidDynamics

theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    machNumber γ ρ₁ u₁ p₁ ≠ 1 ∧
    (1 < machNumber γ ρ₁ u₁ p₁ → machNumber γ ρ₂ u₂ p₂ < 1 ∧ ρ₁ < ρ₂ ∧ p₁ < p₂) ∧
    (machNumber γ ρ₁ u₁ p₁ < 1 → 1 < machNumber γ ρ₂ u₂ p₂ ∧ ρ₂ < ρ₁ ∧ p₂ < p₁) := by
  rcases hRH with ⟨hmass, hmom, henergy⟩
  have hγ0 : γ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hγ)
  have hγm1 : γ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hγ)
  have hρ₁0 : ρ₁ ≠ 0 := ne_of_gt hρ₁
  have hρ₂0 : ρ₂ ≠ 0 := ne_of_gt hρ₂
  have hu₁0 : u₁ ≠ 0 := ne_of_gt hu₁
  have hu₂0 : u₂ ≠ 0 := ne_of_gt hu₂
  have hu_ne : u₂ ≠ u₁ := by
    intro hu
    have hrho : ρ₂ = ρ₁ := by
      have hz : (ρ₂ - ρ₁) * u₁ = 0 := by
        rw [hu] at hmass
        nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · linarith
      · exact (hu₁0 hz).elim
    have hp : p₂ = p₁ := by
      rw [hu, hrho] at hmom
      linarith
    apply hshock
    simp [hrho, hu, hp]
  unfold perfectGasEnthalpy at henergy
  field_simp at henergy
  have hmass_u₂ : ρ₂ * u₂ ^ 2 = ρ₁ * u₁ * u₂ := by
    calc
      ρ₂ * u₂ ^ 2 = (ρ₂ * u₂) * u₂ := by ring
      _ = (ρ₁ * u₁) * u₂ := by rw [hmass]
      _ = ρ₁ * u₁ * u₂ := by ring
  have hp_diff : p₂ - p₁ = ρ₁ * u₁ * (u₁ - u₂) := by
    nlinarith [hmom, hmass_u₂]
  have henergy' :
      u₂ * ((γ - 1) * (ρ₁ * u₁) * u₂ + 2 * γ * p₂) =
        u₁ * ((γ - 1) * (ρ₁ * u₁) * u₁ + 2 * γ * p₁) := by
    calc
      u₂ * ((γ - 1) * (ρ₁ * u₁) * u₂ + 2 * γ * p₂) =
          u₂ * (ρ₂ * u₂ ^ 2 * (γ - 1) + 2 * γ * p₂) := by
            rw [hmass_u₂]
            ring
      _ = u₁ * ((γ - 1) * ρ₁ * u₁ ^ 2 + 2 * γ * p₁) := henergy
      _ = u₁ * ((γ - 1) * (ρ₁ * u₁) * u₁ + 2 * γ * p₁) := by ring
  have hp_diff_u₂ := congrArg (fun x : ℝ => x * u₂) hp_diff
  have hfactor :
      (u₂ - u₁) *
          (2 * γ * p₁ + (ρ₁ * u₁) * ((γ - 1) * u₁ - (γ + 1) * u₂)) = 0 := by
    nlinarith [henergy', hp_diff_u₂]
  have hupstream :
      2 * γ * p₁ = ρ₁ * u₁ * ((γ + 1) * u₂ - (γ - 1) * u₁) := by
    rcases mul_eq_zero.mp hfactor with hvel | hbracket
    · exact (hu_ne (sub_eq_zero.mp hvel)).elim
    · nlinarith
  have hp_diff_scaled := congrArg (fun x : ℝ => 2 * γ * x) hp_diff
  have hdownstream :
      2 * γ * p₂ = ρ₁ * u₁ * ((γ + 1) * u₁ - (γ - 1) * u₂) := by
    nlinarith [hupstream, hp_diff_scaled]
  have hγpos : 0 < γ := lt_trans zero_lt_one hγ
  have hs1sqpos : 0 < soundSpeedSq γ p₁ ρ₁ := by
    unfold soundSpeedSq
    positivity
  have hs2sqpos : 0 < soundSpeedSq γ p₂ ρ₂ := by
    unfold soundSpeedSq
    positivity
  have hs1pos : 0 < soundSpeed γ p₁ ρ₁ := by
    rw [soundSpeed]
    exact Real.sqrt_pos.2 hs1sqpos
  have hs2pos : 0 < soundSpeed γ p₂ ρ₂ := by
    rw [soundSpeed]
    exact Real.sqrt_pos.2 hs2sqpos
  have hs1sq : soundSpeed γ p₁ ρ₁ ^ 2 = γ * p₁ / ρ₁ := by
    rw [soundSpeed, Real.sq_sqrt hs1sqpos.le]
    rfl
  have hs2sq : soundSpeed γ p₂ ρ₂ ^ 2 = γ * p₂ / ρ₂ := by
    rw [soundSpeed, Real.sq_sqrt hs2sqpos.le]
    rfl
  have hs1poly : ρ₁ * soundSpeed γ p₁ ρ₁ ^ 2 = γ * p₁ := by
    rw [hs1sq]
    field_simp
  have hs2poly : ρ₂ * soundSpeed γ p₂ ρ₂ ^ 2 = γ * p₂ := by
    rw [hs2sq]
    field_simp
  have hsound_upstream :
      2 * ρ₁ * (soundSpeed γ p₁ ρ₁ ^ 2 - u₁ ^ 2) =
        ρ₁ * u₁ * (γ + 1) * (u₂ - u₁) := by
    calc
      2 * ρ₁ * (soundSpeed γ p₁ ρ₁ ^ 2 - u₁ ^ 2) =
          2 * (ρ₁ * soundSpeed γ p₁ ρ₁ ^ 2) - 2 * ρ₁ * u₁ ^ 2 := by ring
      _ = 2 * (γ * p₁) - 2 * ρ₁ * u₁ ^ 2 := by rw [hs1poly]
      _ = 2 * γ * p₁ - 2 * ρ₁ * u₁ ^ 2 := by ring
      _ = ρ₁ * u₁ * ((γ + 1) * u₂ - (γ - 1) * u₁) - 2 * ρ₁ * u₁ ^ 2 := by
        rw [hupstream]
      _ = ρ₁ * u₁ * (γ + 1) * (u₂ - u₁) := by ring
  have hsound_downstream :
      2 * ρ₂ * (soundSpeed γ p₂ ρ₂ ^ 2 - u₂ ^ 2) =
        ρ₁ * u₁ * (γ + 1) * (u₁ - u₂) := by
    calc
      2 * ρ₂ * (soundSpeed γ p₂ ρ₂ ^ 2 - u₂ ^ 2) =
          2 * (ρ₂ * soundSpeed γ p₂ ρ₂ ^ 2) - 2 * (ρ₂ * u₂ ^ 2) := by ring
      _ = 2 * (γ * p₂) - 2 * (ρ₂ * u₂ ^ 2) := by rw [hs2poly]
      _ = 2 * γ * p₂ - 2 * (ρ₂ * u₂ ^ 2) := by ring
      _ = ρ₁ * u₁ * ((γ + 1) * u₁ - (γ - 1) * u₂) - 2 * (ρ₁ * u₁ * u₂) := by
        rw [hdownstream, hmass_u₂]
      _ = ρ₁ * u₁ * (γ + 1) * (u₁ - u₂) := by ring
  have hfluxpos : 0 < ρ₁ * u₁ := mul_pos hρ₁ hu₁
  have hcoef_up : 0 < ρ₁ * u₁ * (γ + 1) := by positivity
  have hM1ne : machNumber γ ρ₁ u₁ p₁ ≠ 1 := by
    intro hM1
    have hquot : u₁ / soundSpeed γ p₁ ρ₁ = 1 := by
      simpa [machNumber] using hM1
    have hus : u₁ = soundSpeed γ p₁ ρ₁ :=
      (div_eq_one_iff_eq hs1pos.ne').mp hquot
    have hz : (ρ₁ * u₁ * (γ + 1)) * (u₂ - u₁) = 0 := by
      have hsound0 := hsound_upstream
      rw [← hus] at hsound0
      simpa only [sub_self, mul_zero] using hsound0.symm
    have hdu : u₂ - u₁ = 0 := (mul_eq_zero.mp hz).resolve_left hcoef_up.ne'
    exact hu_ne (sub_eq_zero.mp hdu)
  refine ⟨hM1ne, ?_, ?_⟩
  · intro hM1
    have hquot : 1 < u₁ / soundSpeed γ p₁ ρ₁ := by
      simpa [machNumber] using hM1
    have hs1ltu1 : soundSpeed γ p₁ ρ₁ < u₁ :=
      (one_lt_div hs1pos).mp hquot
    have hsq1 : soundSpeed γ p₁ ρ₁ ^ 2 < u₁ ^ 2 :=
      (sq_lt_sq₀ hs1pos.le hu₁.le).2 hs1ltu1
    have hu2ltu1 : u₂ < u₁ := by
      by_contra hnot
      have hdu : 0 ≤ u₂ - u₁ := sub_nonneg.mpr (le_of_not_gt hnot)
      have hprod : 0 ≤ (ρ₁ * u₁ * (γ + 1)) * (u₂ - u₁) :=
        mul_nonneg hcoef_up.le hdu
      have hleft :
          2 * ρ₁ * (soundSpeed γ p₁ ρ₁ ^ 2 - u₁ ^ 2) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos zero_lt_two hρ₁) (sub_neg.mpr hsq1)
      rw [hsound_upstream] at hleft
      exact (not_lt_of_ge hprod) hleft
    have hright2 : 0 < (ρ₁ * u₁ * (γ + 1)) * (u₁ - u₂) :=
      mul_pos hcoef_up (sub_pos.mpr hu2ltu1)
    have hsq2 : u₂ ^ 2 < soundSpeed γ p₂ ρ₂ ^ 2 := by
      rw [← hsound_downstream] at hright2
      exact sub_pos.mp
        (pos_of_mul_pos_right hright2 (mul_pos zero_lt_two hρ₂).le)
    have hu2lts2 : u₂ < soundSpeed γ p₂ ρ₂ :=
      (sq_lt_sq₀ hu₂.le hs2pos.le).1 hsq2
    have hM2 : machNumber γ ρ₂ u₂ p₂ < 1 := by
      rw [machNumber]
      exact (div_lt_one hs2pos).2 hu2lts2
    have hrho : ρ₁ < ρ₂ := by
      by_contra hnot
      have hrle : ρ₂ ≤ ρ₁ := le_of_not_gt hnot
      have hmul : ρ₂ * u₂ < ρ₁ * u₁ :=
        calc
          ρ₂ * u₂ < ρ₂ * u₁ := mul_lt_mul_of_pos_left hu2ltu1 hρ₂
          _ ≤ ρ₁ * u₁ := mul_le_mul_of_nonneg_right hrle hu₁.le
      rw [hmass] at hmul
      exact (lt_irrefl _ hmul)
    have hp : p₁ < p₂ := by
      have : 0 < p₂ - p₁ := by
        rw [hp_diff]
        exact mul_pos hfluxpos (sub_pos.mpr hu2ltu1)
      exact sub_pos.mp this
    exact ⟨hM2, hrho, hp⟩
  · intro hM1
    have hquot : u₁ / soundSpeed γ p₁ ρ₁ < 1 := by
      simpa [machNumber] using hM1
    have hu1lts1 : u₁ < soundSpeed γ p₁ ρ₁ :=
      (div_lt_one hs1pos).mp hquot
    have hsq1 : u₁ ^ 2 < soundSpeed γ p₁ ρ₁ ^ 2 :=
      (sq_lt_sq₀ hu₁.le hs1pos.le).2 hu1lts1
    have hu1ltu2 : u₁ < u₂ := by
      by_contra hnot
      have hdu : u₂ - u₁ ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hprod : (ρ₁ * u₁ * (γ + 1)) * (u₂ - u₁) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef_up.le hdu
      have hleft :
          0 < 2 * ρ₁ * (soundSpeed γ p₁ ρ₁ ^ 2 - u₁ ^ 2) :=
        mul_pos (mul_pos zero_lt_two hρ₁) (sub_pos.mpr hsq1)
      rw [hsound_upstream] at hleft
      exact (not_lt_of_ge hprod) hleft
    have hright2 : (ρ₁ * u₁ * (γ + 1)) * (u₁ - u₂) < 0 :=
      mul_neg_of_pos_of_neg hcoef_up (sub_neg.mpr hu1ltu2)
    have hsq2 : soundSpeed γ p₂ ρ₂ ^ 2 < u₂ ^ 2 := by
      rw [← hsound_downstream] at hright2
      exact sub_neg.mp
        (neg_of_mul_neg_right hright2 (mul_pos zero_lt_two hρ₂).le)
    have hs2ltu2 : soundSpeed γ p₂ ρ₂ < u₂ :=
      (sq_lt_sq₀ hs2pos.le hu₂.le).1 hsq2
    have hM2 : 1 < machNumber γ ρ₂ u₂ p₂ := by
      rw [machNumber]
      exact (one_lt_div hs2pos).2 hs2ltu2
    have hrho : ρ₂ < ρ₁ := by
      by_contra hnot
      have hrle : ρ₁ ≤ ρ₂ := le_of_not_gt hnot
      have hmul : ρ₁ * u₁ < ρ₂ * u₂ :=
        calc
          ρ₁ * u₁ < ρ₁ * u₂ := mul_lt_mul_of_pos_left hu1ltu2 hρ₁
          _ ≤ ρ₂ * u₂ := mul_le_mul_of_nonneg_right hrle hu₂.le
      rw [hmass] at hmul
      exact (lt_irrefl _ hmul)
    have hp : p₂ < p₁ := by
      have : p₂ - p₁ < 0 := by
        rw [hp_diff]
        exact mul_neg_of_pos_of_neg hfluxpos (sub_neg.mpr hu1ltu2)
      exact sub_neg.mp this
    exact ⟨hM2, hrho, hp⟩
