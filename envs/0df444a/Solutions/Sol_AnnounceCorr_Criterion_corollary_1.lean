-- Prove2me | solution 1 for AnnounceCorr.Criterion.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:55:13.069577+00:00
-- url     : https://prove2.me/submissions/244be2ec-3510-4345-aad2-b9c739a8c095

import Mathlib
import Definitions.Def_AnnounceCorr_Criterion_Defs

set_option autoImplicit false
open MeasureTheory ProbabilityTheory AnnounceCorr.Criterion

private lemma ac_mse_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W P : Ω → ℝ) (hW : MemLp W 2 μ) (hP : MemLp P 2 μ) :
    mse μ W P = Var[W; μ] - 2 * cov[W, P; μ] + Var[P; μ]
      + ((∫ ω, W ω ∂μ) - ∫ ω, P ω ∂μ) ^ 2 := by
  have h1 : Var[W - P; μ] = Var[W; μ] - 2 * cov[W, P; μ] + Var[P; μ] := variance_sub hW hP
  have h2 := variance_eq_sub (μ := μ) (hW.sub hP)
  have h3 : ∫ ω, (W - P) ω ∂μ = (∫ ω, W ω ∂μ) - ∫ ω, P ω ∂μ :=
    integral_sub (hW.integrable (by norm_num)) (hP.integrable (by norm_num))
  have h4 : mse μ W P = μ[(W - P) ^ 2] := by
    simp [mse, Pi.pow_apply]
  rw [h4]
  have h5 : μ[(W - P) ^ 2] = Var[W - P; μ] + (μ[W - P]) ^ 2 := by linarith
  rw [h5, h1]
  have : μ[W - P] = (∫ ω, W ω ∂μ) - ∫ ω, P ω ∂μ := h3
  rw [this]

private lemma ac_cov_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W P : Ω → ℝ) (hP : MemLp P 2 μ) (h : Var[P; μ] = 0) :
    cov[P, W; μ] = 0 := by
  have := ae_eq_integral_of_variance_eq_zero hP h
  unfold covariance
  apply integral_eq_zero_of_ae
  filter_upwards [this] with ω hω
  simp [hω]

private lemma ac_expansion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (WD P : Ω → ℝ) (hWD : MemLp WD 2 μ)
    (hP : MemLp P 2 μ) (hVarPos : 0 < Var[WD; μ])
    (γ β : ℝ) (hβ : 0 ≤ β)
    (hMean : ∫ ω, P ω ∂μ = γ * ∫ ω, WD ω ∂μ)
    (hVar : Var[P; μ] = β * Var[WD; μ]) :
    mse μ WD P = Var[P; μ] + Var[WD; μ] +
      (γ - 1) ^ 2 * (∫ ω, WD ω ∂μ) ^ 2 -
      2 * corr μ P WD * Real.sqrt β * Var[WD; μ] := by
  rw [ac_mse_eq μ WD P hWD hP, hMean, covariance_comm]
  have hc : cov[P, WD; μ] = corr μ P WD * Real.sqrt β * Var[WD; μ] := by
    rcases hβ.eq_or_lt with h0 | hpos
    · subst h0
      have : Var[P; μ] = 0 := by rw [hVar]; ring
      rw [ac_cov_zero μ WD P hP this]; simp
    · have hs : Real.sqrt (Var[P; μ] * Var[WD; μ]) = Real.sqrt β * Var[WD; μ] := by
        rw [hVar, show β * Var[WD; μ] * Var[WD; μ] = β * Var[WD; μ] ^ 2 by ring,
          Real.sqrt_mul hβ, Real.sqrt_sq hVarPos.le]
      have hne : Real.sqrt β * Var[WD; μ] ≠ 0 :=
        (mul_pos (Real.sqrt_pos.2 hpos) hVarPos).ne'
      unfold corr
      rw [hs]
      field_simp
  rw [hc]
  ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (WD P : Ω → ℝ) (hWD : MemLp WD 2 μ)
    (hP : MemLp P 2 μ) (hVarPos : 0 < Var[WD; μ])
    (hMean : ∫ ω, P ω ∂μ = ∫ ω, WD ω ∂μ)
    (hVar : Var[P; μ] = Var[WD; μ]) :
    mse μ WD (ea μ WD) ≤ mse μ WD P ↔ corr μ P WD ≤ 1 / 2 := by
  have h1 : mse μ WD (ea μ WD) = Var[WD; μ] := by
    unfold mse ea
    exact (variance_eq_integral hWD.aemeasurable).symm
  rw [h1, ac_mse_eq μ WD P hWD hP, hMean, hVar, covariance_comm]
  have hs : Real.sqrt (Var[WD; μ] * Var[WD; μ]) = Var[WD; μ] :=
    Real.sqrt_mul_self hVarPos.le
  unfold corr
  rw [hVar, hs, div_le_iff₀ hVarPos]
  constructor <;> intro h <;> nlinarith
