-- Prove2me | Definitions.Def_SourceProof_95e247e701da3178181c6103
-- name    : SourceProof_95e247e701da3178181c6103
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:32:51.627174+00:00
-- url     : https://prove2.me/theorems/029cf1cf-d4a6-4625-810a-c5152d943b6e
-- title:
--   LevyStochCalc source module: SourceProof_95e247e701da3178181c6103
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.process_eLpNorm_two_right_tendsto` comes from the `LevyStochCalc.Poisson.CompensatedProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F002
import Definitions.Def_SourceProof_278d2487462db88d9db97988
import Definitions.Def_SourceProof_2c4e2697eef458aa9c0dbb56
import Definitions.Def_SourceProof_ae659e073861bb6f13485bb6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

end Process

section Isometry

include hℱ in

theorem _root_.Prove2MeSourceProof.h_95e247e701da3178181c6103 (s : ℝ) :
    Tendsto (fun r => eLpNorm (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r
      - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s) 2 P) (𝓝[>] s) (𝓝 0) := by
  suffices hsq : Tendsto (fun r => ∫⁻ ω,
      (‖(LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r
        - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      (𝓝[>] s) (𝓝 0) by
    have h2 := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr (fun r => ?_)
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  rcases le_or_gt 0 s with hs | hs
  · have hFsq : ∀ {t : ℝ}, 0 ≤ t →
        ∫ ω, (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 ∂P
          = (LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ t).toReal := by
      intro t ht
      have hb := LevyStochCalc.Poisson.Compensated.lintegral_sq_eq_ofReal_integral
        (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
      rw [_root_.Prove2MeSourceProof.h_ae659e073861bb6f13485bb6 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht] at hb
      rw [hb, ENNReal.toReal_ofReal (integral_nonneg fun ω => sq_nonneg _)]
    have hincr : ∀ {r : ℝ}, s ≤ r →
        ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω
          - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          = ENNReal.ofReal ((LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ r).toReal
            - (LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ s).toReal) := by
      intro r hsr
      rw [LevyStochCalc.Poisson.Compensated.lintegral_sq_eq_ofReal_integral
        (g := fun ω => LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω
          - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω)
        ((LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r).sub
          (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s))]
      congr 1
      rw [_root_.Prove2MeSourceProof.h_410f74bc0d5bdc6969bf4ac5
        (_root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
        (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
        (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r) hsr,
        hFsq (hs.trans hsr), hFsq hs]
    have hcont : Tendsto (fun r => (LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ r).toReal
        - (LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ s).toReal) (𝓝[>] s) (𝓝 0) := by
      have h0 := (ENNReal.tendsto_toReal (LevyStochCalc.Poisson.Compensated.horizonInt_lt_top φ h_sq_int_global s).ne).comp
        (LevyStochCalc.Poisson.Compensated.horizonInt_right_tendsto φ h_meas h_sq_int_global hs)
      have h1 := h0.sub_const (LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ s).toReal
      rw [sub_self] at h1
      exact h1
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hincr (le_of_lt hr)).symm
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [← lintegral_zero (μ := P)]
    refine lintegral_congr_ae ?_
    filter_upwards [_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hr.2.le,
      _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hs.le] with ω hr0 hs0
    simp [hr0, hs0]
end Isometry

end LevyStochCalc.Poisson.Compensated


