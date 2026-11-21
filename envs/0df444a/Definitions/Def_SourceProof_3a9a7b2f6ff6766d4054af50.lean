-- Prove2me | Definitions.Def_SourceProof_3a9a7b2f6ff6766d4054af50
-- name    : SourceProof_3a9a7b2f6ff6766d4054af50
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:49:41.945238+00:00
-- url     : https://prove2.me/theorems/30798e28-162d-4218-a0f8-1825c6119ae4
-- title:
--   LevyStochCalc source module: SourceProof_3a9a7b2f6ff6766d4054af50
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stageEval_tendsto` comes from the `LevyStochCalc.Poisson.CompensatedProcessQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral process

The compensated square `t ↦ F_t² − ∫_0^t ∫_E φ(u, e)² ν(de) du` of the `L²` integral process
`F` is a martingale on the filtration `ℱ` of the integral and on its right-continuation `ℱ₊`,
`ℱ₊ t = ⨅ s > t, ℱ s` (no null sets are added). The stage compensated squares are martingales
(`MarkStep.martingale_sq_sub_compensator`) and converge in `L¹` to the compensated square of the
process: the stage integrands converge to `φ` in `L²` of the product measure on
`Ω × [0, t] × E`, so their squares converge in `L¹`, and the `L¹(P)`-distance of the compensators
is dominated by the joint `L¹`-distance.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Compensator

variable (ν : Measure E) (φ : Ω → ℝ → E → ℝ)

end Compensator

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)


theorem _root_.Prove2MeSourceProof.h_3a9a7b2f6ff6766d4054af50 (t : ℝ) :
    Tendsto (fun n => eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => eLpNorm (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) ^ (2 : ℝ))
      atTop (𝓝 0) := by
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ LevyStochCalc.Poisson.Compensated.stageHorizon N₀ := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
      exact ⟨k, hk.le⟩
    have hbound : ∀ n, N₀ ≤ n → eLpNorm (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) ^ (2 : ℝ)
        ≤ LevyStochCalc.Poisson.Compensated.stageErr φ P n (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 := by
      intro n hn
      set G := (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
      have hdm : Measurable (fun p : Ω × ℝ × E =>
          (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
        (ENNReal.continuous_coe.measurable.comp (h_meas.sub G.eval_measurable).nnnorm).pow_const 2
      calc eLpNorm (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
            - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) ^ (2 : ℝ)
          = ∫⁻ p, (‖(LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
              - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) p‖₊ : ℝ≥0∞) ^ 2
              ∂(LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) :=
            LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _
        _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
            rw [← LevyStochCalc.Poisson.Compensated.lintegral_horizonMeasure t
              (fun ω s e => (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hdm]
            refine lintegral_congr fun q => ?_
            rw [Pi.sub_apply, ← nnnorm_neg, neg_sub]
            rfl
        _ ≤ LevyStochCalc.Poisson.Compensated.stageErr φ P n G := lintegral_mono fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (hN₀.trans (LevyStochCalc.Poisson.Compensated.stageHorizon_mono hn)))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp]
    have herr : Tendsto (fun n => LevyStochCalc.Poisson.Compensated.stageErr φ P n
        (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => bot_le)
        (fun n => (LevyStochCalc.Poisson.Compensated.master_err N ℱ φ h_meas h_progMeas h_sq_int_global n).le)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
      (Eventually.of_forall fun _ => bot_le) (eventually_atTop.2 ⟨N₀, hbound⟩)
  have h := hsq.ennrpow_const ((1 : ℝ) / 2)
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine h.congr (fun n => ?_)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
end LevyStochCalc.Poisson.Compensated


