-- Prove2me | Definitions.Def_SourceProof_ae659e073861bb6f13485bb6
-- name    : SourceProof_ae659e073861bb6f13485bb6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:30:22.124369+00:00
-- url     : https://prove2.me/theorems/64315a07-90a7-4bd6-9a96-86e31c03c3c9
-- title:
--   LevyStochCalc source module: SourceProof_ae659e073861bb6f13485bb6
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.process_lintegral_sq` comes from the `LevyStochCalc.Poisson.CompensatedProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F002
import Definitions.Def_SourceProof_711d7a58a27af1d1b25e8dc9
import Definitions.Def_SourceProof_d924d3c21257fe582c3c4d51

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

theorem _root_.Prove2MeSourceProof.h_ae659e073861bb6f13485bb6 {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = horizonInt (P := P) (ν := ν) φ t := by
  set μt := P.prod (ν.prod (volume.restrict (Set.Icc (0 : ℝ) t))) with hμt
  set g : Ω × E × ℝ → ℝ := fun q => φ q.1 q.2.2 q.2.1 with hg
  set gₙ : ℕ → Ω × E × ℝ → ℝ := fun n q =>
    (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval q.2.2 q.2.1 q.1 with hgₙ
  have hswap : Measurable fun q : Ω × E × ℝ => ((q.1, q.2.2, q.2.1) : Ω × ℝ × E) := by fun_prop
  have hgm : Measurable g := h_meas.comp hswap
  have hgₙm : ∀ n, Measurable (gₙ n) := fun n =>
    (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable.comp hswap
  have hφsq : Measurable (fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2
  -- the triple integrals as integrals for `μt`
  have hlift : ∀ (f : Ω → ℝ → E → ℝ≥0∞), Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) →
      ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s e ∂volume ∂ν ∂P
        = ∫⁻ q, f q.1 q.2.2 q.2.1 ∂μt := fun f hf => LevyStochCalc.Poisson.Compensated.triple_eq_lintegral_prod f hf
  -- 1. the stage integrals
  have h1 : ∀ n, ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω‖₊
      : ℝ≥0∞) ^ 2 ∂P = ∫⁻ q, (‖gₙ n q‖₊ : ℝ≥0∞) ^ 2 ∂μt := by
    intro n
    simp only [LevyStochCalc.Poisson.Compensated.stageIntegral]
    rw [(LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.lintegral_integral_sq_at N hℱ
      (LevyStochCalc.Poisson.Compensated.master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n) ht]
    exact hlift (fun ω s e =>
      (‖(LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2)
      ((ENNReal.continuous_coe.measurable.comp
        (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable.nnnorm).pow_const 2)
  -- 2. `gₙ → g` in `L²(μt)`
  have h2 : Tendsto (fun n => eLpNorm (gₙ n - g) 2 μt) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => eLpNorm (gₙ n - g) 2 μt ^ (2 : ℝ)) atTop (𝓝 0) := by
      obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ LevyStochCalc.Poisson.Compensated.stageHorizon N₀ := by
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
        exact ⟨k, hk.le⟩
      have hbound : ∀ n, N₀ ≤ n → eLpNorm (gₙ n - g) 2 μt ^ (2 : ℝ)
          ≤ LevyStochCalc.Poisson.Compensated.stageErr φ P n (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 := by
        intro n hn
        set G := (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
        have hdm : Measurable (fun p : Ω × ℝ × E =>
            (‖G.eval p.2.1 p.2.2 p.1 - φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) :=
          (ENNReal.continuous_coe.measurable.comp
            (G.eval_measurable.sub h_meas).nnnorm).pow_const 2
        rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
          show (fun q => (‖(gₙ n - g) q‖₊ : ℝ≥0∞) ^ 2)
            = fun q : Ω × E × ℝ => (‖G.eval q.2.2 q.2.1 q.1 - φ q.1 q.2.2 q.2.1‖₊ : ℝ≥0∞) ^ 2
            from rfl,
          ← hlift (fun ω s e => (‖G.eval s e ω - φ ω s e‖₊ : ℝ≥0∞) ^ 2) hdm]
        calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖G.eval s e ω - φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
            = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
              refine lintegral_congr fun ω => ?_
              rw [LevyStochCalc.Poisson.Compensated.lintegral_swap_es (fun ω s e => (‖G.eval s e ω - φ ω s e‖₊ : ℝ≥0∞) ^ 2) hdm ω]
              refine lintegral_congr fun s => lintegral_congr fun e => ?_
              rw [← nnnorm_neg, neg_sub]
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
  -- 3. `∫⁻ ‖g‖² ∂μt` is finite (the horizon integral)
  have hgint : ∫⁻ q, (‖g q‖₊ : ℝ≥0∞) ^ 2 ∂μt = LevyStochCalc.Poisson.Compensated.horizonInt (P := P) (ν := ν) φ t := by
    rw [← hlift (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) hφsq, LevyStochCalc.Poisson.Compensated.horizonInt]
    exact lintegral_congr fun ω =>
      LevyStochCalc.Poisson.Compensated.lintegral_swap_es (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) hφsq ω
  have hgfin : eLpNorm g 2 μt ≠ ⊤ := by
    refine ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_).ne
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq, hgint]
    exact LevyStochCalc.Poisson.Compensated.horizonInt_lt_top φ h_sq_int_global t
  have h3 := _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
    (fun n => (hgₙm n).aestronglyMeasurable) hgm.aestronglyMeasurable hgfin h2
  -- 4. the stage integrals converge to the process
  have h4 := _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
    (fun n => (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
      t).aestronglyMeasurable)
    (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).aestronglyMeasurable
    (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).eLpNorm_ne_top
    (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
  simp_rw [h1] at h4
  rw [tendsto_nhds_unique h4 h3, hgint]
end Isometry

end LevyStochCalc.Poisson.Compensated


