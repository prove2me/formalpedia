-- Prove2me | Definitions.Def_SourceProof_d2f9dc9e3005aab0038c8983
-- name    : SourceProof_d2f9dc9e3005aab0038c8983
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:37:40.114858+00:00
-- url     : https://prove2.me/theorems/8c736e23-376f-4c17-8564-66fac9911fe2
-- title:
--   LevyStochCalc source module: SourceProof_d2f9dc9e3005aab0038c8983
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.process_congr_filtration` comes from the `LevyStochCalc.Brownian.ItoFiltrationChange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F000
import Definitions.Def_SourceProof_7e6dc0a5b3abba2670f5e8de

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The stochastic integrals under a change of filtration

The `L²` Brownian Itô integral and the `L²` Itô–Lévy integral against a compensated Poisson
random measure are each assembled from an approximating sequence of elementary integrands
selected relative to a filtration, so one integrand integrated against one driver over two
filtrations gives two constructions. The elementary integral of such an approximant mentions no
filtration, and the `L²` distance between two elementary integrals, or between an elementary
integral and the limit, is the energy of the difference of the integrands; both constructions
are therefore the `L²`-limit of a single sequence, and they agree almost everywhere. Passing to
the augmented filtration is the case of interest, since that filtration satisfies the usual
conditions.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` — the Brownian
  integral over `ℱ` agrees almost everywhere with the integral over a larger filtration.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration` — the Brownian integral
  over `ℱ` agrees almost everywhere with the integral over `augFiltration ℱ P`.
* `LevyStochCalc.Poisson.Compensated.process_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_augFiltration` — the same three
  statements for the compensated Poisson integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory
open scoped NNReal ENNReal

universe u
universe v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_d2f9dc9e3005aab0038c8983
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (h𝒢 : IsPoissonFiltration N 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable 𝒢 φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    process N ℱ hℱ φ hm hp hq T =ᵐ[P] process N 𝒢 h𝒢 φ hm hp' hq T := by
  rcases le_or_gt T 0 with hT | hT
  · exact (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ φ hm hp hq hT).trans
      (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N 𝒢 h𝒢 φ hm hp' hq hT).symm
  have hbd : ∀ n : ℕ, T ≤ LevyStochCalc.Poisson.Compensated.stageHorizon n →
      ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ hm hp hq n T ω
          - LevyStochCalc.Poisson.Compensated.stageIntegral N 𝒢 φ hm hp' hq n T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n hTn
    have hmax1 : (LevyStochCalc.Poisson.Compensated.master N ℱ φ hm hp hq n).1
        ≤ max (LevyStochCalc.Poisson.Compensated.master N ℱ φ hm hp hq n).1 (LevyStochCalc.Poisson.Compensated.master N 𝒢 φ hm hp' hq n).1 := le_max_left _ _
    have hmax2 : (LevyStochCalc.Poisson.Compensated.master N 𝒢 φ hm hp' hq n).1
        ≤ max (LevyStochCalc.Poisson.Compensated.master N ℱ φ hm hp hq n).1 (LevyStochCalc.Poisson.Compensated.master N 𝒢 φ hm hp' hq n).1 := le_max_right _ _
    set G := (LevyStochCalc.Poisson.Compensated.master N ℱ φ hm hp hq n).2 with hGdef
    set G' := (LevyStochCalc.Poisson.Compensated.master N 𝒢 φ hm hp' hq n).2 with hG'def
    have hG : G.Adapted 𝒢 :=
      (LevyStochCalc.Poisson.Compensated.master_adapted N ℱ φ hm hp hq n).mono_filtration hle
    have hG' : G'.Adapted 𝒢 := LevyStochCalc.Poisson.Compensated.master_adapted N 𝒢 φ hm hp' hq n
    have hRf : (G.dyadicRefine hmax1).Adapted 𝒢 := hG.dyadicRefine N hmax1
    have hRf' : (G'.dyadicRefine hmax2).Adapted 𝒢 := hG'.dyadicRefine N hmax2
    have e1 : ∀ ω, LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ hm hp hq n T ω = G.integral N T ω := fun _ => rfl
    have e2 : ∀ ω, LevyStochCalc.Poisson.Compensated.stageIntegral N 𝒢 φ hm hp' hq n T ω = G'.integral N T ω := fun _ => rfl
    have hae : (fun ω => (‖G.integral N T ω - G'.integral N T ω‖₊ : ℝ≥0∞) ^ 2)
        =ᵐ[P] fun ω => (‖(G.dyadicRefine hmax1).integral N T ω
          - (G'.dyadicRefine hmax2).integral N T ω‖₊ : ℝ≥0∞) ^ 2 := by
      filter_upwards [(fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_c4dfabd4f14ab7a2037da138 p2mMethodArg0 p2mMethodArg1 G) N h𝒢 hmax1 hG T,
        (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_c4dfabd4f14ab7a2037da138 p2mMethodArg0 p2mMethodArg1 G') N h𝒢 hmax2 hG' T] with ω hω hω'
      rw [hω, hω']
    simp_rw [e1, e2]
    rw [lintegral_congr_ae hae,
      (G.dyadicRefine hmax1).lintegral_integral_sub_sq_at N h𝒢 (G'.dyadicRefine hmax2)
        hRf hRf' hT.le]
    have hev : ∀ ω e s, (G.dyadicRefine hmax1).eval s e ω - (G'.dyadicRefine hmax2).eval s e ω
        = G.eval s e ω - G'.eval s e ω := fun ω e s => by
      rw [G.eval_dyadicRefine hmax1, G'.eval_dyadicRefine hmax2]
    have hw : Measurable (fun p : Ω × ℝ × E =>
        (‖G.eval p.2.1 p.2.2 p.1 - G'.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_coe.measurable.comp
        (G.eval_measurable.sub G'.eval_measurable).nnnorm).pow_const 2
    have hu : Measurable (fun p : Ω × ℝ × E =>
        (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_coe.measurable.comp (hm.sub G.eval_measurable).nnnorm).pow_const 2
    have hpt : ∀ ω s e, (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
          + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s e
      rw [show G.eval s e ω - G'.eval s e ω
        = -(φ ω s e - G.eval s e ω) + (φ ω s e - G'.eval s e ω) by ring]
      have h2 := LevyStochCalc.Poisson.Compensated.sq_nnnorm_add_le_two_mul (-(φ ω s e - G.eval s e ω)) (φ ω s e - G'.eval s e ω)
      rwa [nnnorm_neg] at h2
    have hresG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
      le_trans (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hTn))
        (LevyStochCalc.Poisson.Compensated.master_err N ℱ φ hm hp hq n).le
    have hresG' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
      le_trans (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hTn))
        (LevyStochCalc.Poisson.Compensated.master_err N 𝒢 φ hm hp' hq n).le
    calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G.dyadicRefine hmax1).eval s e ω
            - (G'.dyadicRefine hmax2).eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← LevyStochCalc.Poisson.Compensated.lintegral_swap_es
            (fun ω s e => (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hw ω]
          refine lintegral_congr fun e => ?_
          refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
          rw [hev ω e s]
      _ ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
              + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) ∂ν ∂volume ∂P :=
          lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
            + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
          rw [LevyStochCalc.Poisson.Compensated.lintegral_triple_const_mul 2 (by norm_num), _root_.Prove2MeSourceProof.h_64b57ddfa082ba813e2cbaf7 hu]
      _ ≤ 2 * (((n : ℝ≥0∞) + 1)⁻¹ + ((n : ℝ≥0∞) + 1)⁻¹) := by gcongr
      _ = 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n : ℝ≥0∞) + 1)⁻¹ := mul_add _ _ _
  have hHor : ∀ᶠ n : ℕ in Filter.atTop, T ≤ LevyStochCalc.Poisson.Compensated.stageHorizon n := by
    have h2 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact h2.eventually_ge_atTop T
  have hsq : Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (‖LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ hm hp hq n T ω
        - LevyStochCalc.Poisson.Compensated.stageIntegral N 𝒢 φ hm hp' hq n T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto
        (fun n : ℕ => 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n : ℝ≥0∞) + 1)⁻¹)
        Filter.atTop (nhds 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) LevyStochCalc.Poisson.Compensated.tendsto_natCast_add_one_inv
        (Or.inr (by simp))
      simpa using h1.add h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [hHor] with n hn using hbd n hn
  have hcross : Filter.Tendsto (fun n : ℕ => eLpNorm
      (fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ hm hp hq n T ω
        - LevyStochCalc.Poisson.Compensated.stageIntegral N 𝒢 φ hm hp' hq n T ω) 2 P) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n : ℕ => eLpNorm
        (fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ hm hp hq n T ω
          - LevyStochCalc.Poisson.Compensated.stageIntegral N 𝒢 φ hm hp' hq n T ω) 2 P ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      refine hsq.congr fun n => ?_
      exact (LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq _).symm
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr fun n => ?_
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  have hmix : Filter.Tendsto (fun n : ℕ => eLpNorm
      (fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ hm hp hq n T ω
        - LevyStochCalc.Poisson.Compensated.process N 𝒢 h𝒢 φ hm hp' hq T ω) 2 P) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hcross.add (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N 𝒢 h𝒢 φ hm hp' hq T))
      (Filter.Eventually.of_forall fun n => bot_le)
      (Filter.Eventually.of_forall fun n => ?_)
    refine le_trans (le_of_eq ?_) (eLpNorm_add_le
      ((LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ hm hp hq n T).sub
        (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N 𝒢 φ hm hp' hq n T)).aestronglyMeasurable
      ((LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N 𝒢 φ hm hp' hq n T).sub
        (LevyStochCalc.Poisson.Compensated.process_memLp N 𝒢 h𝒢 φ hm hp' hq T)).aestronglyMeasurable (by norm_num))
    refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  exact _root_.Prove2MeSourceProof.h_7e6dc0a5b3abba2670f5e8de
    (fun n => (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ hm hp hq n T).aestronglyMeasurable)
    (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq T).aestronglyMeasurable
    (LevyStochCalc.Poisson.Compensated.process_memLp N 𝒢 h𝒢 φ hm hp' hq T).aestronglyMeasurable
    (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ hm hp hq T) hmix
end LevyStochCalc.Poisson.Compensated


