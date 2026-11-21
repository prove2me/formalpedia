-- Prove2me | Definitions.Def_SourceProof_be0f56f10988c86fe4ec7fca
-- name    : SourceProof_be0f56f10988c86fe4ec7fca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:11.51599+00:00
-- url     : https://prove2.me/theorems/d9c7e6e9-c040-44b0-b8de-9ed77a59dd73
-- title:
--   LevyStochCalc source module: SourceProof_be0f56f10988c86fe4ec7fca
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Generator.exists_progressive_generator_modification` comes from the `LevyStochCalc.BSDEJ.GeneratorModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorModification_F000
import Definitions.Def_SourceProof_35da2440c6c558bf9e0bd5fa
import Definitions.Def_SourceProof_8a691b9df27a58f82cb0646c
import Definitions.Def_SourceProof_98b1bfd1eba405ec69e0ef6d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressively measurable version of the generator along a triple of processes

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable is
not assumed measurable in the jump variable, so the composite `(ω, s) ↦ f s (Y s ω) (Z s ω)
(U s ω)` along a triple of processes need not be measurable. Approximating the marked process `U`
in `L²` by mark-step integrands makes the composite the pointwise limit, along a subsequence and
almost everywhere on `Ω × [0, T]`, of the jointly and progressively measurable processes obtained
by evaluating the generator along the approximants; the pointwise `limsup` of that subsequence is
then a progressively measurable process of finite energy, vanishing off the horizon, which agrees
with the composite almost everywhere.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

/-! ### Almost everywhere convergence from summable integrals -/

/-! ### The generator along a triple of processes -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

variable [IsProbabilityMeasure P] [SigmaFinite ν] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_be0f56f10988c86fe4ec7fca (N : Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ mΩ)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))) {T : ℝ} (hT : 0 < T)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hYp : Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω)
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZp : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZ : ∀ i, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hUp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hUq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
      ∧ Probability.ProgressivelyMeasurable ℱ b
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
      ∧ Brownian.Ito.energy P T b ≠ ⊤
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1) := by
  classical
  obtain ⟨G, hGad, hGerr⟩ : ∃ G : ∀ n : ℕ, Σ ℓ : ℕ,
      LevyStochCalc.Poisson.Compensated.MarkStep Ω E ν (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (LevyStochCalc.Poisson.Compensated.stageHorizon n) (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n) ℓ),
      (∀ n, (G n).2.Adapted ℱ) ∧
        ∀ n, LevyStochCalc.Poisson.Compensated.stageErr (fun ω s e => U s ω e) P n (G n).2 < ((n : ℝ≥0∞) + 1)⁻¹ :=
    ⟨LevyStochCalc.Poisson.Compensated.master N ℱ (fun ω s e => U s ω e) hUm hUp hUq,
      LevyStochCalc.Poisson.Compensated.master_adapted N ℱ (fun ω s e => U s ω e) hUm hUp hUq,
      LevyStochCalc.Poisson.Compensated.master_err N ℱ (fun ω s e => U s ω e) hUm hUp hUq⟩
  set W : Ω → ℝ → ℝ := fun ω s =>
    Set.indicator (Set.Icc (0 : ℝ) T) (fun s => f s (Y s ω) (Z s ω) (U s ω)) s with hWdef
  set g : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    ∫⁻ e, (‖U p.2 p.1 e - (G n).2.eval p.2 e p.1‖₊ : ℝ≥0∞) ^ 2 ∂ν with hgdef
  have hswap : Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    have h1 : Measurable fun q : (Ω × ℝ) × E => U q.1.2 q.1.1 q.2 := hUm.comp hswap
    have h2 : Measurable fun q : (Ω × ℝ) × E => (G n).2.eval q.1.2 q.2 q.1.1 :=
      (G n).2.eval_measurable.comp hswap
    exact (((h1.sub h2).nnnorm.coe_nnreal_ennreal).pow_const 2).lintegral_prod_right'
  have hgle : ∀ n, T ≤ LevyStochCalc.Poisson.Compensated.stageHorizon n →
      ∫⁻ p, g n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n hn
    refine le_of_lt (lt_of_le_of_lt ?_ (hGerr n))
    rw [lintegral_prod _ (hgm n).aemeasurable]
    exact lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hn)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, T ≤ LevyStochCalc.Poisson.Compensated.stageHorizon N₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt T (one_lt_two : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  have htend : Tendsto
      (fun n => ∫⁻ p, g n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine h.congr fun n => ?_
      simp [Function.comp]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun _ => bot_le) (eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩)
    exact hgle n (hN₀.trans (LevyStochCalc.Poisson.Compensated.stageHorizon_mono hn))
  obtain ⟨ms, -, hmslt⟩ := LevyStochCalc.BSDEJ.Generator.exists_subseq_lt_geometric htend
  have hsum : ∑' i : ℕ, ∫⁻ p, g (ms i) p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      ≠ ⊤ :=
    ne_top_of_le_ne_top LevyStochCalc.BSDEJ.Generator.tsum_geometric_two_inv_ne_top
      (ENNReal.tsum_le_tsum fun i => (hmslt i).le)
  have hae0 : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Tendsto (fun i => g (ms i) p) atTop (𝓝 0) :=
    LevyStochCalc.BSDEJ.Generator.ae_tendsto_zero_of_tsum_lintegral_ne_top (fun i => hgm (ms i)) hsum
  obtain ⟨H, hHm, hHp, hHz, hHle⟩ : ∃ H : ℕ → Ω → ℝ → ℝ,
      (∀ n, Measurable (Function.uncurry (H n))) ∧
      (∀ n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H n)) ∧
      (∀ n ω s, s ∉ Set.Icc (0 : ℝ) T → H n ω s = 0) ∧
      ∀ n ω s, s ∈ Set.Icc (0 : ℝ) T →
        (‖W ω s - H n ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L * g n (ω, s) ^ (1 / 2 : ℝ) := by
    refine ⟨fun n ω s => Set.indicator (Set.Icc (0 : ℝ) T)
      (fun s => f s (Y s ω) (Z s ω) (fun e => (G n).2.eval s e ω)) s, ?_, ?_, ?_, ?_⟩
    · intro n
      have hbase := _root_.Prove2MeSourceProof.h_8a691b9df27a58f82cb0646c hf hlip (G n).2 hYm hZm
      have hrw : (Function.uncurry fun ω s => Set.indicator (Set.Icc (0 : ℝ) T)
            (fun s => f s (Y s ω) (Z s ω) (fun e => (G n).2.eval s e ω)) s)
          = {q : Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T}.indicator
            (Function.uncurry fun ω s =>
              f s (Y s ω) (Z s ω) (fun e => (G n).2.eval s e ω)) := by
        funext p
        simp only [Function.uncurry]
        by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
        · rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem (show p ∈ {q : Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T} from hp)]
          rfl
        · rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem (show p ∉ {q : Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T} from hp)]
      rw [hrw]
      exact hbase.indicator (measurable_snd measurableSet_Icc)
    · intro n
      exact _root_.Prove2MeSourceProof.h_98b1bfd1eba405ec69e0ef6d
        (_root_.Prove2MeSourceProof.h_35da2440c6c558bf9e0bd5fa hf hlip (G n).2 (hGad n) hYp hZp) T
    · intro n ω s hs
      exact Set.indicator_of_notMem hs _
    · intro n ω s hs
      simp only [hWdef, hgdef, Set.indicator_of_mem hs]
      exact LevyStochCalc.BSDEJ.Generator.enorm_sub_generator_jump_le hlip s (Y s ω) (Z s ω) (U s ω)
        (fun e => (G n).2.eval s e ω)
  have haeW : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      LevyStochCalc.Brownian.Ito.limsupIntegrand H ms p.1 p.2 = W p.1 p.2 := by
    filter_upwards [hae0] with p hp0
    have hc : Tendsto (fun i => ENNReal.ofReal L * g (ms i) p ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i => g (ms i) p ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have h2 := hp0.ennrpow_const (1 / 2 : ℝ)
        rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
    have hlim : Tendsto (fun i => H (ms i) p.1 p.2) atTop (𝓝 (W p.1 p.2)) := by
      by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
      · exact LevyStochCalc.BSDEJ.Generator.tendsto_of_enorm_sub_le (fun i => hHle (ms i) p.1 p.2 hp) hc
      · have hW0 : W p.1 p.2 = 0 := by
          simp only [hWdef]
          exact Set.indicator_of_notMem hp _
        have hH0 : ∀ i, H (ms i) p.1 p.2 = 0 := fun i => hHz (ms i) p.1 p.2 hp
        rw [hW0]
        simp only [hH0]
        exact tendsto_const_nhds
    exact hlim.limsup_eq
  have haeW' : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      LevyStochCalc.Brownian.Ito.limsupIntegrand H ms ω s = W ω s := Measure.ae_ae_of_ae_prod haeW
  have hWfin : LevyStochCalc.Brownian.Ito.energy P T W ≠ ⊤ := by
    simp only [hWdef]
    exact LevyStochCalc.BSDEJ.Generator.lintegral_sq_generator_along_indicator_lt_top hlip hf hf0 hYm hY hZm hZ hUm
      (hUq T hT).ne
  refine ⟨LevyStochCalc.Brownian.Ito.limsupIntegrand H ms, Measurable.limsup fun i => hHm (ms i),
    _root_.Prove2MeSourceProof.h_f0c53d0eaa784ed729ffd61d fun i => hHp (ms i), ?_, ?_, ?_⟩
  · intro ω s hs
    have h0 : (fun i => H (ms i) ω s) = fun _ => (0 : ℝ) :=
      funext fun i => hHz (ms i) ω s hs
    rw [LevyStochCalc.Brownian.Ito.limsupIntegrand, h0]
    exact limsup_const 0
  · have heq : LevyStochCalc.Brownian.Ito.energy P T (LevyStochCalc.Brownian.Ito.limsupIntegrand H ms)
        = LevyStochCalc.Brownian.Ito.energy P T W := by
      unfold LevyStochCalc.Brownian.Ito.energy
      refine lintegral_congr_ae ?_
      filter_upwards [haeW'] with ω hω
      refine lintegral_congr_ae ?_
      filter_upwards [hω] with s hs
      rw [hs]
    rw [heq]
    exact hWfin
  · have hnull : (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
        ((Set.univ : Set Ω) ×ˢ (Set.Icc (0 : ℝ) T)ᶜ) = 0 := by
      rw [Measure.prod_prod, Measure.restrict_apply' measurableSet_Icc,
        Set.compl_inter_self, measure_empty, mul_zero]
    have haeIcc : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
        p.2 ∈ Set.Icc (0 : ℝ) T := by
      rw [ae_iff]
      refine measure_mono_null ?_ hnull
      intro p hp
      exact Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩
    filter_upwards [haeW, haeIcc] with p h1 h2
    rw [h1]
    simp only [hWdef]
    exact Set.indicator_of_mem h2 _
end LevyStochCalc.BSDEJ.Generator


