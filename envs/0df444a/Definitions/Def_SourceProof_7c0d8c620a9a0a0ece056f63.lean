-- Prove2me | Definitions.Def_SourceProof_7c0d8c620a9a0a0ece056f63
-- name    : SourceProof_7c0d8c620a9a0a0ece056f63
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:55:32.077575+00:00
-- url     : https://prove2.me/theorems/2e3abb2a-d462-4f76-9e1f-c556198f8e37
-- title:
--   LevyStochCalc source module: SourceProof_7c0d8c620a9a0a0ece056f63
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_sub_leftFreeze` comes from the `LevyStochCalc.Brownian.LeftFreeze` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F001
import Definitions.Def_SourceProof_ab7ca2049b8b9b3eaf1b7768

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Freezing a bounded adapted process at the left endpoints of a dyadic grid

Freezing a bounded adapted process `Y` at the left endpoints of the dyadic partition of `[0, t]`
of level `n` (`Analysis/DyadicGrid.lean`) gives a simple predictable integrand
`leftFreeze Y t n`, whose value at a time `s ∈ (0, t]` is `Y` at the left endpoint `leftPt t n s`
of the cell containing `s`. When the
frozen values converge, at every positive time and almost every sample point, to a bounded
process `Y₋`, the Itô integrals of `leftFreeze Y t n · H` converge in `L²` to the Itô integral of
`Y₋ · H`, by the difference isometry and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Analysis

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Freeze

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t) (n : ℕ)

end Freeze

section Limit

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s)) {t : ℝ} (ht : 0 < t)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_7c0d8c620a9a0a0ece056f63 (Yminus : ℝ → Ω → ℝ)
    (hYmb : ∀ s ω, |Yminus s ω| ≤ C)
    (hmm' : Measurable (Function.uncurry fun ω s => Yminus s ω * H ω s))
    (hmp' : Probability.ProgressivelyMeasurable ℱ fun ω s => Yminus s ω * H ω s)
    (hmq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hconv : ∀ᵐ ω ∂P, ∀ s, 0 < s → s ≤ t →
      Tendsto (fun n : ℕ => Y (leftPt t n s) ω) atTop (𝓝 (Yminus s ω))) :
    Tendsto (fun n : ℕ => ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (leftFreeze Y hYb hYm ht n).eval s ω * H ω s)
        ((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm)
        ((leftFreeze Y hYb hYm ht n).progressivelyMeasurable_eval_mul ℱ
          (leftFreeze_adapt Y hYb hYm ht n ℱ hYad) hp)
        ((_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (leftFreeze Y hYb hYm ht n)) hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
  have hiso : ∀ n : ℕ, (∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s)
        ((LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm)
        ((LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).progressivelyMeasurable_eval_mul ℱ
          (LevyStochCalc.Brownian.Ito.leftFreeze_adapt Y hYb hYm ht n ℱ hYad) hp)
        ((_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n)) hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P :=
    fun n => _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ _ _ _ _ _ _ _ _ ht
  rw [tendsto_congr hiso]
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * |C|) ^ 2) with hK
  have hK' : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), s ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  -- the pointwise bound on `(0, t]`
  have hpt : ∀ (n : ℕ) (ω : Ω) (s : ℝ), 0 < s → s ≤ t →
      (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ K * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro n ω s hs hst
    rw [← sub_mul, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, hK,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω - Yminus s ω|
        ≤ |(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω| + |Yminus s ω| := abs_sub _ _
      _ ≤ C + C := add_le_add (LevyStochCalc.Brownian.Ito.abs_leftFreeze_eval_le Y hYb hYm ht n hs hst ω) (hYmb s ω)
      _ ≤ 2 * |C| := by linarith [le_abs_self C]
  -- measurability
  have hHmeas : Measurable fun p : Ω × ℝ => (‖H p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp hm)).pow_const 2
  have hHint : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    hHmeas.lintegral_prod_right'
  have hjoint : ∀ n : ℕ, Measurable fun p : Ω × ℝ =>
      (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval p.2 p.1 * H p.1 p.2 - Yminus p.2 p.1 * H p.1 p.2‖₊
        : ℝ≥0∞) ^ 2 := fun n =>
    (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp
      (((LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm).sub hmm'))).pow_const 2
  have hslice : ∀ (n : ℕ) (ω : Ω), Measurable fun s : ℝ =>
      (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro n ω
    have h1 : Measurable fun s : ℝ => (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s :=
      ((LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm).comp measurable_prodMk_left
    have h2 : Measurable fun s : ℝ => Yminus s ω * H ω s := hmm'.comp measurable_prodMk_left
    exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp (h1.sub h2))).pow_const 2
  have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume :=
    fun n => (hjoint n).lintegral_prod_right'
  have hfin : ∫⁻ ω, K * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ hK']
    exact ENNReal.mul_ne_top hK' (hq t ht).ne
  have hbdd : ∀ n : ℕ, ∀ᵐ ω ∂P, (∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume) ≤ K * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun n =>
    Filter.Eventually.of_forall fun ω => by
      rw [← lintegral_const_mul' _ _ hK']
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
      exact hpt n ω s (lt_of_le_of_ne hs.1 hs0.symm) hs.2
  have hHfin : ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    ae_lt_top hHint (hq t ht).ne
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume) atTop (𝓝 0) := by
    filter_upwards [hconv, hHfin] with ω hω hHω
    have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), Tendsto (fun n : ℕ =>
        (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2)
        atTop (𝓝 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
      have hs' : 0 < s := lt_of_le_of_ne hs.1 hs0.symm
      have h1 : Tendsto (fun n => (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω) atTop
          (𝓝 (Yminus s ω)) :=
        (hω s hs' hs.2).congr fun n => (_root_.Prove2MeSourceProof.h_80616d8197bf2b1beeb50920 Y hYb hYm ht n hs' hs.2 ω).symm
      have h2 : Tendsto (fun n => (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s
          - Yminus s ω * H ω s) atTop (𝓝 0) := by
        have := (h1.mul_const (H ω s)).sub (tendsto_const_nhds (x := Yminus s ω * H ω s))
        simpa using this
      have h3 : Tendsto (fun n => (‖(LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s
          - Yminus s ω * H ω s‖₊ : ℝ≥0∞)) atTop (𝓝 0) := by
        rw [← ENNReal.coe_zero]
        exact ENNReal.tendsto_coe.mpr (by simpa using h2.nnnorm)
      simpa using (ENNReal.Tendsto.pow (n := 2) h3)
    have hdom := tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (f := fun _ => 0)
      (fun s => K * (‖H ω s‖₊ : ℝ≥0∞) ^ 2) (fun n => hslice n ω)
      (fun n => by
        filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
        exact hpt n ω s (lt_of_le_of_ne hs.1 hs0.symm) hs.2)
      (by rw [lintegral_const_mul' _ _ hK']; exact ENNReal.mul_ne_top hK' hHω.ne) hptw
    simpa using hdom
  have hmain := tendsto_lintegral_of_dominated_convergence (μ := P) (f := fun _ => 0)
    (fun ω => K * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas hbdd hfin hlim
  simpa using hmain
end Limit

end LevyStochCalc.Brownian.Ito


