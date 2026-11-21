-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
-- name    : LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:03:03.489809+00:00
-- url     : https://prove2.me/theorems/d9831fa1-cf6d-425d-aad2-a9b42bfcf64a
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionConvergence
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionConvergence. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F001
import Definitions.Def_SourceProof_6192656f90a3e230d130317d
import Definitions.Def_SourceProof_f748d28952e895ba511897bd

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Cauchy-at-each-time bound for the simple integral.** For two adapted
simple integrands sharing the endpoint `T`, the `L²(P)`-distance of their integrals
at any intermediate time `t ≤ T` is bounded by the (endpoint) `L²(λ⊗P)`-distance of
their evals over `[0, T]`. The difference process `simpleIntegral W H₁ · −
simpleIntegral W H₂ ·` is a martingale (`Martingale.sub`), so its second moment is
monotone in time (`integral_sq_mono_of_martingale`), capping the `t`-value by the
`T`-value, which is the endpoint difference isometry `diff_isometry_simple`. This
upgrades the endpoint `L²`-Cauchy hypothesis to `L²`-Cauchy at *every* `t ≤ T`
without a general-`t` refinement re-derivation. -/
lemma simpleIntegral_lintegral_sq_sub_le_endpoint_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : ℝ → Ω → ℝ :=
    fun u ω => simpleIntegral W H₁ u ω - simpleIntegral W H₂ u ω with hM
  have hmart : MeasureTheory.Martingale M
      ℱ P :=
    (_root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ H₁ h_adapt₁).sub
      (_root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ H₂ h_adapt₂)
  have hMemLp : ∀ {u : ℝ}, 0 ≤ u → u ≤ T → MeasureTheory.MemLp (M u) 2 P :=
    fun {u} hu huT =>
      (_root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ hT H₁ h_adapt₁ hu huT).sub
        (_root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ hT H₂ h_adapt₂ hu huT)
  -- bridge `∫⁻‖M u‖₊² = ofReal (∫ (M u)²)` for `M u ∈ L²`.
  have h_bridge : ∀ {u : ℝ}, MeasureTheory.MemLp (M u) 2 P →
      ∫⁻ ω, (‖M u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (M u ω) ^ 2 ∂P) := by
    intro u hu
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    refine lintegral_congr (fun ω => ?_)
    rw [show (‖M u ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖M u ω‖ from (ofReal_norm _).symm,
        ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  calc ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (∫ ω, (M t ω) ^ 2 ∂P) := h_bridge (hMemLp ht_nn htT)
    _ ≤ ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (integral_sq_mono_of_martingale hmart
          (hMemLp ht_nn htT) (hMemLp (le_of_lt hT) (le_refl T)) htT)
    _ = ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := (h_bridge (hMemLp (le_of_lt hT) (le_refl T))).symm
    _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        simp only [hM]
        exact _root_.Prove2MeSourceProof.h_02639dd90be44822908c47b8 W ℱ hℱ hT H₁ H₂ h_eq h_adapt₁ h_adapt₂
/-- **A single adapted simple approximant within `ε` on `[0, T]`.** Extracted from
the convergent dense sequence `adaptedSimple_dense_L2_brownian`. -/
lemma exists_adaptedSimple_within
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    {T : ℝ} (hT : 0 < T)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ G : SimplePredictable Ω T,
      (∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (G.partition i.castSucc)) (G.ξ i)) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε := by
  obtain ⟨Hn, h_adapt, h_tend⟩ :=
    _root_.Prove2MeSourceProof.h_6192656f90a3e230d130317d ℱ hT H h_meas h_progMeas h_sq_int
  have hev : ∀ᶠ m in Filter.atTop,
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε :=
    h_tend (Iio_mem_nhds hε)
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨Hn m, h_adapt m, hm⟩
/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`. -/
lemma eLpNorm_two_rpow_eq_lintegral_sq {μ : MeasureTheory.Measure Ω} (g : Ω → ℝ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num)
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]
  refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`, over an arbitrary base type. -/
lemma eLpNorm_sq_eq_lintegral_nnnorm_sq {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} (g : β → ℝ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num)
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]; refine lintegral_congr (fun x => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
/-- `eval` is bounded by the sum of the coefficient bounds. -/
lemma eval_abs_le_sum_bounds {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    |H.eval s ω| ≤ ∑ i : Fin H.N, (H.ξ_bounded i).choose := by
  unfold SimplePredictable.eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hM : ∀ ω, |H.ξ i ω| ≤ (H.ξ_bounded i).choose := (H.ξ_bounded i).choose_spec
  have hM0 : 0 ≤ (H.ξ_bounded i).choose := le_trans (abs_nonneg _) (hM ω)
  split_ifs with h
  · exact hM ω
  · simpa using hM0
end LevyStochCalc.Brownian.Ito


