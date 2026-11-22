-- Prove2me | Definitions.Def_SourceProof_67ddefea84ca823233581ab0
-- name    : SourceProof_67ddefea84ca823233581ab0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:19:52.313043+00:00
-- url     : https://prove2.me/theorems/d7e22e59-2dc6-41dc-b928-856c23d5a7d2
-- title:
--   LevyStochCalc source module: SourceProof_67ddefea84ca823233581ab0
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt` comes from the `LevyStochCalc.Ito.JumpSplittingRemainderVanishing` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_SourceProof_7c1e051c1c1f9aebd6c80fa9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing remainders and the jump of a solution

Along a subsequence of the spanning sets of the intensity the compensated integrals of a finite
family of integrands cut to the complements of those sets vanish uniformly on every bounded
window, by Doob's `L²` maximal inequality against the Itô–Lévy isometry; passing to such a
subsequence in the splitting with remainder, the jump of a jump diffusion across an arrival time
carrying a mark of a spanning set is exactly the jump coefficient read at the left limit there.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` — the jump of a
  solution across an arrival time.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Uniform

open LevyStochCalc.Probability

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

omit h_meas h_progMeas h_sq in

theorem _root_.Prove2MeSourceProof.h_67ddefea84ca823233581ab0
    {ι : Type*} [Finite ι] (φ : ι → Ω → ℝ → E → ℝ)
    (hm : ∀ i, Measurable fun p : Ω × ℝ × E => φ i p.1 p.2.1 p.2.2)
    (hp : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ (φ i))
    (hq : ∀ i, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∃ ks : ℕ → ℕ, (∀ m, m ≤ ks m) ∧ ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ m in atTop,
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |stochasticIntegral N ℱ hℱ (markCut (spanningSets ν (ks m))ᶜ (φ i))
          (measurable_markCut (hm i) (measurableSet_spanningSets ν (ks m)).compl)
          ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hp i)) (measurableSet_spanningSets ν (ks m)).compl)
          (fun T' hT' => sq_markCut (hq i) (spanningSets ν (ks m))ᶜ T' hT') t ω| < δ := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  set R : ℕ → ι → ℝ → Ω → ℝ := fun m i t ω =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (spanningSets ν m)ᶜ (φ i))
      (LevyStochCalc.Poisson.Compensated.measurable_markCut (hm i) (measurableSet_spanningSets ν m).compl)
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hp i)) (measurableSet_spanningSets ν m).compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hq i) (spanningSets ν m)ᶜ T' hT') t ω with hRdef
  have hMart : ∀ m i, Martingale (R m i) ℱ.rightCont P := fun m i =>
    LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ _ _ _ _
  have hRm : ∀ m i t, Measurable (R m i t) := fun m i t =>
    (((hMart m i).1 t).mono (ℱ.rightCont.le t)).measurable
  set D : ℕ → ι → Ω → ℝ≥0∞ := fun m i ω => ⨆ k, (‖LevyStochCalc.Probability.dyadicRunMax (R m i) T k ω‖₊ : ℝ≥0∞)
    with hDdef
  have hDm : ∀ m i, Measurable (D m i) := fun m i =>
    Measurable.iSup fun k => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hRm m i) T k
  have hDoob : ∀ m i, ∫⁻ ω, (D m i ω) ^ 2 ∂P ≤ 4 * ∫⁻ ω, (‖R m i T ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    fun m i => LevyStochCalc.Probability.lintegral_iSup_dyadicRunMax_sq_le (hMart m i) hT.le
  have hD0 : ∀ i, Tendsto (fun m => ∫⁻ ω, (D m i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
      (hDoob · i)
    simpa using ENNReal.Tendsto.const_mul
      (LevyStochCalc.Ito.JumpSplitting.tendsto_lintegral_sq_stochasticIntegral_markCut_spanningSets_compl N ℱ hℱ (φ i) (hm i)
        (hp i) (hq i) hT) (Or.inr (by norm_num))
  have hconv : ∀ i, Tendsto (fun m => ∫⁻ ω, (‖(D m i ω).toReal - (0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hD0 i)
      (fun _ => zero_le) fun m => lintegral_mono fun ω => ?_
    rw [sub_zero, Real.nnnorm_of_nonneg ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.coe_toNNReal_le_self 2
  obtain ⟨ks, hks, hae⟩ := _root_.Prove2MeSourceProof.h_7c1e051c1c1f9aebd6c80fa9
    (μ := P) (ι := ι) (u := fun m i ω => (D m i ω).toReal) (v := fun _ _ => (0 : ℝ))
    (fun m i => (hDm m i).ennreal_toReal) (fun _ => measurable_const) hconv
  refine ⟨ks, hks, ?_⟩
  have hfin : ∀ m i, ∀ᵐ ω ∂P, D m i ω ≠ ⊤ := fun m i => by
    have hlt : ∫⁻ ω, (D m i ω) ^ 2 ∂P < ⊤ := by
      refine lt_of_le_of_lt (hDoob m i) (ENNReal.mul_lt_top (by norm_num) ?_)
      rw [hRdef]
      dsimp only
      exact lt_of_eq_of_lt
        (LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ _ _ _ _ T hT)
        (LevyStochCalc.Poisson.Compensated.sq_markCut (hq i) _ T hT)
    filter_upwards [ae_lt_top ((hDm m i).pow_const 2) hlt.ne] with ω hω
    intro h
    rw [h] at hω
    simp at hω
  have hcad : ∀ m i, ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => R m i s ω) (𝓝[>] t) (𝓝 (R m i t ω)) :=
    fun m i => by
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (spanningSets ν m)ᶜ (φ i))
        (LevyStochCalc.Poisson.Compensated.measurable_markCut (hm i) (measurableSet_spanningSets ν m).compl)
        ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hp i)) (measurableSet_spanningSets ν m).compl)
        (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hq i) (spanningSets ν m)ᶜ T' hT')] with ω hω t
      exact (hω t).1
  filter_upwards [hae, MeasureTheory.ae_all_iff.mpr fun m => MeasureTheory.ae_all_iff.mpr
    fun i => hfin (ks m) i, MeasureTheory.ae_all_iff.mpr fun m => MeasureTheory.ae_all_iff.mpr
    fun i => hcad (ks m) i] with ω hω hfω hcω
  intro δ hδ
  have hlim : ∀ i, Tendsto (fun m => (D (ks m) i ω).toReal) atTop (𝓝 0) := hω
  have hev : ∀ᶠ m in atTop, ∀ i, (D (ks m) i ω).toReal < δ :=
    Filter.eventually_all.mpr fun i => (hlim i).eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with m hm i t ht
  have hle : (‖R (ks m) i t ω‖₊ : ℝ≥0∞) ≤ D (ks m) i ω := by
    rw [hDdef]
    dsimp only
    rw [← _root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6 hT.le (hcω m i)]
    exact le_iSup (fun t : Set.Icc (0 : ℝ) T => (‖R (ks m) i (t : ℝ) ω‖₊ : ℝ≥0∞)) ⟨t, ht⟩
  calc |R (ks m) i t ω| = ((‖R (ks m) i t ω‖₊ : ℝ≥0∞)).toReal := by simp
    _ ≤ (D (ks m) i ω).toReal := ENNReal.toReal_mono (hfω m i) hle
    _ < δ := hm i
end Uniform

section Solution

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

end Solution

end LevyStochCalc.Ito.JumpSplitting


