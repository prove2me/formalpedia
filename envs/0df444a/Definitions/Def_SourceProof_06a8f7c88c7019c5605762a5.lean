-- Prove2me | Definitions.Def_SourceProof_06a8f7c88c7019c5605762a5
-- name    : SourceProof_06a8f7c88c7019c5605762a5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:36.987418+00:00
-- url     : https://prove2.me/theorems/8bd48798-08fc-5c65-a5fd-8e78d4edd03b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsConditionalIncrementModulus.ae_bounds_of_largeJumpResidual

import Definitions.Def_StochLean_Probability_Martingale_Doob_ConditionalModulus_F000
import Definitions.Def_SourceProof_1dacd1f3a039fdd05447383b
import Definitions.Def_SourceProof_2b6f7a09ab4a386150058c78
import Definitions.Def_SourceProof_3d7237f9edbb29513436330d
import Definitions.Def_SourceProof_66fd83be7b48068a9848e468
import Definitions.Def_SourceProof_9d156f29c7de720a7f707cce
import Definitions.Def_SourceProof_a54f17b20359f1a9dacf5570
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual residual control of the conditional increment modulus

The least almost-sure upper-bound property lifts each fixed-pair conditional
estimate to the conditional modulus. No uncountable intersection of the null
sets of conditional expectations is taken. Right-continuous representatives
are compared with the existing countable running suprema on their common path
events. The fixed residual cap and the bound on probability indicators prove
these suprema finite; no maximal-integrability hypothesis is supplied.

The original process bound independently proves the conditional modulus finite
before its real value is used. This is a domination theorem, not a claim of
small-window convergence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
  {X : ℝ≥0 → Ω → ℝ} {b N : ℝ} {T δ : ℝ≥0} {W : Ω → ℝ≥0∞}

namespace IsConditionalIncrementModulus

theorem _root_.Prove2MeSourceProof.h_06a8f7c88c7019c5605762a5
    (hW : IsConditionalIncrementModulus F P X T δ W) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) (K : ℕ) (hδ : 0 < δ)
    (M : ℝ≥0 → Ω → ℝ) (R : ℕ → ℝ≥0 → Ω → ℝ)
    (hrM : HasRightContinuousPaths M P)
    (hrR : ∀ i ∈ Finset.range K, HasRightContinuousPaths (R i) P)
    (heM : ∀ t : ℝ≥0, M t =ᵐ[P]
      P[cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ) (2 * N) | F t])
    (heR : ∀ i ∈ Finset.range K, ∀ t : ℝ≥0, R i t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < largeJumpSequence X b i ω ∧
          largeJumpSequence X b i ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) :
    ∀ᵐ ω ∂P, W ω ≠ ∞ ∧
      W ω ≤ ENNReal.ofReal ((denseRunningSupremum M T ω).toReal +
        2 * N * ∑ i ∈ Finset.range K, (denseRunningSupremum (R i) T ω).toReal) ∧
      (W ω).toReal ≤ (denseRunningSupremum M T ω).toReal +
        2 * N * ∑ i ∈ Finset.range K, (denseRunningSupremum (R i) T ω).toReal := by
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hMcap : ∀ᵐ ω ∂P,
      ProbabilityTheory.denseRunningSupremum M T ω ≤ ENNReal.ofReal (2 * N) := by
    apply _root_.Prove2MeSourceProof.h_66fd83be7b48068a9848e468
    intro t _
    have hinput : ∀ᵐ ω ∂P,
        ProbabilityTheory.cappedDenseWindowOscillation (ProbabilityTheory.largeJumpResidual X b K) T (2 * δ) (2 * N) ω ≤
          2 * N := Eventually.of_forall fun ω ↦
      _root_.Prove2MeSourceProof.h_2b6f7a09ab4a386150058c78 (ProbabilityTheory.largeJumpResidual X b K) T (2 * δ) (2 * N) ω
    filter_upwards [heM t, condExp_le_nonneg_const (m := F t) hC hinput] with ω he hle
    exact he.le.trans hle
  have hRcap (i : ℕ) (hi : i ∈ Finset.range K) : ∀ᵐ ω ∂P,
      ProbabilityTheory.denseRunningSupremum (R i) T ω ≤ ENNReal.ofReal 1 := by
    apply _root_.Prove2MeSourceProof.h_66fd83be7b48068a9848e468
    intro t _
    have hinput : ∀ᵐ ω ∂P,
        {v | (t : WithTop ℝ≥0) < ProbabilityTheory.largeJumpSequence X b i v ∧
          ProbabilityTheory.largeJumpSequence X b i v ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
            (fun _ ↦ (1 : ℝ)) ω ≤ 1 := by
      apply Eventually.of_forall
      intro ω
      exact indicator_le_self' (fun _ _ ↦ zero_le_one) ω
    filter_upwards [heR i hi t,
      condExp_le_nonneg_const (m := F t) (by norm_num : (0 : ℝ) ≤ 1) hinput]
      with ω he hle
    exact he.le.trans hle
  have hrRall : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range K,
      ProbabilityTheory.IsRightContinuousPath (R i · ω) := (Finset.range K).eventually_all.mpr hrR
  have hRcapall : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range K,
      ProbabilityTheory.denseRunningSupremum (R i) T ω ≤ ENNReal.ofReal 1 :=
    (Finset.range K).eventually_all.mpr hRcap
  have hsup : W ≤ᵐ[P] (fun ω ↦ ENNReal.ofReal
      ((ProbabilityTheory.denseRunningSupremum M T ω).toReal +
        2 * N * ∑ i ∈ Finset.range K, (ProbabilityTheory.denseRunningSupremum (R i) T ω).toReal)) := by
    apply (_root_.Prove2MeSourceProof.h_a54f17b20359f1a9dacf5570 hW)
    intro t u htu huT huδ
    have hce := (_root_.Prove2MeSourceProof.h_3d7237f9edbb29513436330d hX) hc hb T K hN hbound
      hδ htu huT huδ (M t) (fun i ↦ R i t) (heM t) (fun i hi ↦ heR i hi t)
    filter_upwards [hce, hrM, hrRall, hMcap, hRcapall] with ω hceω hrMω hrRω hMω hRω
    apply ENNReal.ofReal_le_ofReal
    apply hceω.2.2.trans
    apply add_le_add
    · exact _root_.Prove2MeSourceProof.h_1dacd1f3a039fdd05447383b (htu.trans huT) hrMω
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMω)
    · apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro i hi
      exact _root_.Prove2MeSourceProof.h_1dacd1f3a039fdd05447383b (htu.trans huT) (hrRω i hi)
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hRω i hi))
  have hiX (t : ℝ≥0) : Integrable (X t) P := by
    have hp : MemLp (X t) 1 P := MemLp.of_bound
      ((hX t).mono (F.le t) le_rfl).aestronglyMeasurable N
      (hbound.mono fun _ hω ↦ hω t)
    exact hp.integrable le_rfl
  have hfin : ∀ᵐ ω ∂P, W ω ≠ ∞ := (_root_.Prove2MeSourceProof.h_9d156f29c7de720a7f707cce hW)
    (fun t _ ↦ hiX t) (fun t _ ↦ hbound.mono fun _ hω ↦ hω t)
  filter_upwards [hfin, hsup] with ω hfinω hsupω
  refine ⟨hfinω, hsupω, ?_⟩
  have hnonneg : 0 ≤ (ProbabilityTheory.denseRunningSupremum M T ω).toReal +
      2 * N * ∑ i ∈ Finset.range K, (ProbabilityTheory.denseRunningSupremum (R i) T ω).toReal :=
    add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg hC (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg))
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    (ENNReal.toReal_le_toReal hfinω ENNReal.ofReal_ne_top).mpr hsupω
end IsConditionalIncrementModulus

end ProbabilityTheory


