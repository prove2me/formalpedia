-- Prove2me | Definitions.Def_SourceProof_d15413cea1756ce85082d92a
-- name    : SourceProof_d15413cea1756ce85082d92a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:45.385868+00:00
-- url     : https://prove2.me/theorems/882ba986-70f0-5f17-bee9-bb05c8064dc7
-- title:
--   StochLean source theorem: MeasureTheory.isUIMartingale_tsum_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_14e908939680537161478394
import Definitions.Def_SourceProof_4d66c8d394bf81c5a531f8d4
import Definitions.Def_SourceProof_be0b26cebaa157c758248f0a
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual sums of centered integrable lifetime jumps

Summable coefficient first moments provide an actual integrable envelope on
one common event of absolute convergence. Finite partial sums are martingales;
their coordinatewise UI convergence proves martingality of the original tsum.
The same envelope gives UI over the entire time axis.

The source centering theorem uses the actual conditional expectation before
each stopping lifetime. No predictability, finite lifetime, initial-value
normalization, candidate terminal or assumed series convergence is needed.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0} {C Z : ℕ → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_d15413cea1756ce85082d92a
    (hM : ∀ n, IsUIMartingale
      (fun t : ℝ≥0 ↦ {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n)) F P)
    (hi : ∀ n, Integrable (C n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖C n ω‖ ∂P)) :
    IsUIMartingale
      (fun t ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n) ω) F P := by
  classical
  let J : ℕ → ℝ≥0 → Ω → ℝ :=
    fun n t ↦ {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n)
  let S : ℕ → ℝ≥0 → Ω → ℝ := fun N t ω ↦ ∑ n ∈ Finset.range N, J n t ω
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' n, J n t ω
  let G : Ω → ℝ := fun ω ↦ ∑' n, ‖C n ω‖
  obtain ⟨habs, hiG, _⟩ := _root_.Prove2MeSourceProof.h_14e908939680537161478394 hi hs
  have hmS (N : ℕ) : Martingale (S N) F P := by
    induction N with
    | zero =>
      have he : S 0 = 0 := by
        funext t ω
        exact Finset.sum_range_zero (fun n ↦ J n t ω)
      rw [he]
      exact martingale_zero ℝ F P
    | succ N ih =>
      have he : S (N + 1) = S N + J N := by
        funext t ω
        exact Finset.sum_range_succ (fun n ↦ J n t ω) N
      rw [he]
      exact ih.add (hM N).1
  have haY : StronglyAdapted F Y := by
    intro t
    let : MeasurableSpace Ω := F t
    change StronglyMeasurable (fun ω ↦ ∑' n, J n t ω)
    exact StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ)
      (fun n ↦ (hM n).1.stronglyAdapted t)
  have hjnorm (n : ℕ) (t : ℝ≥0) (ω : Ω) : ‖J n t ω‖ ≤ ‖C n ω‖ :=
    norm_indicator_le_norm_self _ _
  have hbS (N : ℕ) (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖S N t ω‖ ≤ ‖G ω‖ := by
    filter_upwards [habs] with ω hω
    rw [Real.norm_of_nonneg (tsum_nonneg fun n ↦ norm_nonneg (C n ω))]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ ↦ hjnorm n t ω).trans
      (hω.sum_le_tsum (Finset.range N) (fun n _ ↦ norm_nonneg (C n ω))))
  have hsum (t : ℝ≥0) : ∀ᵐ ω ∂P, Summable (fun n ↦ J n t ω) :=
    habs.mono fun ω hω ↦ hω.of_norm_bounded (fun n ↦ hjnorm n t ω)
  have hbY (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖Y t ω‖ ≤ ‖G ω‖ := by
    filter_upwards [habs, hsum t] with ω hω hJ
    rw [Real.norm_of_nonneg (tsum_nonneg fun n ↦ norm_nonneg (C n ω))]
    exact (norm_tsum_le_tsum_norm hJ.norm).trans
      (hJ.norm.tsum_le_tsum (fun n ↦ hjnorm n t ω) hω)
  have huiS (t : ℝ≥0) : UniformIntegrable (fun N ↦ S N t) 1 P :=
    (_root_.Prove2MeSourceProof.h_4d66c8d394bf81c5a531f8d4 (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hiG)))
      (fun N ↦ ((hmS N).integrable t).aestronglyMeasurable) (fun N ↦ hbS N t)
  have hl (t : ℝ≥0) : TendstoInMeasure P (fun N ↦ S N t) atTop (Y t) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun N ↦ ((hmS N).integrable t).aestronglyMeasurable)
    exact (hsum t).mono fun _ hω ↦ hω.hasSum.tendsto_sum_nat
  refine ⟨_root_.Prove2MeSourceProof.h_be0b26cebaa157c758248f0a hmS haY huiS hl, ?_⟩
  exact (_root_.Prove2MeSourceProof.h_4d66c8d394bf81c5a531f8d4 (uniformIntegrable_const le_rfl ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hiG)))
    (fun t ↦ ((haY t).mono (F.le t)).aestronglyMeasurable) hbY
end MeasureTheory


