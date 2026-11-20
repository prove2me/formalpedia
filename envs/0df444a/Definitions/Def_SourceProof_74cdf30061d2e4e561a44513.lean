-- Prove2me | Definitions.Def_SourceProof_74cdf30061d2e4e561a44513
-- name    : SourceProof_74cdf30061d2e4e561a44513
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:22:34.914186+00:00
-- url     : https://prove2.me/theorems/9393d51d-a00c-404e-b7ad-8e74d51172ae
-- title:
--   LevyStochCalc source module: SourceProof_74cdf30061d2e4e561a44513
-- statement:
--   The original source theorem `LevyStochCalc.Martingale.exists_adapted_ae_cadlag` comes from the `LevyStochCalc.Martingale.CadlagModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of real martingales

A real martingale on a right-continuous filtration whose time slices are right-continuous
in measure admits an adapted modification whose paths are almost surely càdlàg. The
modification is the right-limit regularisation along a countable dense set of times
(`ProbabilityTheory.rightContModif`), available for real quasimartingales; a martingale is
a quasimartingale because the elementary integral of a predictable indicator against it has
zero mean.

Two index sets are treated: `ℝ≥0`, where the quasimartingale theory lives (it needs a least
time), and `ℝ`, by restricting to nonnegative times and extending by zero to negative times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Martingale

section Modification

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} {X Y : ι → Ω → ℝ}

end Modification

section Quasimartingale

variable {ι Ω : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ι mΩ} {μ : Measure Ω} {X : ι → Ω → ℝ}

variable [OrderBot ι]

end Quasimartingale

section NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

end NNReal

section Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_74cdf30061d2e4e561a44513 [ℱ.IsRightContinuous] (hX : Martingale X ℱ μ)
    (hrc : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t))
    (hneg : ∀ t, t < 0 → X t =ᵐ[μ] 0) :
    ∃ Y : ℝ → Ω → ℝ, Adapted ℱ Y ∧ (∀ t, Y t =ᵐ[μ] X t) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by
  classical
  -- restrict to nonnegative times
  have hX'm : Martingale (fun s : ℝ≥0 => X s) (LevyStochCalc.Martingale.restrictNNReal ℱ) μ :=
    hX.indexComap NNReal.coe_mono
  have hrc' : ∀ t : ℝ≥0,
      TendstoInMeasure μ (fun s : ℝ≥0 => X s) (𝓝[>] t) (X t) := by
    intro t
    have hcoe : Tendsto (fun r : ℝ≥0 => (r : ℝ)) (𝓝[>] t) (𝓝[>] (t : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun r hr => NNReal.coe_lt_coe.2 hr
    intro ε hε
    exact (hrc t ε hε).comp hcoe
  obtain ⟨Y', hY'ad, hY'eq, hY'c⟩ := LevyStochCalc.Martingale.exists_adapted_ae_isCadlag_nnreal hX'm hrc'
  -- extend by zero to negative times
  let Y : ℝ → Ω → ℝ := fun t ω => if 0 ≤ t then Y' (Real.toNNReal t) ω else 0
  have hYnn : ∀ t, 0 ≤ t → Y t = Y' (Real.toNNReal t) := fun t ht =>
    funext fun ω => if_pos ht
  have hYneg : ∀ t, t < 0 → Y t = 0 := fun t ht => funext fun ω => if_neg (not_le.2 ht)
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [hYnn t ht]
      have h : Measurable[ℱ ((Real.toNNReal t : ℝ≥0) : ℝ)] (Y' (Real.toNNReal t)) :=
        hY'ad (Real.toNNReal t)
      rwa [Real.coe_toNNReal t ht] at h
    · rw [hYneg t ht]
      exact measurable_const
  · intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [hYnn t ht]
      have h : Y' (Real.toNNReal t) =ᵐ[μ] X ((Real.toNNReal t : ℝ≥0) : ℝ) :=
        hY'eq (Real.toNNReal t)
      rwa [Real.coe_toNNReal t ht] at h
    · rw [hYneg t ht]
      exact (hneg t ht).symm
  · filter_upwards [hY'c] with ω hω
    intro t
    constructor
    · rcases le_or_gt 0 t with ht | ht
      · have h1 := (hω.right_continuous (Real.toNNReal t)).tendsto.comp
          (LevyStochCalc.Martingale.tendsto_toNNReal_nhdsGT ht)
        rw [congrFun (hYnn t ht) ω]
        refine h1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (congrFun (hYnn s (ht.trans hs.le)) ω).symm
      · rw [congrFun (hYneg t ht) ω]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT ht] with s hs
        exact (congrFun (hYneg s hs.2) ω).symm
    · rcases lt_or_ge 0 t with ht | ht
      · obtain ⟨L, hL⟩ := hω.left_limit (Real.toNNReal t)
        refine ⟨L, (hL.comp (LevyStochCalc.Martingale.tendsto_toNNReal_nhdsLT ht)).congr' ?_⟩
        filter_upwards [Ioo_mem_nhdsLT ht] with s hs
        exact (congrFun (hYnn s hs.1.le) ω).symm
      · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
        refine eventually_nhdsWithin_of_forall fun s hs => ?_
        exact (congrFun (hYneg s (lt_of_lt_of_le hs ht)) ω).symm
end Real

end LevyStochCalc.Martingale


