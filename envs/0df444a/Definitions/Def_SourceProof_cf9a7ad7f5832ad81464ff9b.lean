-- Prove2me | Definitions.Def_SourceProof_cf9a7ad7f5832ad81464ff9b
-- name    : SourceProof_cf9a7ad7f5832ad81464ff9b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:49.684538+00:00
-- url     : https://prove2.me/theorems/92e78f24-687b-4960-b9d3-ddf4bb40b91f
-- title:
--   StochLean source theorem: StochLean.measurable_stieltjesMeasure

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_54540bbaa62044e454e749e1
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable families of locally finite Stieltjes measures on nonnegative time

Unlike the probability-CDF result on the real line, this result imposes no
normalization or finite total mass. Finite initial-interval restrictions suffice.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_cf9a7ad7f5832ad81464ff9b {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → StieltjesFunction ℝ≥0} (hf : ∀ t, Measurable fun ω ↦ f ω t) :
    Measurable fun ω ↦ (f ω).measure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm (n : ℕ) : Measurable fun ω ↦ (f ω).measure (s ∩ Iic (n : ℝ≥0)) := by
    have h := (Measure.measurable_coe hs).comp
      (_root_.Prove2MeSourceProof.h_54540bbaa62044e454e749e1 hf (n : ℝ≥0))
    change Measurable (fun ω ↦ (f ω).measure.restrict (Iic (n : ℝ≥0)) s) at h
    simpa only [Measure.restrict_apply hs] using h
  have hu : (⋃ n : ℕ, s ∩ Iic (n : ℝ≥0)) = s := by
    ext t
    simp only [mem_iUnion, mem_inter_iff, mem_Iic]
    exact ⟨fun ⟨_, ht, _⟩ ↦ ht, fun ht ↦ ⟨Nat.ceil t, ht, Nat.le_ceil t⟩⟩
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro ω
  have hmono : Monotone (fun n : ℕ ↦ s ∩ Iic (n : ℝ≥0)) := by
    intro n m hnm
    exact inter_subset_inter_right s (Iic_subset_Iic.mpr (Nat.cast_le.mpr hnm))
  have h := tendsto_measure_iUnion_atTop (μ := (f ω).measure) hmono
  rw [hu] at h
  exact h
end StochLean


