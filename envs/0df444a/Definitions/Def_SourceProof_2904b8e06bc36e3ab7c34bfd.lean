-- Prove2me | Definitions.Def_SourceProof_2904b8e06bc36e3ab7c34bfd
-- name    : SourceProof_2904b8e06bc36e3ab7c34bfd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:49.436143+00:00
-- url     : https://prove2.me/theorems/eeae5ae2-f334-440b-8785-15a3db5e4c82
-- title:
--   StochLean source theorem: ProbabilityTheory.isCadlagPath_pi_iff

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag coordinate products and their actual left limits

The deterministic product property holds for arbitrary index types. The
common-event stochastic assertion requires countably many coordinates.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_2904b8e06bc36e3ab7c34bfd {T ι : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)] {x : T → ∀ i, E i} :
    IsCadlagPath x ↔ ∀ i, IsCadlagPath (fun t ↦ x t i) := by
  constructor
  · intro hx i
    refine ⟨fun t ↦ (continuous_apply i).continuousAt.comp_continuousWithinAt (hx.1 t), ?_⟩
    intro t ht
    obtain ⟨y, hy⟩ := hx.2 t ht
    exact ⟨y i, ((continuous_apply i).tendsto y).comp hy⟩
  · intro hx
    refine ⟨fun t ↦ continuousWithinAt_pi.mpr (fun i ↦ (hx i).1 t), ?_⟩
    intro t ht
    choose y hy using fun i ↦ (hx i).2 t ht
    exact ⟨y, tendsto_pi_nhds.mpr hy⟩
end ProbabilityTheory


