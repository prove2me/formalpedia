-- Prove2me | Definitions.Def_SourceProof_9121625c995972271da6f2bc
-- name    : SourceProof_9121625c995972271da6f2bc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:34.905799+00:00
-- url     : https://prove2.me/theorems/b2348adf-db54-4cc4-a67e-b5a25b4ec14a
-- title:
--   StochLean source theorem: StochLean.tendsto_stepCutoff_right

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # One-sided limits of a closed step cutoff

The right limit includes a jump at the endpoint; the strict-left limit
excludes it. The zero-time left filter may be trivial and is not asserted
to have a unique limit.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_9121625c995972271da6f2bc {E : Type*} [TopologicalSpace E] [Zero E]
    (a t : ℝ≥0) (b : E) :
    Tendsto (fun u : ℝ≥0 ↦ if a ≤ u then b else 0) (𝓝[≥] t)
      (𝓝 (if a ≤ t then b else 0)) := by
  by_cases h : a ≤ t
  · rw [if_pos h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [if_pos (h.trans (show t ≤ u from hu))]
  · rw [if_neg h]
    have hu : ∀ᶠ u in 𝓝[≥] t, u < a :=
      (eventually_lt_nhds (lt_of_not_ge h)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [hu] with u hu
    simp only [if_neg (not_le_of_gt hu)]
end StochLean


