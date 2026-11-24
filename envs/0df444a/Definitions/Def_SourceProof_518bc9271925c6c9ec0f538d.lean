-- Prove2me | Definitions.Def_SourceProof_518bc9271925c6c9ec0f538d
-- name    : SourceProof_518bc9271925c6c9ec0f538d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:32.944331+00:00
-- url     : https://prove2.me/theorems/436fab6e-c148-42a8-80e8-9535921cf442
-- title:
--   StochLean source theorem: StochLean.tendsto_stepCutoff_left

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

theorem _root_.Prove2MeSourceProof.h_518bc9271925c6c9ec0f538d {E : Type*} [TopologicalSpace E] [Zero E]
    (a t : ℝ≥0) (b : E) :
    Tendsto (fun u : ℝ≥0 ↦ if a ≤ u then b else 0) (𝓝[<] t)
      (𝓝 (if a < t then b else 0)) := by
  by_cases h : a < t
  · rw [if_pos h]
    have hu : ∀ᶠ u in 𝓝[<] t, a < u :=
      (eventually_gt_nhds h).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [hu] with u hu
    simp only [if_pos hu.le]
  · rw [if_neg h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [if_neg (not_le_of_gt ((show u < t from hu).trans_le (le_of_not_gt h)))]
end StochLean


