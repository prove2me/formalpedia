-- Prove2me | Definitions.Def_SourceProof_93f0177984c2fc01cc45a1ac
-- name    : SourceProof_93f0177984c2fc01cc45a1ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:44.260185+00:00
-- url     : https://prove2.me/theorems/33195b60-c7dd-4899-b299-c16588c93d1e
-- title:
--   StochLean source theorem: StochLean.monotone_tsum_indicator_of_nonneg

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Variation of absolutely summable coefficients with nested cutoffs

An increasing family of index sets may activate each signed coefficient
at most once. Splitting its positive and negative parts gives the actual
sum as a difference of two monotone functions, without enumerating the
index type or imposing a sign on the coefficients.
-/

@[expose] public section

open Set

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_93f0177984c2fc01cc45a1ac {α ι : Type*} [Preorder α]
    {a : α → Set ι} (ha : Monotone a) {w : ι → ℝ}
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i) :
    Monotone (fun t ↦ ∑' i, (a t).indicator w i) := by
  classical
  intro s t hst
  apply (hw.indicator (a s)).tsum_le_tsum _ (hw.indicator (a t))
  intro i
  by_cases hi : i ∈ a s
  · simp only [indicator_of_mem hi, indicator_of_mem (ha hst hi)]
    exact le_rfl
  · rw [indicator_of_notMem hi]
    by_cases hit : i ∈ a t <;> simp [Set.indicator, hit, hw0]
end StochLean


