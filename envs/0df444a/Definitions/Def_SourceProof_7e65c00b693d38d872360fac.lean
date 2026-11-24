-- Prove2me | Definitions.Def_SourceProof_7e65c00b693d38d872360fac
-- name    : SourceProof_7e65c00b693d38d872360fac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:32.927943+00:00
-- url     : https://prove2.me/theorems/136e129b-3768-452b-afb2-a0c4d167c2b6
-- title:
--   StochLean source theorem: StochLean.monotone_tsum_Ioc_of_nonneg

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

/-! # Local finite variation of actual absolutely summable jump series

Positive and negative cumulative series are monotone. Their difference
is the original series, so no enumeration of its countable support or
expected-variation bound is needed.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_7e65c00b693d38d872360fac {g : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ g s)) (hg : ∀ s, 0 ≤ g s) :
    Monotone (fun T : ℝ≥0 ↦ ∑' s : Ioc 0 T, g s) := by
  intro t u htu
  let hsub : Ioc (0 : ℝ≥0) t ⊆ Ioc 0 u := fun _ hs ↦ ⟨hs.1, hs.2.trans htu⟩
  exact (hs t).tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
    (fun s _ ↦ hg s) (fun _ ↦ le_rfl) (hs u)
end StochLean


