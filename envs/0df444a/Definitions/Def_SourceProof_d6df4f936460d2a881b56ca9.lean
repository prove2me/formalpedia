-- Prove2me | Definitions.Def_SourceProof_d6df4f936460d2a881b56ca9
-- name    : SourceProof_d6df4f936460d2a881b56ca9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:51.242611+00:00
-- url     : https://prove2.me/theorems/0cd3869b-b4ca-4377-ac8b-9b4aa6674028
-- title:
--   StochLean source theorem: StochLean.tsum_Ioc_cutoff_le

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restricting a positive-time series at a closed stopping endpoint -/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_d6df4f936460d2a881b56ca9 (f : ℝ≥0 → ℝ) (a t : ℝ≥0) :
    (∑' s : Ioc 0 t, (if (s : ℝ≥0) ≤ a then f s else 0)) =
      ∑' s : Ioc 0 (min t a), f s := by
  classical
  rw [tsum_subtype (Ioc 0 t) (fun s ↦ if s ≤ a then f s else 0),
    tsum_subtype (Ioc 0 (min t a)) f]
  apply tsum_congr
  intro s
  by_cases hs0 : 0 < s <;> by_cases hst : s ≤ t <;> by_cases hsa : s ≤ a <;>
    simp only [Set.indicator, mem_Ioc, le_min_iff, hs0, hst, hsa,
      and_true, and_false, if_true, if_false]
end StochLean


