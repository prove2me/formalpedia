-- Prove2me | Definitions.Def_SourceProof_0f8a0101c88cc3ddfc313b0a
-- name    : SourceProof_0f8a0101c88cc3ddfc313b0a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:41.037227+00:00
-- url     : https://prove2.me/theorems/5b3b33cc-f36f-4cde-bbdc-b56c289dbcae
-- title:
--   StochLean source theorem: countable_range_rightGrid

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

theorem _root_.Prove2MeSourceProof.h_0f8a0101c88cc3ddfc313b0a (n : ℕ) :
    (Set.range (rightGrid n)).Countable := by
  refine (Set.countable_range (fun k : ℕ ↦ (k : ℝ≥0) / (n + 1 : ℕ))).mono ?_
  rintro y ⟨t, rfl⟩
  exact ⟨Nat.ceil (((n + 1 : ℕ) : ℝ≥0) * t), rfl⟩
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


