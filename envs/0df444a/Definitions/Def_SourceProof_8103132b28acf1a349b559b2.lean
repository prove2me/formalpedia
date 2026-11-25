-- Prove2me | Definitions.Def_SourceProof_8103132b28acf1a349b559b2
-- name    : SourceProof_8103132b28acf1a349b559b2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:34.554831+00:00
-- url     : https://prove2.me/theorems/6422af20-add1-425c-af7b-7e4f6cfbe049
-- title:
--   StochLean source theorem: StochLean.tendsto_oneVariationSum_of_rightContinuous

import Definitions.Def_SourceProof_2da1122e2444d9d7e9c19b99
import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Definitions.Def_SourceProof_d8131b6909ebfb637737f8ce

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Total variation and refinement

Klenke 21.60: the one-variation sums increase under refinement and tend to the
canonical Mathlib total variation, which may be infinite. The limit theorem is
stronger than the source nested-partition statement: continuity and vanishing
mesh suffice. Finiteness is required before any conversion to a real number.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0}


theorem _root_.Prove2MeSourceProof.h_8103132b28acf1a349b559b2 {f : ℝ≥0 → ℝ}
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ENNReal.ofReal (pVariationSum 1 (π n) f)) atTop
      (𝓝 (eVariationOn f (Icc 0 T))) := by
  apply _root_.Prove2MeSourceProof.h_d8131b6909ebfb637737f8ce
  intro t ht
  apply (hf t).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨_root_.Prove2MeSourceProof.h_2da1122e2444d9d7e9c19b99 hmesh ht.2, Eventually.of_forall (fun n ↦ ?_)⟩
  have h := (_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc (π n)) t
  rw [min_eq_left ht.2] at h
  exact h
end StochLean


