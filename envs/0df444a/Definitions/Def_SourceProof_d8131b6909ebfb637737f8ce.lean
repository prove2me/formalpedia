-- Prove2me | Definitions.Def_SourceProof_d8131b6909ebfb637737f8ce
-- name    : SourceProof_d8131b6909ebfb637737f8ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:42.609221+00:00
-- url     : https://prove2.me/theorems/4e8603c5-fbeb-4346-9b57-5a03f10846a0
-- title:
--   StochLean source theorem: StochLean.tendsto_oneVariationSum_of_ceiling_tendsto

import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_e64beb7d64332a523896d46b
import Definitions.Def_SourceProof_f59fc4a394228730cfab87fb
import Definitions.Def_SourceProof_ff200e7847daf19b8208f6d3

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


theorem _root_.Prove2MeSourceProof.h_d8131b6909ebfb637737f8ce {f : ℝ≥0 → ℝ} {π : ℕ → TimePartition T}
    (happrox : ∀ t ∈ Icc 0 T,
      Tendsto (fun n ↦ f ((π n).ceilingPoint t)) atTop (𝓝 (f t))) :
    Tendsto (fun n ↦ ENNReal.ofReal (pVariationSum 1 (π n) f)) atTop
      (𝓝 (eVariationOn f (Icc 0 T))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eVariationOn.lowerSemicontinuous_aux happrox ha] with n hn
    apply hn.trans_le
    rw [← (_root_.Prove2MeSourceProof.h_ff200e7847daf19b8208f6d3 (π n))]
    exact eVariationOn.comp_le_of_monotoneOn f (π n).ceilingPoint
      ((_root_.Prove2MeSourceProof.h_e64beb7d64332a523896d46b (π n)).monotoneOn _) (fun t _ ↦ (_root_.Prove2MeSourceProof.h_f59fc4a394228730cfab87fb (π n)) t)
  · intro b hb
    apply Eventually.of_forall
    intro n
    rw [← (_root_.Prove2MeSourceProof.h_ff200e7847daf19b8208f6d3 (π n))]
    exact (eVariationOn.mono f (by
      rintro t ⟨i, rfl⟩
      exact ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) i⟩)).trans_lt hb
end StochLean


