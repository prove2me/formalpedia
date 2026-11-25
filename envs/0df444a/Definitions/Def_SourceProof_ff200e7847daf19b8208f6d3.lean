-- Prove2me | Definitions.Def_SourceProof_ff200e7847daf19b8208f6d3
-- name    : SourceProof_ff200e7847daf19b8208f6d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:17.429314+00:00
-- url     : https://prove2.me/theorems/349baa00-8b6f-4682-ab65-676a7cb4cc43
-- title:
--   StochLean source theorem: StochLean.TimePartition.eVariationOn_range

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_SourceProof_06cc3ff1ef6885939f260693
import Definitions.Def_SourceProof_445d46fbf60cf5615d2de765
import Definitions.Def_SourceProof_755988434e451ef665cc0eea
import Definitions.Def_SourceProof_e3ad00054b225b26545121b0
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation

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

namespace TimePartition
theorem _root_.Prove2MeSourceProof.h_ff200e7847daf19b8208f6d3 (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    eVariationOn f (Set.range π.point) = ENNReal.ofReal (pVariationSum 1 π f) := by
  rw [← (_root_.Prove2MeSourceProof.h_e3ad00054b225b26545121b0 π), eVariationOn.image_range_of_monotone f (_root_.Prove2MeSourceProof.h_755988434e451ef665cc0eea π),
    Finset.sum_range, _root_.Prove2MeSourceProof.h_445d46fbf60cf5615d2de765, ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)]
  apply sum_congr rfl
  intro i _
  have hl : π.pointNat i = π.left i := (_root_.Prove2MeSourceProof.h_06cc3ff1ef6885939f260693 π) i.castSucc
  have hr : π.pointNat (i + 1) = π.right i := (_root_.Prove2MeSourceProof.h_06cc3ff1ef6885939f260693 π) i.succ
  rw [hl, hr, edist_comm, edist_dist, Real.dist_eq]
  rfl
end TimePartition

end StochLean


