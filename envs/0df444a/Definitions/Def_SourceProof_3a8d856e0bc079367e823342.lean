-- Prove2me | Definitions.Def_SourceProof_3a8d856e0bc079367e823342
-- name    : SourceProof_3a8d856e0bc079367e823342
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:34.326822+00:00
-- url     : https://prove2.me/theorems/24a42c8c-1227-4849-a9a7-5348c15e2d03
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_gap

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F001
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Deterministic variation along finite partitions

This layer has no probability space or filtration. Partitions may repeat endpoints;
zero-length cells contribute zero to quadratic variation. The empty partition is
available precisely at horizon zero. Raw stochastic brackets, which retain the
initial square, are not defined here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal Topology BigOperators

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_3a8d856e0bc079367e823342 (π : TimePartition T) : (∑ i, (π.gap i : ℝ)) = T := by
  have h := (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 π) (fun t ↦ (t : ℝ))
  simp only [StochLean.TimePartition.increment, NNReal.coe_zero, sub_zero] at h
  simpa only [StochLean.TimePartition.gap, NNReal.coe_sub ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) _)] using h
end TimePartition

variable {T : ℝ≥0}

end StochLean


