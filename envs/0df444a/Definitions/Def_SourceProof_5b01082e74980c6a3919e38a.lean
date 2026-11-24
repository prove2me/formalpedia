-- Prove2me | Definitions.Def_SourceProof_5b01082e74980c6a3919e38a
-- name    : SourceProof_5b01082e74980c6a3919e38a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:06.56178+00:00
-- url     : https://prove2.me/theorems/7a9e85c5-3571-4a26-94fd-8a26a2f31107
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingPoint_lt_iff_of_mem_cell

import Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000
import Definitions.Def_StochLean_Analysis_PathVariation_StepIntegral_F000
import Definitions.Def_SourceProof_100a4fbbee9cf0e8517b3b4d
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Definitions.Def_SourceProof_d90de18cdaae59a2bf0af35c
import Definitions.Def_SourceProof_f59fc4a394228730cfab87fb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Sampling a right-continuous interval step moves its endpoints upwards

Ceilings use the original partition points and are capped at its horizon.
Repeated endpoints are allowed. The increment identity is valid for every
integrator, before any right-continuity or semimartingale assumption.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_5b01082e74980c6a3919e38a (π : TimePartition T) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) (a : ℝ≥0) :
    π.ceilingPoint a < t ↔ a ≤ π.left i := by
  constructor
  · intro ha
    rcases (_root_.Prove2MeSourceProof.h_100a4fbbee9cf0e8517b3b4d π) ((_root_.Prove2MeSourceProof.h_f59fc4a394228730cfab87fb π) a) i with h | h
    · have hm : min a T ≤ π.left i := ((_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc π) a).trans h
      rcases min_le_iff.mp hm with hleft | hT
      · exact hleft
      · exact False.elim (not_lt_of_ge hT
          (hi.1.trans_le (hi.2.trans ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) _))))
    · exact False.elim (not_lt_of_ge (hi.2.trans h) ha)
  · intro ha
    exact (π.monotone_point ((_root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c π) ((min_le_left a T).trans ha))).trans_lt hi.1
end StochLean.TimePartition


