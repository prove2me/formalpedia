-- Prove2me | Definitions.Def_SourceProof_d91c9878c59cc67df92bb6e2
-- name    : SourceProof_d91c9878c59cc67df92bb6e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:25:08.550513+00:00
-- url     : https://prove2.me/theorems/6b615d2f-1c6d-5402-8531-50cf5539944d
-- title:
--   StochLean source theorem: StochLean.TimePartition.leftStep_step_Ico

import Definitions.Def_SourceProof_1f1a39edad68d4f3bc6e94ca
import Definitions.Def_SourceProof_54f7c3a65933c3f46d82cbdc
import Definitions.Def_SourceProof_5b01082e74980c6a3919e38a
import Definitions.Def_SourceProof_7d62dc8056c175578484d53e
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_ffe0bffb5a465ffb7d0925ec

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

theorem _root_.Prove2MeSourceProof.h_d91c9878c59cc67df92bb6e2 (π : TimePartition T) (a b : ℝ≥0) (c : ℝ)
    {t : ℝ≥0} (ht : 0 < t) :
    π.leftStep (fun u ↦ if a ≤ u ∧ u < b then c else 0) t =
      if π.ceilingPoint a < t ∧ t ≤ π.ceilingPoint b then c else 0 := by
  by_cases htT : t ≤ T
  · obtain ⟨i, hi⟩ := (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 π) ⟨ht, htT⟩
    rw [(_root_.Prove2MeSourceProof.h_1f1a39edad68d4f3bc6e94ca π) _ hi]
    simp only [(_root_.Prove2MeSourceProof.h_5b01082e74980c6a3919e38a π) hi a, (_root_.Prove2MeSourceProof.h_ffe0bffb5a465ffb7d0925ec π) hi b]
  · rw [(_root_.Prove2MeSourceProof.h_7d62dc8056c175578484d53e π) _ (lt_of_not_ge htT)]
    have hb : ¬ t ≤ π.ceilingPoint b := fun h ↦ htT (h.trans ((_root_.Prove2MeSourceProof.h_54f7c3a65933c3f46d82cbdc π) b))
    simp only [hb, and_false, if_false]
end StochLean.TimePartition


