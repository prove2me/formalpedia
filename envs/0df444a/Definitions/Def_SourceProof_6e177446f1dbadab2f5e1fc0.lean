-- Prove2me | Definitions.Def_SourceProof_6e177446f1dbadab2f5e1fc0
-- name    : SourceProof_6e177446f1dbadab2f5e1fc0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:17.000887+00:00
-- url     : https://prove2.me/theorems/e2e1e823-d084-5eb2-8477-9001dc7f95da
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_increment_step_Ico

import Definitions.Def_SourceProof_d91c9878c59cc67df92bb6e2
import Definitions.Def_SourceProof_e64beb7d64332a523896d46b
import Definitions.Def_SourceProof_f663a9831488630e6f3e2684
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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

theorem _root_.Prove2MeSourceProof.h_6e177446f1dbadab2f5e1fc0 (π : TimePartition T) {a b : ℝ≥0} (hab : a ≤ b)
    (c : ℝ) (x : ℝ≥0 → ℝ) :
    (∑ i : Fin π.size, (if a ≤ π.left i ∧ π.left i < b then c else 0) *
      (x (π.right i) - x (π.left i))) = c * (x (π.ceilingPoint b) - x (π.ceilingPoint a)) := by
  classical
  have heq := _root_.Prove2MeSourceProof.h_f663a9831488630e6f3e2684
    π.left π.right (fun i ↦ if a ≤ π.left i ∧ π.left i < b then c else 0)
    (fun _ : Unit ↦ π.ceilingPoint a) (fun _ : Unit ↦ π.ceilingPoint b) (fun _ : Unit ↦ c)
    (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) (fun _ ↦ (_root_.Prove2MeSourceProof.h_e64beb7d64332a523896d46b π) hab) (fun t ht ↦ ?_) x
  · simpa only [Fintype.sum_unique] using heq
  · simpa only [StochLean.TimePartition.leftStep, if_neg (ne_of_gt ht), Set.indicator_apply, Set.mem_Ioc,
      Fintype.sum_unique] using (_root_.Prove2MeSourceProof.h_d91c9878c59cc67df92bb6e2 π) a b c ht
end StochLean.TimePartition


