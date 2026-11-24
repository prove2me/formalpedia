-- Prove2me | Definitions.Def_SourceProof_31135d2892768ad56db3e4a8
-- name    : SourceProof_31135d2892768ad56db3e4a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:48:05.908402+00:00
-- url     : https://prove2.me/theorems/98cc5cd8-a44c-49d9-a706-3045e65a6684
-- title:
--   StochLean source theorem: StochLean.TimePartition.maxIncrement_le

import Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vanishing increments on fine deterministic partitions -/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_31135d2892768ad56db3e4a8 (π : TimePartition T) {f : ℝ≥0 → ℝ} {δ : ℝ≥0}
    (h : ∀ i, |π.increment f i| ≤ δ) : π.maxIncrement f ≤ δ := by
  apply Finset.sup_le
  intro i _
  exact_mod_cast h i
end StochLean.TimePartition


