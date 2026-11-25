-- Prove2me | Definitions.Def_SourceProof_be4dfea3ac57333b7efb8bb1
-- name    : SourceProof_be4dfea3ac57333b7efb8bb1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:26.806666+00:00
-- url     : https://prove2.me/theorems/ef3431ab-2b48-428d-a502-f49b97b9da3e
-- title:
--   StochLean source theorem: StochLean.TimePartition.maxIncrement_tendsto_zero

import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_31135d2892768ad56db3e4a8
import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_eaa152490266b02f7461a510

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


theorem _root_.Prove2MeSourceProof.h_be4dfea3ac57333b7efb8bb1 {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ((π n).maxIncrement f : ℝ)) atTop (𝓝 0) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (NNReal.coe_nonneg _)
  · intro ε hε
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
    filter_upwards [hmesh.eventually_lt_const hη] with n hn
    have hinc : ∀ i, |(π n).increment f i| ≤ ε / 2 := by
      intro i
      apply le_of_lt
      apply hmod _ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩
        _ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩
      change dist ((π n).right i) ((π n).left i) < η
      rw [(_root_.Prove2MeSourceProof.h_eaa152490266b02f7461a510 (π n))]
      exact (show ((π n).gap i : ℝ) ≤ ((π n).mesh : ℝ) by
        exact_mod_cast (_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 (π n)) i).trans_lt hn
    have hb := (_root_.Prove2MeSourceProof.h_31135d2892768ad56db3e4a8 (δ := ⟨ε / 2, by positivity⟩) (π n)) hinc
    exact (show ((π n).maxIncrement f : ℝ) ≤ ε / 2 from
      NNReal.coe_le_coe.mpr hb).trans_lt (by linarith)
end StochLean.TimePartition


