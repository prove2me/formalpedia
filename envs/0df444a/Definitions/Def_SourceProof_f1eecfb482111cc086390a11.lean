-- Prove2me | Definitions.Def_SourceProof_f1eecfb482111cc086390a11
-- name    : SourceProof_f1eecfb482111cc086390a11
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:25.778206+00:00
-- url     : https://prove2.me/theorems/a1fba771-e2f2-47b1-a253-528ae0a35e11
-- title:
--   StochLean source theorem: ProbabilityTheory.leftLimitProcess_step_Ici

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact source jumps of lifetime step processes

A step activated on the closed lifetime event has left limit activated on the strict lifetime
event. Its jump is the coefficient on the lifetime graph and zero elsewhere. These formulas hold
also at zero, since the source convention is `leftLimitProcess X 0 = 0`, and an infinite lifetime
never activates at a finite time. Finite sums retain exactly the sum of their coincident jumps;
no disjointness assumption or artificial finite value for an infinite lifetime is needed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}


theorem _root_.Prove2MeSourceProof.h_f1eecfb482111cc086390a11 (a : ℝ≥0) (Z : Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess (fun s v ↦ if a ≤ s then Z v else 0) t ω =
      if a < t then Z ω else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, not_lt_zero, if_false]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
    by_cases ha : a < t
    · rw [if_pos ha]
      apply leftLim_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with s hs
      exact (if_pos (show a ≤ s from (show a < s from hs).le)).symm
    · rw [if_neg ha]
      apply leftLim_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (not_le_of_gt
        ((show s < t from hs).trans_le (le_of_not_gt ha)))).symm
end ProbabilityTheory


