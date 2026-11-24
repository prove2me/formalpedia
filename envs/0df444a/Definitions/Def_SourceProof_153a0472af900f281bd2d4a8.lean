-- Prove2me | Definitions.Def_SourceProof_153a0472af900f281bd2d4a8
-- name    : SourceProof_153a0472af900f281bd2d4a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:09.79007+00:00
-- url     : https://prove2.me/theorems/4099db96-0422-449a-a0da-c476fef989c7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.jumpProcess_min_const

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_0cd12103eb000692396f52e4
import Definitions.Def_SourceProof_36f071daa4d958dd1bd65126
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source jumps of stopped cadlag paths

The endpoint jump is included: the cutoff is `t <= tau`, not `t < tau`.
The original initial jump is retained, including when the stopping time is zero.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_153a0472af900f281bd2d4a8 (hX : IsCadlagPath (X · ω)) (a t : ℝ≥0) :
    jumpProcess (fun u v ↦ X (min u a) v) t ω =
      if t ≤ a then jumpProcess X t ω else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_36f071daa4d958dd1bd65126, if_pos (show (0 : ℝ≥0) ≤ a from bot_le),
      min_eq_left (show (0 : ℝ≥0) ≤ a from bot_le)]
  · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    have hl : ProbabilityTheory.leftLimitProcess (fun u v ↦ X (min u a) v) t ω =
        if a < t then X a ω else ProbabilityTheory.leftLimitProcess X t ω := by
      rw [ProbabilityTheory.leftLimitProcess, if_neg ht]
      apply leftLim_eq_of_tendsto
      simpa only [min_comm] using (_root_.Prove2MeSourceProof.h_0cd12103eb000692396f52e4 hX) ht a
    change X (min t a) ω - ProbabilityTheory.leftLimitProcess (fun u v ↦ X (min u a) v) t ω = _
    rw [hl]
    by_cases ha : a < t
    · simp only [if_pos ha, min_eq_right ha.le, sub_self, if_neg (not_le_of_gt ha)]
    · simp only [if_neg ha, min_eq_left (le_of_not_gt ha), if_pos (le_of_not_gt ha)]
      rfl
end IsCadlagPath

end ProbabilityTheory


