-- Prove2me | Definitions.Def_SourceProof_7b2577ad98c1b05c2fcc98eb
-- name    : SourceProof_7b2577ad98c1b05c2fcc98eb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:28.716715+00:00
-- url     : https://prove2.me/theorems/2928d806-1e84-4b7e-bb0e-f008e2edfc23
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.largeJumpNormSumProcess_le_before_joint_exit

import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_72a1ab211be956ee5d818cd1
import Definitions.Def_SourceProof_752c0bc3f1b08be0f7be8e77
import Definitions.Def_SourceProof_8721f78b0017a7455a9a15ba
import Definitions.Def_SourceProof_db883fb799e1ec461a70ab4f
import Definitions.Def_SourceProof_de298d81ae177af385de3ac2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual large-jump variation at a joint norm exit

Write `C` for the actual cumulative norm of the large positive-time jumps.
The existing capped norm exits of `C + norm X` bound both summands strictly
before exit. Their genuine left limits retain those bounds at the exit,
and the exact jump of `C` is at most the norm of the jump of `X`.

The resulting bound retains the actual possibly overshooting value of `X`.
It does not assert that the stopped original process is bounded. The case
of an exit at zero uses `C 0 = 0` and needs no initial-value hypothesis on
`X`. All exit samples are explicitly known finite before `untopA` is used.
No filtration, measurability, moment, or martingale premise is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_7b2577ad98c1b05c2fcc98eb
    (hx : IsCadlagPath (X · ω)) (hb : 0 < b) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ cappedNormExitSequence
      (fun s v ↦ largeJumpNormSumProcess X b s v + ‖X s v‖) n ω) :
    largeJumpNormSumProcess X b t ω ≤ 2 * ((n + 1 : ℕ) : ℝ) + ‖X t ω‖ := by
  let C := ProbabilityTheory.largeJumpNormSumProcess X b
  let Z : ℝ≥0 → Ω → ℝ := fun s v ↦ C s v + ‖X s v‖
  have hc : ProbabilityTheory.IsCadlagPath (C · ω) := ((_root_.Prove2MeSourceProof.h_72a1ab211be956ee5d818cd1 hx) hb).2
  have hm : Monotone (C · ω) := (_root_.Prove2MeSourceProof.h_de298d81ae177af385de3ac2 hx) hb
  have hC0 : C 0 ω = 0 := congrFun (_root_.Prove2MeSourceProof.h_8721f78b0017a7455a9a15ba X b).2 ω
  have hnC (s : ℝ≥0) : 0 ≤ C s ω := by
    have h := hm (bot_le : (0 : ℝ≥0) ≤ s)
    change C 0 ω ≤ C s ω at h
    rwa [hC0] at h
  by_cases hz : t = 0
  · subst t
    change C 0 ω ≤ _
    rw [hC0]
    positivity
  have hp : 0 < t := pos_iff_ne_zero.mpr hz
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
  have hpre (s : ℝ≥0) (hs : s < t) :
      C s ω ≤ ((n + 1 : ℕ) : ℝ) ∧ ‖X s ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    have hclock : (s : WithTop ℝ≥0) < ProbabilityTheory.cappedNormExitSequence Z n ω :=
      (WithTop.coe_lt_coe.mpr hs).trans_le ht
    have hbound := _root_.Prove2MeSourceProof.h_752c0bc3f1b08be0f7be8e77 hclock
    change ‖C s ω + ‖X s ω‖‖ ≤ ((n + 1 : ℕ) : ℝ) at hbound
    rw [Real.norm_of_nonneg (add_nonneg (hnC s) (norm_nonneg _))] at hbound
    constructor <;> linarith only [hbound, hnC s, norm_nonneg (X s ω)]
  have hlC : ProbabilityTheory.leftLimitProcess C t ω ≤ ((n + 1 : ℕ) : ℝ) := by
    apply le_of_tendsto ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hc) hz)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hpre s hs).1
  have hlX : ‖ProbabilityTheory.leftLimitProcess X t ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    apply le_of_tendsto ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hx) hz).norm
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hpre s hs).2
  have hjC : ProbabilityTheory.jumpProcess C t ω =
      if b < ‖ProbabilityTheory.jumpProcess X t ω‖ then ‖ProbabilityTheory.jumpProcess X t ω‖ else 0 := by
    change C t ω - ProbabilityTheory.leftLimitProcess C t ω = _
    rw [ProbabilityTheory.leftLimitProcess, if_neg hz]
    exact ((_root_.Prove2MeSourceProof.h_db883fb799e1ec461a70ab4f hx) hb hp).2
  have hjle : ProbabilityTheory.jumpProcess C t ω ≤ ‖ProbabilityTheory.jumpProcess X t ω‖ := by
    rw [hjC]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hjX : ‖ProbabilityTheory.jumpProcess X t ω‖ ≤ ‖X t ω‖ + ‖ProbabilityTheory.leftLimitProcess X t ω‖ :=
    norm_sub_le _ _
  have heC : C t ω = ProbabilityTheory.jumpProcess C t ω + ProbabilityTheory.leftLimitProcess C t ω :=
    (sub_add_cancel _ _).symm
  change C t ω ≤ _
  linarith only [hlC, hlX, hjle, hjX, heC]
end IsCadlagPath

end ProbabilityTheory


