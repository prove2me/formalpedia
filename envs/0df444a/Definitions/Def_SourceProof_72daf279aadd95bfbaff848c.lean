-- Prove2me | Definitions.Def_SourceProof_72daf279aadd95bfbaff848c
-- name    : SourceProof_72daf279aadd95bfbaff848c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:01.734986+00:00
-- url     : https://prove2.me/theorems/0aed8d97-5bc1-567b-a347-6718da7474ca
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.largeJumpNormSumProcess_stopped_joint_exit_le

import Definitions.Def_SourceProof_33c8d48450307c7c064de424
import Definitions.Def_SourceProof_7b2577ad98c1b05c2fcc98eb
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

theorem _root_.Prove2MeSourceProof.h_72daf279aadd95bfbaff848c
    (hx : IsCadlagPath (X · ω)) (hb : 0 < b) (n : ℕ) (t : ℝ≥0) :
    stoppedProcess (largeJumpNormSumProcess X b)
      (cappedNormExitSequence (fun s v ↦ largeJumpNormSumProcess X b s v + ‖X s v‖) n)
      t ω ≤ 2 * ((n + 1 : ℕ) : ℝ) +
        ‖X ((cappedNormExitSequence
          (fun s v ↦ largeJumpNormSumProcess X b s v + ‖X s v‖) n ω).untopA) ω‖ := by
  let C := ProbabilityTheory.largeJumpNormSumProcess X b
  let Z : ℝ≥0 → Ω → ℝ := fun s v ↦ C s v + ‖X s v‖
  let ρ := ProbabilityTheory.cappedNormExitSequence Z n
  let r : ℝ≥0 := (ρ ω).untopA
  have hfin : ρ ω ≠ ⊤ := _root_.Prove2MeSourceProof.h_33c8d48450307c7c064de424 Z n ω
  have hr : (r : WithTop ℝ≥0) = ρ ω := by
    dsimp only [r]
    rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  have hclock : (min (t : WithTop ℝ≥0) (ρ ω)).untopA ≤ r := by
    apply WithTop.untopA_le
    rw [hr]
    exact min_le_right _ _
  have hbR : C r ω ≤ 2 * ((n + 1 : ℕ) : ℝ) + ‖X r ω‖ :=
    (_root_.Prove2MeSourceProof.h_7b2577ad98c1b05c2fcc98eb hx) hb hr.le
  change C ((min (t : WithTop ℝ≥0) (ρ ω)).untopA) ω ≤ _
  exact ((_root_.Prove2MeSourceProof.h_de298d81ae177af385de3ac2 hx) hb hclock).trans hbR
end IsCadlagPath

end ProbabilityTheory


