-- Prove2me | Definitions.Def_SourceProof_44d1656187b87c7a69eb114b
-- name    : SourceProof_44d1656187b87c7a69eb114b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:58.743058+00:00
-- url     : https://prove2.me/theorems/4bf6af0f-cac3-53f1-8095-e67d2ce9a4e4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_firstExitTruncation_eq_of_lt

import Definitions.Def_SourceProof_c9eacbbef1c8e0923f7b8eda
import Definitions.Def_SourceProof_d507c7a71143f0376195947b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded source truncation at a left-continuous first exit

The initial event `{τ > 0}` is indispensable: the source class allows an arbitrary
initial value and a distinct right limit at zero. The closed cutoff is bounded by
the threshold on this event and its elementary integral agrees strictly before `τ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

variable [F.IsRightContinuous]

theorem _root_.Prove2MeSourceProof.h_44d1656187b87c7a69eb114b
    (hH : IsSimplePredictable H F) (a : ℝ) (X : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω) :
    ((_root_.Prove2MeSourceProof.h_c9eacbbef1c8e0923f7b8eda hH) a).elementaryIntegralProcess X t ω =
      hH.elementaryIntegralProcess X t ω := by
  have hp : (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω :=
    (show (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) from WithTop.coe_le_coe.mpr bot_le).trans_lt ht
  rw [(_root_.Prove2MeSourceProof.h_d507c7a71143f0376195947b hH) a X]
  change {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v}.indicator
    (stoppedProcess (hH.elementaryIntegralProcess X) (hittingAfter H {x | a < ‖x‖} 0) t) ω = _
  rw [indicator_of_mem
    (show ω ∈ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hp)]
  exact stoppedProcess_eq_of_le ht.le
end IsSimplePredictable
end ProbabilityTheory


