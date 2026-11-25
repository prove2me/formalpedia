-- Prove2me | Definitions.Def_SourceProof_673028e029d6cd61fe3f19f1
-- name    : SourceProof_673028e029d6cd61fe3f19f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:45.557457+00:00
-- url     : https://prove2.me/theorems/6e7765d3-dcb1-488e-87ee-8d1aa10a3321
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.norm_firstExitTruncation_le

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_08f35e40de15386d6fd32725
import Definitions.Def_SourceProof_1d54cd29abd24002abe388d1

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

theorem _root_.Prove2MeSourceProof.h_673028e029d6cd61fe3f19f1 (hH : IsSimplePredictable H F)
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ≥0) (ω : Ω) : ‖firstExitTruncation H a t ω‖ ≤ a := by
  classical
  by_cases hpos : (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω
  · rw [ProbabilityTheory.firstExitTruncation, indicator_of_mem
      (show ω ∈ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos)]
    by_cases ht : (t : WithTop ℝ≥0) ≤ hittingAfter H {x | a < ‖x‖} 0 ω
    · simp only [ProbabilityTheory.cutoffIntegrand, if_pos ht]
      exact _root_.Prove2MeSourceProof.h_1d54cd29abd24002abe388d1 ((_root_.Prove2MeSourceProof.h_08f35e40de15386d6fd32725 hH) ω).1 hpos ht
    · simpa only [ProbabilityTheory.cutoffIntegrand, if_neg ht, norm_zero] using ha
  · simpa only [ProbabilityTheory.firstExitTruncation, indicator_of_notMem
      (show ω ∉ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos),
      norm_zero] using ha
variable [F.IsRightContinuous]

end IsSimplePredictable
end ProbabilityTheory


