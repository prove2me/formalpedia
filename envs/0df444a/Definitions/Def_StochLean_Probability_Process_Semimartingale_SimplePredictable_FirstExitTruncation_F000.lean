-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:07:17.949905+00:00
-- url     : https://prove2.me/theorems/e401bd43-bf21-4de9-ab79-60b8863741ea
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.FirstExitTruncation F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_SourceProof_ba15608e2ab7164b205d1611
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

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

/-- The source first-exit cutoff with the Protter initial-event mask. -/
noncomputable def firstExitTruncation (H : ℝ≥0 → Ω → ℝ) (a : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ {ω | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω}.indicator
    (cutoffIntegrand H (hittingAfter H {x | a < ‖x‖} 0) t)
namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

variable [F.IsRightContinuous]

end IsSimplePredictable
end ProbabilityTheory


