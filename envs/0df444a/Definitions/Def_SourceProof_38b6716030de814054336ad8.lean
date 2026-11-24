-- Prove2me | Definitions.Def_SourceProof_38b6716030de814054336ad8
-- name    : SourceProof_38b6716030de814054336ad8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:25.311622+00:00
-- url     : https://prove2.me/theorems/f20884eb-5c6d-47a2-bcb7-8657c70284d8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsRightContinuousPath.min_const

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping preserves common-event path regularity -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] {x : ℝ≥0 → E}

namespace IsRightContinuousPath
theorem _root_.Prove2MeSourceProof.h_38b6716030de814054336ad8 (hx : IsRightContinuousPath x) (T : ℝ≥0) :
    IsRightContinuousPath (fun t ↦ x (min t T)) := by
  intro t
  exact (hx (min t T)).comp (f := fun s ↦ min s T) (x := t)
    (continuous_id.min continuous_const).continuousWithinAt
    (fun _ hu ↦ min_le_min_right T hu)
end IsRightContinuousPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E}

end ProbabilityTheory


