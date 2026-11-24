-- Prove2me | Definitions.Def_SourceProof_a239f509638bc9274841d0b5
-- name    : SourceProof_a239f509638bc9274841d0b5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:07.623003+00:00
-- url     : https://prove2.me/theorems/c8c34f93-7372-40b6-8719-67973f918acb
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.stoppedProcess

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E}

namespace Indistinguishable
omit [TopologicalSpace E] in
theorem _root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 {Y : ℝ≥0 → Ω → E}
    (h : Indistinguishable X Y P) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (stoppedProcess X τ) (stoppedProcess Y τ) P :=
  h.mono fun _ hω _ ↦ hω _
end Indistinguishable

end ProbabilityTheory


