-- Prove2me | Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
-- name    : SourceProof_0f93b663621787fcc9aa0ad4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:30.942125+00:00
-- url     : https://prove2.me/theorems/b5beeb38-cd65-4600-9a3e-02587871a7c3
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.stoppedValue

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
theorem _root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 {Y : ℝ≥0 → Ω → E}
    (h : Indistinguishable X Y P) (τ : Ω → WithTop ℝ≥0) :
    stoppedValue X τ =ᵐ[P] stoppedValue Y τ :=
  h.mono fun _ hω ↦ hω _
end Indistinguishable

end ProbabilityTheory


