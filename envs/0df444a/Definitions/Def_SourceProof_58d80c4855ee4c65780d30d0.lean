-- Prove2me | Definitions.Def_SourceProof_58d80c4855ee4c65780d30d0
-- name    : SourceProof_58d80c4855ee4c65780d30d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:20:29.263553+00:00
-- url     : https://prove2.me/theorems/cffbd4c2-cb3a-5f5f-95a9-1d16c9edeafc
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_hittingAfter_isOpen_of_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_SourceProof_08f7d57d38bb10b7a2a6d033
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_dc6544145c4c3d4d9a670a19

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Open-set hitting times for right-continuous processes

The owner is Mathlib's `hittingAfter`. Open hits strictly before a deterministic time
are detected on a fixed countable dense grid. Right continuity of the filtration then
gives the stopping-time property. At a finite hit the path belongs to the closure of
the target, not necessarily the open target itself.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_58d80c4855ee4c65780d30d0 {P : Measure Ω}
    (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : ProbabilityTheory.HasRightContinuousPaths X P)
    {s : Set E} (hs : IsOpen s) (a : ℝ≥0) : IsStoppingTime F (hittingAfter X s a) := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsRightContinuousPath (X · ω)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp hr)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then X 0 ω else X t ω
  have hYa : Adapted F Y := fun t ↦ Measurable.ite (F.mono bot_le _ hbad)
    ((hX 0).mono (F.mono bot_le) le_rfl) (hX t)
  have hYr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (Y · ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · intro t
      simp only [Y, if_pos hb]
      exact continuous_const.continuousWithinAt
    · simpa only [Y, if_neg hb] using
        (not_not.mp hb : ProbabilityTheory.IsRightContinuousPath (X · ω))
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  apply (_root_.Prove2MeSourceProof.h_08f7d57d38bb10b7a2a6d033 ((_root_.Prove2MeSourceProof.h_dc6544145c4c3d4d9a670a19 hYa) hYr hs a)) hF
  filter_upwards [hr] with ω hω
  have hb : ω ∉ bad := fun h ↦ h hω
  simp only [hittingAfter, Y, if_neg hb]
end Adapted

end MeasureTheory


