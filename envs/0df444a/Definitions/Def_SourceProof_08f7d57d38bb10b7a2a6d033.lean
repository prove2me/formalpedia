-- Prove2me | Definitions.Def_SourceProof_08f7d57d38bb10b7a2a6d033
-- name    : SourceProof_08f7d57d38bb10b7a2a6d033
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:47.224806+00:00
-- url     : https://prove2.me/theorems/94a9bd5b-b5e2-4268-b9d5-b48989b20dc8
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.congr_ae_of_usual

import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping times and null-set changes under usual conditions -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

namespace IsStoppingTime
theorem _root_.Prove2MeSourceProof.h_08f7d57d38bb10b7a2a6d033 {τ σ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hF : F.IsUsual P) (heq : τ =ᵐ[P] σ) :
    IsStoppingTime F σ := by
  intro t
  have hc : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) := fun s hs ↦
    F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  let : MeasurableSpace Ω := F t
  apply measurableSet_setOfPred.mpr
  apply (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc) (measurableSet_setOfPred.mp (hτ t))
  filter_upwards [heq] with ω hω
  exact congrArg (fun s ↦ s ≤ (t : WithTop ℝ≥0)) hω
end IsStoppingTime

end MeasureTheory


