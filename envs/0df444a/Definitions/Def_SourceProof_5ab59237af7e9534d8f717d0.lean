-- Prove2me | Definitions.Def_SourceProof_5ab59237af7e9534d8f717d0
-- name    : SourceProof_5ab59237af7e9534d8f717d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:42.334859+00:00
-- url     : https://prove2.me/theorems/729322d7-1d93-5dbf-adbe-b765c73f2365
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.stoppedProcess_of_adapted

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_8510e2a398f823aff8350c3b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping source good integrators and semimartingales

The good-integrator proof uses actual source cutoff closure and elementary stopping,
not a classical semimartingale decomposition or a postulated general integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_5ab59237af7e9534d8f717d0 (hX : IsTotalSemimartingale X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (ha : Adapted F (MeasureTheory.stoppedProcess X τ)) :
    IsTotalSemimartingale (MeasureTheory.stoppedProcess X τ) F P :=
  ⟨ha, (_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hX.2.1) τ, (_root_.Prove2MeSourceProof.h_8510e2a398f823aff8350c3b hX.2.2) hτ⟩
end IsTotalSemimartingale

end ProbabilityTheory


