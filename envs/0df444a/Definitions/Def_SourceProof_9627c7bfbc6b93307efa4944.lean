-- Prove2me | Definitions.Def_SourceProof_9627c7bfbc6b93307efa4944
-- name    : SourceProof_9627c7bfbc6b93307efa4944
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:16:07.243643+00:00
-- url     : https://prove2.me/theorems/cb8d8ca1-2fab-43aa-b3bf-5e77ba4a21e9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_3b6770fe33c80a2ec52a585f
import Definitions.Def_SourceProof_5ab59237af7e9534d8f717d0
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f

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
theorem _root_.Prove2MeSourceProof.h_9627c7bfbc6b93307efa4944 (hX : IsTotalSemimartingale X F P)
    (hF : F.IsUsual P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsTotalSemimartingale (MeasureTheory.stoppedProcess X τ) F P :=
  (_root_.Prove2MeSourceProof.h_5ab59237af7e9534d8f717d0 hX) hτ
    ((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f hX.1.stronglyAdapted) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hX.2.1) hτ).adapted
end IsTotalSemimartingale

end ProbabilityTheory


