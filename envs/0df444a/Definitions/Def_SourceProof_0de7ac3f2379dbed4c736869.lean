-- Prove2me | Definitions.Def_SourceProof_0de7ac3f2379dbed4c736869
-- name    : SourceProof_0de7ac3f2379dbed4c736869
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:24.166995+00:00
-- url     : https://prove2.me/theorems/414f8400-9f49-42c9-85c9-4220814a6585
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_congr_indistinguishable

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_1c5b3fc9d4606b838c65c75d
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_0de7ac3f2379dbed4c736869
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (hXY : Indistinguishable X Y P) :
    hH.elementaryIntegral X =ᵐ[P] hH.elementaryIntegral Y :=
  hXY.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_1c5b3fc9d4606b838c65c75d hH) hω
end IsSimplePredictable

variable [IsFiniteMeasure P]

end ProbabilityTheory


