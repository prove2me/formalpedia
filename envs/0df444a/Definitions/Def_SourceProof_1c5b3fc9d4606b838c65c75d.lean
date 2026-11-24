-- Prove2me | Definitions.Def_SourceProof_1c5b3fc9d4606b838c65c75d
-- name    : SourceProof_1c5b3fc9d4606b838c65c75d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:44:52.573909+00:00
-- url     : https://prove2.me/theorems/a8c24d48-b4ef-4e7b-ad6b-969f899a4110
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_congr_integrator_path

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_6917b09fe59e5bd92fe810d4
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
theorem _root_.Prove2MeSourceProof.h_1c5b3fc9d4606b838c65c75d
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) {ω : Ω}
    (hXY : ∀ t, X t ω = Y t ω) : hH.elementaryIntegral X ω = hH.elementaryIntegral Y ω :=
  (_root_.Prove2MeSourceProof.h_6917b09fe59e5bd92fe810d4 hH.choose) hXY
end IsSimplePredictable

variable [IsFiniteMeasure P]

end ProbabilityTheory


