-- Prove2me | Definitions.Def_SourceProof_19ffdfb9260bf3a7628b85b5
-- name    : SourceProof_19ffdfb9260bf3a7628b85b5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:31:43.827124+00:00
-- url     : https://prove2.me/theorems/63b08a6c-1ea5-5242-aed6-38eb08bbbb07
-- title:
--   StochLean source theorem: ProbabilityTheory.HasIntegrableVariation.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F000
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F001
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_3239f1038c8273faf6129713
import Definitions.Def_SourceProof_3b6770fe33c80a2ec52a585f
import Definitions.Def_SourceProof_50a177887096eaca73013898
import Definitions.Def_SourceProof_79df3f91a26f3a9f018e88d6
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping and masking integrable variation

Stopping retains the endpoint and does not increase actual total variation.
Usual cadlag adaptedness supplies measurability of the stopped path's total
variation; domination alone would not supply it. The local-property mask at
zero does not affect variation, because a process stopped at zero is constant.
This last statement does not require the initial value to vanish or be integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

namespace HasIntegrableVariation
theorem _root_.Prove2MeSourceProof.h_19ffdfb9260bf3a7628b85b5 (hX : HasIntegrableVariation X P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    HasIntegrableVariation (stoppedProcess X τ) P := by
  have hs : Adapted F (MeasureTheory.stoppedProcess X τ) :=
    ((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f ha.stronglyAdapted) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hc) hτ).adapted
  refine ⟨(_root_.Prove2MeSourceProof.h_3239f1038c8273faf6129713 hX.1) τ, hX.2.mono' ?_ ?_⟩
  · exact (((_root_.Prove2MeSourceProof.h_79df3f91a26f3a9f018e88d6 hs) hF
      ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hc) τ)).ennreal_toReal).aestronglyMeasurable
  · filter_upwards [hX.1] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hω (_root_.Prove2MeSourceProof.h_50a177887096eaca73013898 X τ ω)
end HasIntegrableVariation

end ProbabilityTheory


