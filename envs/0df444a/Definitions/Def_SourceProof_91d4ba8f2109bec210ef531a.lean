-- Prove2me | Definitions.Def_SourceProof_91d4ba8f2109bec210ef531a
-- name    : SourceProof_91d4ba8f2109bec210ef531a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:19.538452+00:00
-- url     : https://prove2.me/theorems/1e6bb3ea-bd9a-4139-8879-114cadb45fc6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_add_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_487832d6cb2410ff018577d0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linearity of the elementary integral process in its integrator -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {H : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_91d4ba8f2109bec210ef531a
    (hH : IsSimplePredictable H F) (X Y : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (X + Y) =
      hH.elementaryIntegralProcess X + hH.elementaryIntegralProcess Y := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_487832d6cb2410ff018577d0 hH) (fun s ω ↦ X (min s t) ω)
    (fun s ω ↦ Y (min s t) ω)
end IsSimplePredictable

end ProbabilityTheory


