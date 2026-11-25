-- Prove2me | Definitions.Def_SourceProof_042946cfff92727bdbde6373
-- name    : SourceProof_042946cfff92727bdbde6373
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:03.683797+00:00
-- url     : https://prove2.me/theorems/83df1f13-0963-5645-956f-97f091e0704b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_sub_integrator

import Definitions.Def_SourceProof_91d4ba8f2109bec210ef531a
import Definitions.Def_SourceProof_f9163e64a89a6717e7883932

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
theorem _root_.Prove2MeSourceProof.h_042946cfff92727bdbde6373
    (hH : IsSimplePredictable H F) (X Y : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (X - Y) =
      hH.elementaryIntegralProcess X - hH.elementaryIntegralProcess Y := by
  rw [sub_eq_add_neg, (_root_.Prove2MeSourceProof.h_91d4ba8f2109bec210ef531a hH),
    (_root_.Prove2MeSourceProof.h_f9163e64a89a6717e7883932 hH), sub_eq_add_neg]
end IsSimplePredictable

end ProbabilityTheory


