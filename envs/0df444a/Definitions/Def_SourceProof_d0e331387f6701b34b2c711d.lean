-- Prove2me | Definitions.Def_SourceProof_d0e331387f6701b34b2c711d
-- name    : SourceProof_d0e331387f6701b34b2c711d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:46.126418+00:00
-- url     : https://prove2.me/theorems/2a907116-9b55-4038-ba04-571f785c291e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.sub

import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_4100b78f80ce8fb249ea8a36
import Definitions.Def_SourceProof_55bfecf129a3c017a43c0b43
import Definitions.Def_SourceProof_fafcf0b157c21d22977aee5c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Negation and subtraction of source semimartingales -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_d0e331387f6701b34b2c711d (hX : IsGoodIntegrator X F P) (hY : IsGoodIntegrator Y F P) :
    IsGoodIntegrator (X - Y) F P := by
  simpa only [sub_eq_add_neg] using (_root_.Prove2MeSourceProof.h_fafcf0b157c21d22977aee5c hX) (_root_.Prove2MeSourceProof.h_55bfecf129a3c017a43c0b43 hY)
end IsGoodIntegrator

end ProbabilityTheory


