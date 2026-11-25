-- Prove2me | Definitions.Def_SourceProof_76e6f1c00540bd94935e0dc0
-- name    : SourceProof_76e6f1c00540bd94935e0dc0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:07.133063+00:00
-- url     : https://prove2.me/theorems/6df05046-c5d1-594f-93cb-c7b2dafd4bbf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.sub

import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_4100b78f80ce8fb249ea8a36
import Definitions.Def_SourceProof_ef6358ad5b934038709df8f0

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

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_76e6f1c00540bd94935e0dc0
    (hX : IsTotalSemimartingale X F P) (hY : IsTotalSemimartingale Y F P) :
    IsTotalSemimartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using (_root_.Prove2MeSourceProof.h_4100b78f80ce8fb249ea8a36 hX) (_root_.Prove2MeSourceProof.h_ef6358ad5b934038709df8f0 hY)
end IsTotalSemimartingale

end ProbabilityTheory


