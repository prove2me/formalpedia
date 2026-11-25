-- Prove2me | Definitions.Def_SourceProof_ef6358ad5b934038709df8f0
-- name    : SourceProof_ef6358ad5b934038709df8f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:33:00.117976+00:00
-- url     : https://prove2.me/theorems/459718b3-a249-4f1d-968a-2ff0dcee66b3
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.neg

import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_db083938190d317e3f66eea4

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
theorem _root_.Prove2MeSourceProof.h_ef6358ad5b934038709df8f0 (hX : IsTotalSemimartingale X F P) :
    IsTotalSemimartingale (-X) F P := by
  change ProbabilityTheory.IsTotalSemimartingale (fun t ω ↦ -X t ω) F P
  simpa only [neg_one_mul] using (_root_.Prove2MeSourceProof.h_db083938190d317e3f66eea4 hX) (-1)
end IsTotalSemimartingale

end ProbabilityTheory


