-- Prove2me | Definitions.Def_SourceProof_98b90b63a7c20b2905dd0848
-- name    : SourceProof_98b90b63a7c20b2905dd0848
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:43.492796+00:00
-- url     : https://prove2.me/theorems/19a11e1e-b800-4ced-945b-c43649a20fcf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.neg

import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_ed9d54393901c01d92a26019

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

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_98b90b63a7c20b2905dd0848 (hX : IsSemimartingale X F P) : IsSemimartingale (-X) F P := by
  change ProbabilityTheory.IsSemimartingale (fun t ω ↦ -X t ω) F P
  simpa only [neg_one_mul] using (_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) (-1)
end IsSemimartingale

end ProbabilityTheory


