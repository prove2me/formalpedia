-- Prove2me | Definitions.Def_SourceProof_55bfecf129a3c017a43c0b43
-- name    : SourceProof_55bfecf129a3c017a43c0b43
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:48.409363+00:00
-- url     : https://prove2.me/theorems/96637c72-f891-56c9-a57a-32ec74828447
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.neg

import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_db083938190d317e3f66eea4
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

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_55bfecf129a3c017a43c0b43 (hX : IsGoodIntegrator X F P) : IsGoodIntegrator (-X) F P := by
  change ProbabilityTheory.IsGoodIntegrator (fun t ω ↦ -X t ω) F P
  simpa only [neg_one_mul] using (_root_.Prove2MeSourceProof.h_ed9d54393901c01d92a26019 hX) (-1)
end IsGoodIntegrator

end ProbabilityTheory


