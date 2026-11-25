-- Prove2me | Definitions.Def_SourceProof_c128905347c476a8d319023c
-- name    : SourceProof_c128905347c476a8d319023c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:30.909852+00:00
-- url     : https://prove2.me/theorems/35f8e4d8-7d55-4352-8235-11f95934242b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.neg

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_SourceProof_2e6ca13dfe2fe5276b1d3986

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_c128905347c476a8d319023c (hH : IsSimplePredictable H F) : IsSimplePredictable (-H) F := by
  simpa only [neg_one_smul] using (_root_.Prove2MeSourceProof.h_2e6ca13dfe2fe5276b1d3986 hH) (-1)
end IsSimplePredictable
end ProbabilityTheory


