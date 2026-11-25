-- Prove2me | Definitions.Def_SourceProof_2e6ca13dfe2fe5276b1d3986
-- name    : SourceProof_2e6ca13dfe2fe5276b1d3986
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:12.354462+00:00
-- url     : https://prove2.me/theorems/72eef57e-19d1-58f5-806e-0bb774efa9e0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.smul

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
import Definitions.Def_SourceProof_3d83037636fda5e157d51fda

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

theorem _root_.Prove2MeSourceProof.h_2e6ca13dfe2fe5276b1d3986 (hH : IsSimplePredictable H F) (c : ℝ) : IsSimplePredictable (c • H) F := by
  refine ⟨hH.choose.scale c, ?_⟩
  rw [_root_.Prove2MeSourceProof.h_3d83037636fda5e157d51fda, hH.choose_spec]
  rfl
end IsSimplePredictable
end ProbabilityTheory


