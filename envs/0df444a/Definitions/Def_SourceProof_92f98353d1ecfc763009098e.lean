-- Prove2me | Definitions.Def_SourceProof_92f98353d1ecfc763009098e
-- name    : SourceProof_92f98353d1ecfc763009098e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:57.211113+00:00
-- url     : https://prove2.me/theorems/533dc325-1eef-493b-9b5b-84d45d0818c3
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_congr

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000

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

theorem _root_.Prove2MeSourceProof.h_92f98353d1ecfc763009098e (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (hHK : H = K) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral X = hK.elementaryIntegral X := by
  subst K
  rfl
end IsSimplePredictable
end ProbabilityTheory


