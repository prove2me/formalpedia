-- Prove2me | Definitions.Def_SourceProof_59ed35988bf791fd6e7e31bb
-- name    : SourceProof_59ed35988bf791fd6e7e31bb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:08:11.556092+00:00
-- url     : https://prove2.me/theorems/b123fa6a-4774-48e9-9482-d7ee6de673a7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_SourceProof_3f363a7f74dc18c6b2d72139

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

theorem _root_.Prove2MeSourceProof.h_59ed35988bf791fd6e7e31bb (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F) :
    IsSimplePredictable (H + K) F :=
  (_root_.Prove2MeSourceProof.h_3f363a7f74dc18c6b2d72139 hH) hK (· + ·) (measurable_fst.add measurable_snd) (add_zero 0)
end IsSimplePredictable
end ProbabilityTheory


