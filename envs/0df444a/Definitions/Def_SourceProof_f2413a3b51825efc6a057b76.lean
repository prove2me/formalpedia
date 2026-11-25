-- Prove2me | Definitions.Def_SourceProof_f2413a3b51825efc6a057b76
-- name    : SourceProof_f2413a3b51825efc6a057b76
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:07:30.992255+00:00
-- url     : https://prove2.me/theorems/4d89119d-fb55-4ab9-a89c-c51e24cc4847
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.mul

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

theorem _root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F) :
    IsSimplePredictable (H * K) F :=
  (_root_.Prove2MeSourceProof.h_3f363a7f74dc18c6b2d72139 hH) hK (· * ·) (measurable_fst.mul measurable_snd) (mul_zero 0)
end IsSimplePredictable
end ProbabilityTheory


