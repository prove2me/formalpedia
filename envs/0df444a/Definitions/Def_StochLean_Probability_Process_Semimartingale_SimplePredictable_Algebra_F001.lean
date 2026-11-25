-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:50:01.527904+00:00
-- url     : https://prove2.me/theorems/b1989054-45bc-47d1-afec-2b942540ea1a
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Algebra F001

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F000
import Definitions.Def_SourceProof_15e5de2b6483fa8bd27008ef

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

/-- A common-refinement realization of a binary Borel operation. -/
noncomputable def combine (H K : SimplePredictableRep F) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) : SimplePredictableRep F :=
  H.combineOn K ((_root_.Prove2MeSourceProof.h_15e5de2b6483fa8bd27008ef H.partition) K.partition).choose φ hφ
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


