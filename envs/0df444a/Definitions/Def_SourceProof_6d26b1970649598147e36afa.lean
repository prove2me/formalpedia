-- Prove2me | Definitions.Def_SourceProof_6d26b1970649598147e36afa
-- name    : SourceProof_6d26b1970649598147e36afa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:47:09.95743+00:00
-- url     : https://prove2.me/theorems/d7fb1056-76e7-5efe-a827-7e9c7ad95d2b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_combine

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_SourceProof_15e5de2b6483fa8bd27008ef
import Definitions.Def_SourceProof_929d91cc8c3fee0fc2fa1acb
import Definitions.Def_SourceProof_96c840413a5bd52fd9e42aec

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

theorem _root_.Prove2MeSourceProof.h_6d26b1970649598147e36afa (H K : SimplePredictableRep F) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (h0 : φ 0 0 = 0) :
    (H.combine K φ hφ).toProcess = fun t ω ↦ φ (H.toProcess t ω) (K.toProcess t ω) := by
  obtain ⟨hH, hK⟩ := ((_root_.Prove2MeSourceProof.h_15e5de2b6483fa8bd27008ef H.partition) K.partition).choose_spec
  rw [ProbabilityTheory.SimplePredictableRep.combine, _root_.Prove2MeSourceProof.h_929d91cc8c3fee0fc2fa1acb H K _ φ hφ h0,
    (_root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec H) hH, (_root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec K) hK]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


