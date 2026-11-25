-- Prove2me | Definitions.Def_SourceProof_66e575b29ed1f51be78afafb
-- name    : SourceProof_66e575b29ed1f51be78afafb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:27:59.96731+00:00
-- url     : https://prove2.me/theorems/8b847ef5-72b7-4f9c-987f-5c736035163b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_stoppedFinite_eq_integralProcess

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary integral process

Protter's `J_X(H)` is the existing elementary integral evaluated against `X` stopped
at the current deterministic time. This is not another general stochastic integral.
The source initial term is retained, including at time zero.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_66e575b29ed1f51be78afafb (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (τ : FiniteStoppingTime F) (ω : Ω) :
    H.integral (stoppedProcess X τ.withTop) ω = H.integralProcess X (τ ω) ω := by
  rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf p2mMethodArg0 τ) X]
  simp only [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105, ProbabilityTheory.SimplePredictableRep.integral, min_comm]
  simp
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


