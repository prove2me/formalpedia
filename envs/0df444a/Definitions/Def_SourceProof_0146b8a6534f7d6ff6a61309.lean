-- Prove2me | Definitions.Def_SourceProof_0146b8a6534f7d6ff6a61309
-- name    : SourceProof_0146b8a6534f7d6ff6a61309
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:34:27.043824+00:00
-- url     : https://prove2.me/theorems/5a64a386-97ee-5fe3-85af-8bcf65402c95
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integralProcess_zero

import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105

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

@[simp] theorem _root_.Prove2MeSourceProof.h_0146b8a6534f7d6ff6a61309 (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : H.integralProcess X 0 ω = H.initial ω * X 0 ω := by
  simp [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


