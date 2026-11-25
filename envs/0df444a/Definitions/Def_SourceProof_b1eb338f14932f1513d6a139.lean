-- Prove2me | Definitions.Def_SourceProof_b1eb338f14932f1513d6a139
-- name    : SourceProof_b1eb338f14932f1513d6a139
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:26.469992+00:00
-- url     : https://prove2.me/theorems/04e8b85a-099a-47a7-a9e2-8921932200dc
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integralProcess_congr

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_SourceProof_f1dc368dba361aa17c9bfbeb

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

theorem _root_.Prove2MeSourceProof.h_b1eb338f14932f1513d6a139 (H K : SimplePredictableRep F) (hHK : H.toProcess = K.toProcess)
    (X : ℝ≥0 → Ω → ℝ) : H.integralProcess X = K.integralProcess X := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_f1dc368dba361aa17c9bfbeb H) K hHK _
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


