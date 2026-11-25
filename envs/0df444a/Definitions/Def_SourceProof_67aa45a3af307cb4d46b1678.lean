-- Prove2me | Definitions.Def_SourceProof_67aa45a3af307cb4d46b1678
-- name    : SourceProof_67aa45a3af307cb4d46b1678
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:52.095228+00:00
-- url     : https://prove2.me/theorems/e236181b-dc50-4293-a98a-13ae1990faee
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_eq

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_ec04cdbdbe92b05b4697a078

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

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 (hH : IsSimplePredictable H F)
    (R : SimplePredictableRep F) (hR : R.toProcess = H) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess X = R.integralProcess X := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 hH) R hR _
end IsSimplePredictable
end ProbabilityTheory


