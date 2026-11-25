-- Prove2me | Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
-- name    : SourceProof_5caa95db89fdd596c2cde105
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:12:52.427825+00:00
-- url     : https://prove2.me/theorems/260b4318-8fcf-5aff-8cdf-dbc5f7ced6b3
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integralProcess_apply

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000

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

theorem _root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    H.integralProcess X t ω = H.initial ω * X 0 ω +
      ∑ i, H.coefficient i ω * (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω) := by
  simp only [ProbabilityTheory.SimplePredictableRep.integralProcess, integral, min_eq_left (show (0 : ℝ≥0) ≤ t from bot_le)]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


