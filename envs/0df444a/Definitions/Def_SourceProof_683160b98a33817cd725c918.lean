-- Prove2me | Definitions.Def_SourceProof_683160b98a33817cd725c918
-- name    : SourceProof_683160b98a33817cd725c918
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:46:53.605585+00:00
-- url     : https://prove2.me/theorems/0c76e801-289d-5a9b-bd2e-fed5697e9888
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_zero

import Definitions.Def_SourceProof_0146b8a6534f7d6ff6a61309
import Definitions.Def_SourceProof_67aa45a3af307cb4d46b1678
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417

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

@[simp] theorem _root_.Prove2MeSourceProof.h_683160b98a33817cd725c918 (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : hH.elementaryIntegralProcess X 0 ω = H 0 ω * X 0 ω := by
  rw [(_root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 hH) hH.choose hH.choose_spec,
    _root_.Prove2MeSourceProof.h_0146b8a6534f7d6ff6a61309]
  exact congrArg (fun a ↦ a * X 0 ω)
    (by simpa using congrFun (congrFun hH.choose_spec 0) ω)
end IsSimplePredictable
end ProbabilityTheory


