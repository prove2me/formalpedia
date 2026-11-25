-- Prove2me | Definitions.Def_SourceProof_cc0035184dadaa0334c1eb46
-- name    : SourceProof_cc0035184dadaa0334c1eb46
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:54.615025+00:00
-- url     : https://prove2.me/theorems/f5e61e55-48f2-4d3c-b18f-37ebc3e71f22
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_sub

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_6237982d4014ad406249e8ad
import Definitions.Def_SourceProof_bc53441c2020b643491018cd

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

theorem _root_.Prove2MeSourceProof.h_cc0035184dadaa0334c1eb46 (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd hH) hK).elementaryIntegralProcess X =
      hH.elementaryIntegralProcess X - hK.elementaryIntegralProcess X := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_6237982d4014ad406249e8ad hH) hK _
end IsSimplePredictable
end ProbabilityTheory


