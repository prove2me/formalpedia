-- Prove2me | Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591
-- name    : SourceProof_ebaf9e73dbb24b573c624591
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:09:59.767491+00:00
-- url     : https://prove2.me/theorems/91d25496-156e-58f6-b6e3-ec824f31c730
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.cutoff

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_SourceProof_c3e44575654f497031c326a7

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping the full source simple predictable class

The cutoff is `H 1_[0,τ]`, not the frozen stopped process `H^τ`. The source initial
coefficient is retained, including when the stopping time is zero. No boundedness
of coefficients or deterministic bound on the finite partition endpoints is imposed.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 (hH : IsSimplePredictable H F) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) : IsSimplePredictable (cutoffIntegrand H τ) F := by
  simpa only [hH.choose_spec] using (_root_.Prove2MeSourceProof.h_c3e44575654f497031c326a7 hH.choose) hτ
end IsSimplePredictable
end ProbabilityTheory


