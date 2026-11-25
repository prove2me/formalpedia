-- Prove2me | Definitions.Def_SourceProof_d14c6a5c22923c1d07f1756e
-- name    : SourceProof_d14c6a5c22923c1d07f1756e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:16:37.401587+00:00
-- url     : https://prove2.me/theorems/763a4797-78a4-413a-b808-4bcf3aff1446
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_cutoff

import Definitions.Def_SourceProof_30142169a7dbed2f4e087a36
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591

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

theorem _root_.Prove2MeSourceProof.h_d14c6a5c22923c1d07f1756e (hH : IsSimplePredictable H F)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hτ).elementaryIntegral X = hH.elementaryIntegral (stoppedProcess X τ) := by
  apply (_root_.Prove2MeSourceProof.h_30142169a7dbed2f4e087a36 hH.choose) ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hτ).choose τ
  rw [((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hτ).choose_spec, hH.choose_spec]
end IsSimplePredictable
end ProbabilityTheory


