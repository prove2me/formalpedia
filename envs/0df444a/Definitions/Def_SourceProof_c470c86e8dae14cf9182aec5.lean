-- Prove2me | Definitions.Def_SourceProof_c470c86e8dae14cf9182aec5
-- name    : SourceProof_c470c86e8dae14cf9182aec5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:33.598047+00:00
-- url     : https://prove2.me/theorems/0f1f4be6-f5c6-5027-aa12-dbfe90ce12f4
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.isNonnegativeLaw_ofFiniteMeasure

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
import Definitions.Def_SourceProof_3120093e93d873b00f0ead3c
import Definitions.Def_SourceProof_696442d2e4da6d0186632421
import Definitions.Def_SourceProof_cf83d493f8f6a74ec8af8036
import Definitions.Def_SourceProof_d332d56749c842e62ff71033
import Definitions.Def_SourceProof_fadac03da3eca60469f0808f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Compound Poisson laws

The construction is a genuine probability mixture: draw a Poisson count and then use the
corresponding convolution power of the jump law.  The zero-rate branch is proved explicitly and
does not depend on division by the intensity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace CompoundPoisson

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

section CharacteristicFunction

end CharacteristicFunction


theorem _root_.Prove2MeSourceProof.h_c470c86e8dae14cf9182aec5 (ν : FiniteMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x) :
    (ofFiniteMeasure ν).IsNonnegativeLaw := by
  by_cases hz : ν = 0
  · subst ν
    simp [_root_.Prove2MeSourceProof.h_d332d56749c842e62ff71033]
  · rw [_root_.Prove2MeSourceProof.h_3120093e93d873b00f0ead3c hz]
    apply _root_.Prove2MeSourceProof.h_cf83d493f8f6a74ec8af8036
    rw [_root_.Prove2MeSourceProof.h_fadac03da3eca60469f0808f]
    rw [ν.toMeasure_normalize_eq_of_nonzero hz]
    exact Measure.ae_smul_measure hν _
end CompoundPoisson

end ProbabilityTheory


