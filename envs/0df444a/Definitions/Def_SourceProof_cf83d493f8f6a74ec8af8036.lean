-- Prove2me | Definitions.Def_SourceProof_cf83d493f8f6a74ec8af8036
-- name    : SourceProof_cf83d493f8f6a74ec8af8036
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:12.155644+00:00
-- url     : https://prove2.me/theorems/b75c7c60-0deb-5472-82d5-1e9381083581
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.isNonnegativeLaw

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F000
import Definitions.Def_SourceProof_636c524235253bfca8198f2f
import Definitions.Def_SourceProof_f1196a71b532fc911285638d

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


theorem _root_.Prove2MeSourceProof.h_cf83d493f8f6a74ec8af8036 (r : NNReal) (μ : ProbabilityMeasure ℝ)
    (hμ : μ.IsNonnegativeLaw) : (law r μ).IsNonnegativeLaw := by
  rw [MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw]
  rw [_root_.Prove2MeSourceProof.h_f1196a71b532fc911285638d r μ measurableSet_Ici]
  have hpow : ∀ n : ℕ,
      (MeasureTheory.ProbabilityMeasure.convPow μ n : Measure ℝ) (Set.Ici 0) = 1 := by
    intro n
    exact (_root_.Prove2MeSourceProof.h_636c524235253bfca8198f2f hμ) n
  simp_rw [hpow]
  simp
end CompoundPoisson

end ProbabilityTheory


