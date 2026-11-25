-- Prove2me | Definitions.Def_SourceProof_6f80af65b6d22255a398a6e4
-- name    : SourceProof_6f80af65b6d22255a398a6e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:15:53.261014+00:00
-- url     : https://prove2.me/theorems/c4a14679-9ad1-5453-b027-b6e6042ac4af
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.charFun_convPow

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Basic_F000
import Definitions.Def_SourceProof_cce2f2b17a1ce0d26138b150
import Definitions.Def_SourceProof_df666fc452357fe670b01cc3
import Definitions.Def_SourceProof_ef369f12801e25b88b9d4546
import Definitions.Def_SourceProof_fcea44cccdc2e2f35ffe89f9
import Mathlib.Probability.Distributions.Poisson.Basic

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


theorem _root_.Prove2MeSourceProof.h_6f80af65b6d22255a398a6e4 (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (ProbabilityMeasure.convPow μ n : Measure ℝ) t =
      charFun (μ : Measure ℝ) t ^ n := by
  induction n with
  | zero => simp [_root_.Prove2MeSourceProof.h_cce2f2b17a1ce0d26138b150, ProbabilityMeasure.pointMass]
  | succ n ih =>
      rw [_root_.Prove2MeSourceProof.h_ef369f12801e25b88b9d4546, _root_.Prove2MeSourceProof.h_fcea44cccdc2e2f35ffe89f9, charFun_conv, ih,
        pow_succ]
end CharacteristicFunction

end CompoundPoisson

end ProbabilityTheory


