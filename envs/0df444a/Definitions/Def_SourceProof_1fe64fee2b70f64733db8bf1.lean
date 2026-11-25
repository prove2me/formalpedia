-- Prove2me | Definitions.Def_SourceProof_1fe64fee2b70f64733db8bf1
-- name    : SourceProof_1fe64fee2b70f64733db8bf1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:22:26.229827+00:00
-- url     : https://prove2.me/theorems/f9591a58-3fc4-55ff-b4ef-346f84359de0
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.gaussianLaw_zero_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F000
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F003
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F004
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F000
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F002
import Definitions.Def_SourceProof_3c9195c64e429293f81ae822
import Definitions.Def_SourceProof_538c4e6a97628af2c2729c15

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Nonnegative Levy--Khintchine parameters

The canonical parameters of a subordinator consist of a nonnegative deterministic part and a
positive jump measure integrating `min 1 x`.  This file embeds those parameters into StochLean's
fixed-truncation real Levy triplets and proves the constructive half of the nonnegative
Levy--Khintchine theorem, including nonnegative support of the resulting law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

namespace NonnegativeLevyPair

theorem _root_.Prove2MeSourceProof.h_1fe64fee2b70f64733db8bf1 : LevyTriplet.gaussianLaw 0 0 =
    ProbabilityMeasure.pointMass 0 := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [_root_.Prove2MeSourceProof.h_3c9195c64e429293f81ae822, _root_.Prove2MeSourceProof.h_538c4e6a97628af2c2729c15,
    gaussianReal_zero_var]
end NonnegativeLevyPair
end ProbabilityTheory


