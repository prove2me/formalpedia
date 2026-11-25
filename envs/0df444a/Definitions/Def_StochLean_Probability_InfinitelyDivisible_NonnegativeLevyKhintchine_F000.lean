-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F000
-- name    : StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:21:33.895658+00:00
-- url     : https://prove2.me/theorems/8f12aa65-67d9-53e2-9d38-5d57b624ab6b
-- title:
--   StochLean: Probability.InfinitelyDivisible.NonnegativeLevyKhintchine F000

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F000
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F003
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevySemigroup_F004
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F000
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Nonnegative_F002

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

structure NonnegativeLevyPair where
  deterministicPart : NNReal
  jumpMeasure : Measure ℝ
  supportedPositive : ∀ᵐ x ∂jumpMeasure, 0 < x
  integrable_min_one : Integrable (fun x : ℝ ↦ min 1 x) jumpMeasure
namespace NonnegativeLevyPair

end NonnegativeLevyPair
end ProbabilityTheory


