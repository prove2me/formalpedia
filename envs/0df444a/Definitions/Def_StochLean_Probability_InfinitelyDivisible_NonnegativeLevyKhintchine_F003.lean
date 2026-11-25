-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F003
-- name    : StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:56:17.940684+00:00
-- url     : https://prove2.me/theorems/f2d2f92a-96e2-59db-a670-6dd6fc457f64
-- title:
--   StochLean: Probability.InfinitelyDivisible.NonnegativeLevyKhintchine F003

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001

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

noncomputable def law (η : NonnegativeLevyPair) : ProbabilityMeasure ℝ :=
  η.toLevyTriplet.law
end NonnegativeLevyPair
end ProbabilityTheory


