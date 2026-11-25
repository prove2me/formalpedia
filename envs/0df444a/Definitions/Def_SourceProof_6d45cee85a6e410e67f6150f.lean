-- Prove2me | Definitions.Def_SourceProof_6d45cee85a6e410e67f6150f
-- name    : SourceProof_6d45cee85a6e410e67f6150f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:01:57.548435+00:00
-- url     : https://prove2.me/theorems/e18f9cac-f316-57f3-9d78-9c62475b98a6
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.represents_law

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F003
import Definitions.Def_SourceProof_a34cbae749bdf9570a13c7e0

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

theorem _root_.Prove2MeSourceProof.h_6d45cee85a6e410e67f6150f (η : NonnegativeLevyPair) : η.toLevyTriplet.Represents η.law :=
  (_root_.Prove2MeSourceProof.h_a34cbae749bdf9570a13c7e0 η.toLevyTriplet)
end NonnegativeLevyPair
end ProbabilityTheory


