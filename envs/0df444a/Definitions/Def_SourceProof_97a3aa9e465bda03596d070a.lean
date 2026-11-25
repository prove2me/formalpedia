-- Prove2me | Definitions.Def_SourceProof_97a3aa9e465bda03596d070a
-- name    : SourceProof_97a3aa9e465bda03596d070a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:06:07.992114+00:00
-- url     : https://prove2.me/theorems/dadffb58-2a5c-5626-9a18-945fdfb35593
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.isNonnegativeLaw_law

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F003
import Definitions.Def_SourceProof_43a2df67ab5b5e7e533fcfda
import Definitions.Def_SourceProof_5ed50d69db2922e3c5ab6b6d
import Definitions.Def_SourceProof_6d45cee85a6e410e67f6150f
import Definitions.Def_SourceProof_d72fb9e89be890a633fb10d1

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

theorem _root_.Prove2MeSourceProof.h_97a3aa9e465bda03596d070a (η : NonnegativeLevyPair) : η.law.IsNonnegativeLaw := by
  apply _root_.Prove2MeSourceProof.h_43a2df67ab5b5e7e533fcfda
    (μn := fun n ↦ η.toLevyTriplet.finiteRestrictionLaw n)
  · apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    rw [(_root_.Prove2MeSourceProof.h_6d45cee85a6e410e67f6150f η) t]
    exact (_root_.Prove2MeSourceProof.h_d72fb9e89be890a633fb10d1 η.toLevyTriplet) t
  · exact (_root_.Prove2MeSourceProof.h_5ed50d69db2922e3c5ab6b6d η)
end NonnegativeLevyPair
end ProbabilityTheory


