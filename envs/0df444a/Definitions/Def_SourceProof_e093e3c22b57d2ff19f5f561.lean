-- Prove2me | Definitions.Def_SourceProof_e093e3c22b57d2ff19f5f561
-- name    : SourceProof_e093e3c22b57d2ff19f5f561
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:08.894066+00:00
-- url     : https://prove2.me/theorems/6eabcd36-09a7-4494-ab73-0f814c12e6a6
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_affineDriftIntegrand

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002
import Definitions.Def_SourceProof_9d54591e608c50f52d7e3085

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_e093e3c22b57d2ff19f5f561 (a : ℝ) : Measurable (affineDriftIntegrand a) := by
  unfold ProbabilityTheory.affineDriftIntegrand
  exact (_root_.Prove2MeSourceProof.h_9d54591e608c50f52d7e3085.comp (by fun_prop)).sub
    (measurable_const.mul _root_.Prove2MeSourceProof.h_9d54591e608c50f52d7e3085)
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


