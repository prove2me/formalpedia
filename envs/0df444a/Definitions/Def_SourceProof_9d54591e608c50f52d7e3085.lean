-- Prove2me | Definitions.Def_SourceProof_9d54591e608c50f52d7e3085
-- name    : SourceProof_9d54591e608c50f52d7e3085
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:09.539747+00:00
-- url     : https://prove2.me/theorems/25c5888b-5b7c-4a55-b73a-825b334d73c2
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_levyTruncation

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F000

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

theorem _root_.Prove2MeSourceProof.h_9d54591e608c50f52d7e3085 : Measurable levyTruncation := by
  unfold ProbabilityTheory.levyTruncation
  exact Measurable.ite (by measurability) measurable_id measurable_const
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


