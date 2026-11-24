-- Prove2me | Definitions.Def_SourceProof_f9b33963924eb7ac5401881f
-- name    : SourceProof_f9b33963924eb7ac5401881f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:42.389985+00:00
-- url     : https://prove2.me/theorems/13e20a19-c0d3-4992-81ef-91f27a3e40a0
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_levyExponentIntegrand

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
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

theorem _root_.Prove2MeSourceProof.h_f9b33963924eb7ac5401881f (t : ℝ) : Measurable (levyExponentIntegrand t) := by
  unfold ProbabilityTheory.levyExponentIntegrand
  have htrunc : Measurable ProbabilityTheory.levyTruncation := _root_.Prove2MeSourceProof.h_9d54591e608c50f52d7e3085
  fun_prop
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


