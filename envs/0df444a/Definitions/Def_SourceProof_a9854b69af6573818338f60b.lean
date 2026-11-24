-- Prove2me | Definitions.Def_SourceProof_a9854b69af6573818338f60b
-- name    : SourceProof_a9854b69af6573818338f60b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:00.879424+00:00
-- url     : https://prove2.me/theorems/821e3394-df50-4b59-93cf-ba60399f851d
-- title:
--   StochLean source theorem: ProbabilityTheory.levyTruncation_of_one_le_abs

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

theorem _root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b {x : ℝ} (hx : 1 ≤ |x|) : levyTruncation x = 0 := by
  simp [ProbabilityTheory.levyTruncation, not_lt.mpr hx]
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


