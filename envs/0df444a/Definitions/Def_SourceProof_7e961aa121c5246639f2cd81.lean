-- Prove2me | Definitions.Def_SourceProof_7e961aa121c5246639f2cd81
-- name    : SourceProof_7e961aa121c5246639f2cd81
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:32.908682+00:00
-- url     : https://prove2.me/theorems/9f93cdcf-8b12-40ec-99a4-54010a2cdc4b
-- title:
--   StochLean source theorem: ProbabilityTheory.levyTruncation_of_abs_lt_one

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

theorem _root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 {x : ℝ} (hx : |x| < 1) : levyTruncation x = x := by
  simp [ProbabilityTheory.levyTruncation, hx]
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


