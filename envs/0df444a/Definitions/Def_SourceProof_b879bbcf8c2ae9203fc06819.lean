-- Prove2me | Definitions.Def_SourceProof_b879bbcf8c2ae9203fc06819
-- name    : SourceProof_b879bbcf8c2ae9203fc06819
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:22.433229+00:00
-- url     : https://prove2.me/theorems/0c3afd6c-ccf0-4057-891b-3380de7fa508
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.monotone_levyIdentificationSet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F010

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

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_b879bbcf8c2ae9203fc06819 : Monotone levyIdentificationSet := by
  intro n m hnm x hx
  refine ⟨hx.1, lt_of_lt_of_le hx.2 ?_⟩
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  gcongr
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


