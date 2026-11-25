-- Prove2me | Definitions.Def_SourceProof_daf4430892484ad2f4cc58ba
-- name    : SourceProof_daf4430892484ad2f4cc58ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:24:27.208532+00:00
-- url     : https://prove2.me/theorems/33dce93b-f0ed-4ad5-9741-9213d022905b
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.drift_eq_of_exponent_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_SourceProof_01243bc92c93469b6f708225
import Definitions.Def_SourceProof_96e4a2723d12915db081936e

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

theorem _root_.Prove2MeSourceProof.h_daf4430892484ad2f4cc58ba {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) : η.drift = ξ.drift := by
  have hv := _root_.Prove2MeSourceProof.h_96e4a2723d12915db081936e h
  have hj := _root_.Prove2MeSourceProof.h_01243bc92c93469b6f708225 h
  have ht := congrFun h 1
  simp only [ProbabilityTheory.LevyTriplet.exponent] at ht
  rw [hv, hj] at ht
  norm_num at ht
  exact ht
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


