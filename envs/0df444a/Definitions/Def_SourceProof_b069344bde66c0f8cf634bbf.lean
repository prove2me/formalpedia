-- Prove2me | Definitions.Def_SourceProof_b069344bde66c0f8cf634bbf
-- name    : SourceProof_b069344bde66c0f8cf634bbf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:26.470881+00:00
-- url     : https://prove2.me/theorems/b8b4c397-4b5b-5cda-9ac4-4d42df08a229
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.Represents.exponent_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_SourceProof_2669f41d4ab2eaa6e9935e14
import Definitions.Def_SourceProof_4f4be57c88b3655e4c5f0cba

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

namespace Represents

theorem _root_.Prove2MeSourceProof.h_b069344bde66c0f8cf634bbf {η ξ : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hη : η.Represents μ) (hξ : ξ.Represents μ) : η.exponent = ξ.exponent := by
  apply _root_.Prove2MeSourceProof.h_4f4be57c88b3655e4c5f0cba (_root_.Prove2MeSourceProof.h_2669f41d4ab2eaa6e9935e14 η) (_root_.Prove2MeSourceProof.h_2669f41d4ab2eaa6e9935e14 ξ)
  · simp [ProbabilityTheory.LevyTriplet.exponent, ProbabilityTheory.levyExponentIntegrand]
  · intro t
    rw [← hη t, ← hξ t]
end Represents

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


