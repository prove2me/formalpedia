-- Prove2me | Definitions.Def_SourceProof_a9754c6a2daad201e1fa7291
-- name    : SourceProof_a9754c6a2daad201e1fa7291
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:45.87149+00:00
-- url     : https://prove2.me/theorems/84fec270-5d0a-4202-a0dc-6b4ce25529d2
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exponent_gaussian

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F014

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_a9754c6a2daad201e1fa7291 (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (gaussian m v).exponent t =
      -((((v : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) + ((m * t : ℝ) : ℂ) * Complex.I := by
  simp [ProbabilityTheory.LevyTriplet.gaussian, ProbabilityTheory.LevyTriplet.exponent]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


