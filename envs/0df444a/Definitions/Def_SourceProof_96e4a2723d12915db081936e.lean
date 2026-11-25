-- Prove2me | Definitions.Def_SourceProof_96e4a2723d12915db081936e
-- name    : SourceProof_96e4a2723d12915db081936e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:56:28.55361+00:00
-- url     : https://prove2.me/theorems/9f420696-63a5-5832-9df5-bf3f0c3ab51a
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.gaussianVariance_eq_of_exponent_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F009
import Definitions.Def_SourceProof_838469f6b44e20e37e1354d5
import Definitions.Def_SourceProof_90c2d3be15ce60f9e46f9754

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

theorem _root_.Prove2MeSourceProof.h_96e4a2723d12915db081936e {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) : η.gaussianVariance = ξ.gaussianVariance := by
  have hm := congrArg (fun m : Measure ℝ => m {0})
    (_root_.Prove2MeSourceProof.h_838469f6b44e20e37e1354d5 h 1)
  rw [_root_.Prove2MeSourceProof.h_90c2d3be15ce60f9e46f9754,
    _root_.Prove2MeSourceProof.h_90c2d3be15ce60f9e46f9754] at hm
  have hm' : ENNReal.ofReal (η.gaussianVariance : ℝ) =
      ENNReal.ofReal (ξ.gaussianVariance : ℝ) := by
    simpa only [one_pow, mul_one] using hm
  apply ENNReal.coe_inj.mp
  calc
    (η.gaussianVariance : ℝ≥0∞) = ENNReal.ofReal (η.gaussianVariance : ℝ) :=
      ENNReal.coe_nnreal_eq _
    _ = ENNReal.ofReal (ξ.gaussianVariance : ℝ) := hm'
    _ = (ξ.gaussianVariance : ℝ≥0∞) := (ENNReal.coe_nnreal_eq _).symm
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


