-- Prove2me | Definitions.Def_SourceProof_5c93f08a7daf0a879e3a6ed9
-- name    : SourceProof_5c93f08a7daf0a879e3a6ed9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:05:02.953745+00:00
-- url     : https://prove2.me/theorems/15a86e53-923c-444b-9fe5-0c591c23ad0b
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.weightedJumpMeasure_eq_of_exponent_eq

import Definitions.Def_SourceProof_838469f6b44e20e37e1354d5
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

theorem _root_.Prove2MeSourceProof.h_5c93f08a7daf0a879e3a6ed9 {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) (s : ℝ) :
    weightedJumpMeasure η s = weightedJumpMeasure ξ s := by
  have hv := _root_.Prove2MeSourceProof.h_96e4a2723d12915db081936e h
  have hm := _root_.Prove2MeSourceProof.h_838469f6b44e20e37e1354d5 h s
  ext A hA
  have hmA := congrArg (fun m : Measure ℝ => m A) hm
  simp only [ProbabilityTheory.LevyTriplet.secondDifferenceMeasure, Measure.add_apply, Measure.smul_apply, hA] at hmA
  rw [hv] at hmA
  apply (ENNReal.add_right_inj ?_).mp hmA
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


