-- Prove2me | Definitions.Def_SourceProof_838469f6b44e20e37e1354d5
-- name    : SourceProof_838469f6b44e20e37e1354d5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:38.586868+00:00
-- url     : https://prove2.me/theorems/df202b3a-f9f4-46cb-ab32-3fabacbee62a
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.secondDifferenceMeasure_eq_of_exponent_eq

import Definitions.Def_SourceProof_aad21b11daf6930ca2e3b912

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

theorem _root_.Prove2MeSourceProof.h_838469f6b44e20e37e1354d5 {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) (s : ℝ) :
    secondDifferenceMeasure η s = secondDifferenceMeasure ξ s := by
  apply Measure.ext_of_charFun
  funext t
  rw [_root_.Prove2MeSourceProof.h_aad21b11daf6930ca2e3b912, _root_.Prove2MeSourceProof.h_aad21b11daf6930ca2e3b912, h]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


