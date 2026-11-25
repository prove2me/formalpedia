-- Prove2me | Definitions.Def_SourceProof_c76a94657b4085a094543e61
-- name    : SourceProof_c76a94657b4085a094543e61
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:14:24.853442+00:00
-- url     : https://prove2.me/theorems/4b8f79a8-f3ca-4973-976b-f86637f04e0c
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.jumpMeasure_restrict_identificationSet_eq_of_exponent_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F010
import Definitions.Def_SourceProof_1c883159017bdf91b31257ab
import Definitions.Def_SourceProof_1d577702c68f7f6df1204f28
import Definitions.Def_SourceProof_5c93f08a7daf0a879e3a6ed9
import Definitions.Def_SourceProof_86ff457032bada5981439e9c
import Definitions.Def_SourceProof_bc68d4f2e15aa8471858bf4f
import Definitions.Def_SourceProof_be95c401a5efeb9bf84e74e9

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

theorem _root_.Prove2MeSourceProof.h_c76a94657b4085a094543e61
    {η ξ : LevyTriplet} (h : η.exponent = ξ.exponent) (n : ℕ) :
    η.jumpMeasure.restrict (levyIdentificationSet n) =
      ξ.jumpMeasure.restrict (levyIdentificationSet n) := by
  apply _root_.Prove2MeSourceProof.h_bc68d4f2e15aa8471858bf4f
    (show Measurable (fun x =>
      (ProbabilityTheory.LevyTriplet.secondDifferenceWeight ((n + 1 : ℝ)⁻¹) x : ℝ≥0∞)) by
        exact (_root_.Prove2MeSourceProof.h_1c883159017bdf91b31257ab _).coe_nnreal_ennreal)
    (_root_.Prove2MeSourceProof.h_1d577702c68f7f6df1204f28 n)
  · intro x hx
    exact_mod_cast _root_.Prove2MeSourceProof.h_be95c401a5efeb9bf84e74e9 n hx
  · intro x
    exact ENNReal.coe_ne_top
  · exact _root_.Prove2MeSourceProof.h_5c93f08a7daf0a879e3a6ed9 h _
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


