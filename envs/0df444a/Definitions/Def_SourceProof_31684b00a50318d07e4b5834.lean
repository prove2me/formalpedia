-- Prove2me | Definitions.Def_SourceProof_31684b00a50318d07e4b5834
-- name    : SourceProof_31684b00a50318d07e4b5834
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:59.072849+00:00
-- url     : https://prove2.me/theorems/c293c588-c9e5-4851-b300-94dd19330f46
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.tendsto_exponent_finiteRestriction

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F022
import Definitions.Def_SourceProof_356488f94b3a07227fb18a3b
import Definitions.Def_SourceProof_adc43a2e14e55e286ae46d92
import Definitions.Def_SourceProof_b3add94a40be633b5dd4cb55
import Definitions.Def_SourceProof_f62a285e39f3cce92855751f

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

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet


theorem _root_.Prove2MeSourceProof.h_31684b00a50318d07e4b5834 (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n ↦ (η.finiteRestriction n).exponent t) Filter.atTop
      (nhds (η.exponent t)) := by
  have hint := tendsto_setIntegral_of_monotone
    (fun n ↦ _root_.Prove2MeSourceProof.h_adc43a2e14e55e286ae46d92 n)
    _root_.Prove2MeSourceProof.h_356488f94b3a07227fb18a3b
    (((_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) t).integrableOn)
  rw [(_root_.Prove2MeSourceProof.h_b3add94a40be633b5dd4cb55 η)] at hint
  let A : ℂ := -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    ((η.drift * t : ℝ) : ℂ) * Complex.I
  have hadd : Tendsto
      (fun n ↦ A + ∫ x in ProbabilityTheory.IsLevyMeasure.spanningLevel n,
        ProbabilityTheory.levyExponentIntegrand t x ∂η.jumpMeasure) Filter.atTop
      (nhds (A + ∫ x, ProbabilityTheory.levyExponentIntegrand t x ∂η.jumpMeasure)) :=
    tendsto_const_nhds.add hint
  simpa only [ProbabilityTheory.LevyTriplet.finiteRestriction, ProbabilityTheory.LevyTriplet.exponent, A] using hadd
end LevyTriplet

end ProbabilityTheory


