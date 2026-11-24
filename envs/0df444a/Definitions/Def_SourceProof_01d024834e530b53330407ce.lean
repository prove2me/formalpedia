-- Prove2me | Definitions.Def_SourceProof_01d024834e530b53330407ce
-- name    : SourceProof_01d024834e530b53330407ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:57.420318+00:00
-- url     : https://prove2.me/theorems/fd952a53-8494-4ead-b0c7-c73ef3784065
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.integrable_levyTruncation

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F000
import Definitions.Def_SourceProof_7e961aa121c5246639f2cd81
import Definitions.Def_SourceProof_9d54591e608c50f52d7e3085
import Definitions.Def_SourceProof_a9854b69af6573818338f60b

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

theorem _root_.Prove2MeSourceProof.h_01d024834e530b53330407ce (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable levyTruncation ν := by
  apply (integrable_const (1 : ℝ)).mono _root_.Prove2MeSourceProof.h_9d54591e608c50f52d7e3085.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    by_cases hx : |x| < 1
    · rw [_root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 hx, Real.norm_eq_abs]
      simpa using hx.le
    · rw [_root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b (le_of_not_gt hx)]
      simp
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


