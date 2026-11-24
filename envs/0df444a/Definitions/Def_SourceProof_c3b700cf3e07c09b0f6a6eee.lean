-- Prove2me | Definitions.Def_SourceProof_c3b700cf3e07c09b0f6a6eee
-- name    : SourceProof_c3b700cf3e07c09b0f6a6eee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:46.250223+00:00
-- url     : https://prove2.me/theorems/075809bb-f655-4bbb-a397-eab10b1b365b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.integrable_levyExponentIntegrand

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
import Definitions.Def_SourceProof_0c6d3685872c502bae901cb3
import Definitions.Def_SourceProof_153d33725319d021bbb878c0
import Definitions.Def_SourceProof_2be0585f00e4ee67c5a1001f
import Definitions.Def_SourceProof_f9b33963924eb7ac5401881f

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

namespace IsLevyMeasure

theorem _root_.Prove2MeSourceProof.h_c3b700cf3e07c09b0f6a6eee {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) (t : ℝ) : Integrable (levyExponentIntegrand t) ν := by
  have hbase : Integrable (fun x => (ProbabilityTheory.levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3.aemeasurable
      (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hν).ne
  have hdom : Integrable (fun x => ProbabilityTheory.levyExponentBound t * (ProbabilityTheory.levyIntegrand x).toReal) ν :=
    hbase.const_mul _
  apply hdom.mono'
  · exact (_root_.Prove2MeSourceProof.h_f9b33963924eb7ac5401881f t).aestronglyMeasurable
  · exact ae_of_all _ fun x => _root_.Prove2MeSourceProof.h_2be0585f00e4ee67c5a1001f t x
end IsLevyMeasure

namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


