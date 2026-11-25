-- Prove2me | Definitions.Def_SourceProof_c59b662aa91c3d86c96a92b3
-- name    : SourceProof_c59b662aa91c3d86c96a92b3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:33.297188+00:00
-- url     : https://prove2.me/theorems/9f4e97ae-1770-5f25-ba78-479d554cbac3
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.integrable_affineDriftIntegrand

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002
import Definitions.Def_SourceProof_0c6d3685872c502bae901cb3
import Definitions.Def_SourceProof_153d33725319d021bbb878c0
import Definitions.Def_SourceProof_7f578536210b5439b655b536
import Definitions.Def_SourceProof_e093e3c22b57d2ff19f5f561

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
theorem _root_.Prove2MeSourceProof.h_c59b662aa91c3d86c96a92b3 {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) {a : ℝ} (ha : 0 < a) : Integrable (affineDriftIntegrand a) ν := by
  have hbase : Integrable (fun x => (ProbabilityTheory.levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3.aemeasurable
      (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hν).ne
  apply (hbase.const_mul (max 1 (a ^ 2))).mono'
  · exact (_root_.Prove2MeSourceProof.h_e093e3c22b57d2ff19f5f561 a).aestronglyMeasurable
  · exact ae_of_all _ (_root_.Prove2MeSourceProof.h_7f578536210b5439b655b536 ha)
end IsLevyMeasure

namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


