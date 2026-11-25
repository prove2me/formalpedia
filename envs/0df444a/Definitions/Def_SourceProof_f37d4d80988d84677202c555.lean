-- Prove2me | Definitions.Def_SourceProof_f37d4d80988d84677202c555
-- name    : SourceProof_f37d4d80988d84677202c555
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:40.750857+00:00
-- url     : https://prove2.me/theorems/1b3df6f4-2278-4715-86cc-c90dd758d783
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.Represents.add

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F015
import Definitions.Def_SourceProof_f19b3c147d1fbbadaf44c6c0
import Definitions.Def_SourceProof_fcea44cccdc2e2f35ffe89f9

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
theorem _root_.Prove2MeSourceProof.h_f37d4d80988d84677202c555 {η ξ : LevyTriplet} {μ ν : ProbabilityMeasure ℝ}
    (hη : η.Represents μ) (hξ : ξ.Represents ν) :
    (η.add ξ).Represents (ProbabilityMeasure.conv μ ν) := by
  intro t
  rw [_root_.Prove2MeSourceProof.h_fcea44cccdc2e2f35ffe89f9, charFun_conv, hη t, hξ t, _root_.Prove2MeSourceProof.h_f19b3c147d1fbbadaf44c6c0,
    Complex.exp_add]
end Represents

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


