-- Prove2me | Definitions.Def_SourceProof_14aaba468c338b75c22998f2
-- name    : SourceProof_14aaba468c338b75c22998f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:13.350886+00:00
-- url     : https://prove2.me/theorems/3b9f11b9-1e4b-4b5e-a28a-35ff4eda5b17
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.represents_pointMass

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_SourceProof_538c4e6a97628af2c2729c15
import Definitions.Def_SourceProof_b9df4492b15ca36c63738ab2

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

theorem _root_.Prove2MeSourceProof.h_14aaba468c338b75c22998f2 (x : ℝ) :
    (pointMass x).Represents (ProbabilityMeasure.pointMass x) := by
  intro t
  rw [_root_.Prove2MeSourceProof.h_538c4e6a97628af2c2729c15, charFun_dirac, _root_.Prove2MeSourceProof.h_b9df4492b15ca36c63738ab2]
  congr 1
  rw [Real.inner_apply]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


