-- Prove2me | Definitions.Def_SourceProof_e7578178dcf5fa404cb3a96e
-- name    : SourceProof_e7578178dcf5fa404cb3a96e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:43.365534+00:00
-- url     : https://prove2.me/theorems/97715be0-406d-48ae-9e0b-2c1aeeb10470
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure_represents

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_SourceProof_14aaba468c338b75c22998f2
import Definitions.Def_SourceProof_3120093e93d873b00f0ead3c
import Definitions.Def_SourceProof_4604c8146790c1b891bcab47
import Definitions.Def_SourceProof_696442d2e4da6d0186632421
import Definitions.Def_SourceProof_757c0e14bc5574fd4d5f86ba
import Definitions.Def_SourceProof_75969e14c886e2ba9854184e
import Definitions.Def_SourceProof_a7f42d43f828e78b8e988fb6

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


theorem _root_.Prove2MeSourceProof.h_e7578178dcf5fa404cb3a96e (ν : FiniteMeasure ℝ)
    (hzero : (ν : Measure ℝ) {0} = 0) :
    (tripletOfFiniteMeasure ν hzero).Represents (ofFiniteMeasure ν) := by
  by_cases hν : ν = 0
  · subst ν
    rw [_root_.Prove2MeSourceProof.h_a7f42d43f828e78b8e988fb6, _root_.Prove2MeSourceProof.h_696442d2e4da6d0186632421]
    exact _root_.Prove2MeSourceProof.h_14aaba468c338b75c22998f2 0
  · rw [_root_.Prove2MeSourceProof.h_4604c8146790c1b891bcab47 hν hzero,
      _root_.Prove2MeSourceProof.h_3120093e93d873b00f0ead3c hν]
    exact _root_.Prove2MeSourceProof.h_757c0e14bc5574fd4d5f86ba ν.mass ν.normalize
      (_root_.Prove2MeSourceProof.h_75969e14c886e2ba9854184e hν hzero)
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


