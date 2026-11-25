-- Prove2me | Definitions.Def_SourceProof_ec254e0d7aece1e039229627
-- name    : SourceProof_ec254e0d7aece1e039229627
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:09:17.913439+00:00
-- url     : https://prove2.me/theorems/bf4bba96-aca6-439a-9d3c-2d857e6de45d
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exists_represents

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F023
import Definitions.Def_SourceProof_14ce596e78ac87d01b7cd87a
import Definitions.Def_SourceProof_8cfc7b1c9049cca06e74c95b
import Definitions.Def_SourceProof_d72fb9e89be890a633fb10d1

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


theorem _root_.Prove2MeSourceProof.h_ec254e0d7aece1e039229627 (η : LevyTriplet) :
    ∃ μ : ProbabilityMeasure ℝ, η.Represents μ := by
  obtain ⟨μ, hchar, -⟩ := _root_.Prove2MeSourceProof.h_14ce596e78ac87d01b7cd87a
    (_root_.Prove2MeSourceProof.h_8cfc7b1c9049cca06e74c95b η).continuousAt (_root_.Prove2MeSourceProof.h_d72fb9e89be890a633fb10d1 η)
  exact ⟨μ, hchar⟩
end LevyTriplet

end ProbabilityTheory


