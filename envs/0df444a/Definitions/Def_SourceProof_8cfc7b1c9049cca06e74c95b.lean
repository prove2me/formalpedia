-- Prove2me | Definitions.Def_SourceProof_8cfc7b1c9049cca06e74c95b
-- name    : SourceProof_8cfc7b1c9049cca06e74c95b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:33:12.535669+00:00
-- url     : https://prove2.me/theorems/857ff368-aca5-4077-8401-9c7fa547e808
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.continuous_exp_exponent

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_SourceProof_2669f41d4ab2eaa6e9935e14

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

theorem _root_.Prove2MeSourceProof.h_8cfc7b1c9049cca06e74c95b (η : LevyTriplet) :
    Continuous (fun t ↦ Complex.exp (η.exponent t)) := by
  exact Complex.continuous_exp.comp (_root_.Prove2MeSourceProof.h_2669f41d4ab2eaa6e9935e14 η)
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


