-- Prove2me | Definitions.Def_SourceProof_3c2a5c808ed239558b95c152
-- name    : SourceProof_3c2a5c808ed239558b95c152
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:02.784319+00:00
-- url     : https://prove2.me/theorems/38fa769b-ec1a-5e2f-bc79-febda4749223
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exponent_nnrealSMul

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F016

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_3c2a5c808ed239558b95c152 (r : ℝ≥0) (η : LevyTriplet) (t : ℝ) :
    (η.nnrealSMul r).exponent t = (r : ℂ) * η.exponent t := by
  simp only [ProbabilityTheory.LevyTriplet.exponent, ProbabilityTheory.LevyTriplet.nnrealSMul, NNReal.coe_mul,
    MeasureTheory.integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [Complex.real_smul]
  push_cast
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


