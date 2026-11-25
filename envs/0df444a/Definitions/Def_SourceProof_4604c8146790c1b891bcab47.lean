-- Prove2me | Definitions.Def_SourceProof_4604c8146790c1b891bcab47
-- name    : SourceProof_4604c8146790c1b891bcab47
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:54.413158+00:00
-- url     : https://prove2.me/theorems/31767a67-e248-4284-8c80-d3a3eab0967c
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure_eq_triplet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F019
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F020
import Definitions.Def_SourceProof_75969e14c886e2ba9854184e

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

theorem _root_.Prove2MeSourceProof.h_4604c8146790c1b891bcab47 {ν : FiniteMeasure ℝ} (hν : ν ≠ 0)
    (hzero : (ν : Measure ℝ) {0} = 0) :
    tripletOfFiniteMeasure ν hzero =
      triplet ν.mass ν.normalize (_root_.Prove2MeSourceProof.h_75969e14c886e2ba9854184e hν hzero) := by
  have hmeasure : (ν.mass : ℝ≥0) • (ν.normalize : Measure ℝ) = (ν : Measure ℝ) := by
    have hfinite := congrArg (fun m : FiniteMeasure ℝ ↦ (m : Measure ℝ))
      ν.self_eq_mass_smul_normalize.symm
    simpa using hfinite
  rw [LevyTriplet.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · simp only [ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure, ProbabilityTheory.CompoundPoisson.triplet]
    rw [hmeasure]
  · simpa only [ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure, ProbabilityTheory.CompoundPoisson.triplet] using hmeasure.symm
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


