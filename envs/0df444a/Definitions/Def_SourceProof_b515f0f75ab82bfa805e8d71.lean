-- Prove2me | Definitions.Def_SourceProof_b515f0f75ab82bfa805e8d71
-- name    : SourceProof_b515f0f75ab82bfa805e8d71
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:51.094082+00:00
-- url     : https://prove2.me/theorems/5ec2e386-6a87-4e35-a46d-b2157aff8a81
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.levyExponentIntegrand_mul

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002

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

theorem _root_.Prove2MeSourceProof.h_b515f0f75ab82bfa805e8d71 (a t x : ℝ) :
    levyExponentIntegrand t (a * x) = levyExponentIntegrand (a * t) x -
      (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I) := by
  unfold ProbabilityTheory.levyExponentIntegrand ProbabilityTheory.affineDriftIntegrand
  have hexpArg : (((t * (a * x) : ℝ) : ℂ) * Complex.I) =
      ((((a * t) * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexpArg]
  push_cast
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


