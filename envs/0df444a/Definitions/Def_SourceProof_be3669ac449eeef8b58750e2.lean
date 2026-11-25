-- Prove2me | Definitions.Def_SourceProof_be3669ac449eeef8b58750e2
-- name    : SourceProof_be3669ac449eeef8b58750e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:33.714805+00:00
-- url     : https://prove2.me/theorems/2cfccf69-4b79-4949-bd01-67a9ce284865
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.hasLaw

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_d131a251c93ace9fd2ee70bb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Poisson processes

The predicate below packages the standard counting-process requirements without introducing a
new process type. Path properties use one common almost-sure event, and increment laws are only
asserted for ordered times, where natural subtraction represents an actual count increment.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_be3669ac449eeef8b58750e2 (hX : IsPoissonProcess X rate P) (t : NNReal) :
    HasLaw (X t) (poissonMeasure (rate * t)) P := by
  have hinc := hX.incrementLaw 0 t bot_le
  have heq : X t =ᵐ[P] fun ω ↦ X t ω - X 0 ω := by
    filter_upwards [hX.initial] with ω hω
    simp only [hω, Nat.sub_zero]
  simpa only [tsub_zero] using hinc.congr heq
end IsPoissonProcess

end ProbabilityTheory


