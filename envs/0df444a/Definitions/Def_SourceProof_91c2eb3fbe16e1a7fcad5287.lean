-- Prove2me | Definitions.Def_SourceProof_91c2eb3fbe16e1a7fcad5287
-- name    : SourceProof_91c2eb3fbe16e1a7fcad5287
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:27.640771+00:00
-- url     : https://prove2.me/theorems/84f6f067-1c10-49bf-b3b9-e9875eb3d8d6
-- title:
--   StochLean source theorem: MeasureTheory.stronglyAdapted_pathwiseQuadraticVariation

import Definitions.Def_SourceProof_83bfe2ab7b5ac3b55345c1e4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Quadratic variation and predictable bracket in discrete time

The pathwise quadratic variation `[M]` and the predictable bracket `⟨M⟩` are deliberately
different definitions.  The latter is the Doob predictable part (compensator) of the former.
-/

@[expose] public section

open scoped BigOperators ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_91c2eb3fbe16e1a7fcad5287 {M : ℕ → Ω → ℝ}
    {𝓕 : Filtration ℕ mΩ} (hM : StronglyAdapted 𝓕 M) :
    StronglyAdapted 𝓕 (pathwiseQuadraticVariation M) := by
  intro n
  rw [_root_.Prove2MeSourceProof.h_83bfe2ab7b5ac3b55345c1e4]
  refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  exact (((hM (k + 1)).mono (𝓕.mono (Nat.succ_le_of_lt hk))).sub
    ((hM k).mono (𝓕.mono hk.le))).pow 2
end MeasureTheory


