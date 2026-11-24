-- Prove2me | Definitions.Def_SourceProof_442b482eafb28142fd8f3cea
-- name    : SourceProof_442b482eafb28142fd8f3cea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:29.221538+00:00
-- url     : https://prove2.me/theorems/cb512cff-e94e-401b-8d22-583745aa8d5d
-- title:
--   StochLean source theorem: MeasureTheory.pathwiseQuadraticVariation_zero

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F000

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_442b482eafb28142fd8f3cea (M : ℕ → Ω → ℝ) :
    pathwiseQuadraticVariation M 0 = 0 := by
  ext ω
  simp [MeasureTheory.pathwiseQuadraticVariation]
end MeasureTheory


