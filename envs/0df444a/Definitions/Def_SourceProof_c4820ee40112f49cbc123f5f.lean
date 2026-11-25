-- Prove2me | Definitions.Def_SourceProof_c4820ee40112f49cbc123f5f
-- name    : SourceProof_c4820ee40112f49cbc123f5f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:35.920459+00:00
-- url     : https://prove2.me/theorems/862e22e1-b9bb-5ecb-abd7-2fafca7232d6
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_self

import Definitions.Def_StochLean_Probability_Process_UCP_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

@[simp] theorem _root_.Prove2MeSourceProof.h_c4820ee40112f49cbc123f5f (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    compactDeviation X X T ω = 0 := by simp [ProbabilityTheory.compactDeviation]
end ProbabilityTheory


