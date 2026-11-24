-- Prove2me | Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784
-- name    : SourceProof_845eb3d5bff7aa74f6afa784
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:16.832572+00:00
-- url     : https://prove2.me/theorems/e3208067-270e-4031-91f7-1048dcdd837d
-- title:
--   StochLean source theorem: ProbabilityTheory.enorm_sub_le_compactDeviation

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

theorem _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    ENNReal.ofReal ‖X t ω - Y t ω‖ ≤ compactDeviation X Y T ω :=
  le_iSup_of_le t (le_iSup_of_le ht le_rfl)
end ProbabilityTheory


