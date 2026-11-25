-- Prove2me | Definitions.Def_SourceProof_cc9d1824ad64b2323f63380a
-- name    : SourceProof_cc9d1824ad64b2323f63380a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:31.128482+00:00
-- url     : https://prove2.me/theorems/10bd444b-3458-4398-bafc-49e16212854f
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_mono

import Definitions.Def_StochLean_Probability_Process_UCP_F000
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784

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

theorem _root_.Prove2MeSourceProof.h_cc9d1824ad64b2323f63380a {S T : ℝ≥0} (hST : S ≤ T) (ω : Ω) :
    compactDeviation X Y S ω ≤ compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 (ht.trans hST) ω
end ProbabilityTheory


