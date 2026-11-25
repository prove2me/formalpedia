-- Prove2me | Definitions.Def_SourceProof_ad6533256e326b87026fa3d4
-- name    : SourceProof_ad6533256e326b87026fa3d4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:53.150798+00:00
-- url     : https://prove2.me/theorems/62234d9a-a60a-4010-a287-e7f1bab2dc4c
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.isTendingToIdentity_deterministic

import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Definitions.Def_SourceProof_50683a9a3eede679ee61a879
import Definitions.Def_SourceProof_97ee3cedc74c1a56415c4c49

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite stopping-time partitions and deterministic embedding -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace StoppingTimePartition

variable {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_ad6533256e326b87026fa3d4 {P : Measure Ω} {T : ℕ → ℝ≥0}
    (π : (n : ℕ) → StochLean.TimePartition (T n)) (hT : Tendsto T atTop atTop)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) :
    IsTendingToIdentity (fun n ↦ deterministic F (π n)) P := by
  apply ae_of_all
  intro ω
  simpa only [_root_.Prove2MeSourceProof.h_97ee3cedc74c1a56415c4c49, _root_.Prove2MeSourceProof.h_50683a9a3eede679ee61a879] using And.intro hT hmesh
end StoppingTimePartition
end ProbabilityTheory


