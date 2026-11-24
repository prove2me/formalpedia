-- Prove2me | Definitions.Def_SourceProof_538276c71aeae59150be9f02
-- name    : SourceProof_538276c71aeae59150be9f02
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:18.726579+00:00
-- url     : https://prove2.me/theorems/50c2df74-ed05-4e5a-b16d-a7be6b2f2348
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.indicator

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_1e22444e89591e28e8035421

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Fixed event masks preserve UCP convergence

Outer-measure comparison needs no measurability of the event or of the paths.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_538276c71aeae59150be9f02 {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) (s : Set Ω) :
    TendstoUCP P (fun n t ↦ s.indicator (Z n t)) l (fun t ↦ s.indicator (Y t)) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  exact measure_mono fun ω hω ↦ hω.trans (_root_.Prove2MeSourceProof.h_1e22444e89591e28e8035421 s T ω)
end TendstoUCP

end ProbabilityTheory


