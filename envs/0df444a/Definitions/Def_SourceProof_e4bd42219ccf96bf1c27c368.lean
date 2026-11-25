-- Prove2me | Definitions.Def_SourceProof_e4bd42219ccf96bf1c27c368
-- name    : SourceProof_e4bd42219ccf96bf1c27c368
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:32.595324+00:00
-- url     : https://prove2.me/theorems/5030c019-c743-5238-b9f4-6308346a7960
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.rightLimitProcess_of_caglad

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_05a0222ab69a43769846803a
import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right-limit transformation is continuous in UCP on caglad paths

A slightly larger input horizon controls the right limit at the target horizon.
The transformation need not preserve the original initial value or give a
modification. Its continuity is proved by pathwise deviation comparison.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_e4bd42219ccf96bf1c27c368 {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) (hrZ : ∀ n, HasCagladPaths (Z n) P)
    (hrY : HasCagladPaths Y P) :
    TendstoUCP P (fun n ↦ rightLimitProcess (Z n)) l (rightLimitProcess Y) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu (T + 1) ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hrZ n, hrY] with ω hZ hY hω
  exact hω.trans (_root_.Prove2MeSourceProof.h_05a0222ab69a43769846803a hZ hY T)
end TendstoUCP

end ProbabilityTheory


