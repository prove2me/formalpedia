-- Prove2me | Definitions.Def_SourceProof_d131a251c93ace9fd2ee70bb
-- name    : SourceProof_d131a251c93ace9fd2ee70bb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:41.886168+00:00
-- url     : https://prove2.me/theorems/906407fd-3fb3-4267-a00e-4ef308f290ba
-- title:
--   StochLean source theorem: ProbabilityTheory.HasRightContinuousPaths.congr

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure right-continuous paths
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

section PathDefinitions

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

namespace HasRightContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_d131a251c93ace9fd2ee70bb (hXY : Indistinguishable X Y P) (hX : HasRightContinuousPaths X P) :
    HasRightContinuousPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcont
  simpa only [ProbabilityTheory.IsRightContinuousPath, hω] using hcont
end HasRightContinuousPaths

end PathDefinitions

namespace IsModification

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder T] [TopologicalSpace T] [OrderTopology T] [DenselyOrdered T] [NoMaxOrder T]
  [FirstCountableTopology T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [TopologicalSpace E] [T2Space E] {X Y : T → Ω → E} {P : Measure Ω}

end IsModification

end ProbabilityTheory


