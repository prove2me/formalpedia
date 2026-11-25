-- Prove2me | Definitions.Def_SourceProof_2805187910815ebae4f90f84
-- name    : SourceProof_2805187910815ebae4f90f84
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:07.006416+00:00
-- url     : https://prove2.me/theorems/704b06af-9fb8-4b65-adfb-5c2cdc605c5e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.congr_of_adapted

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_f936c2ca6bfeffcec4d6a422
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_2805187910815ebae4f90f84 (hX : IsSemimartingale X F P)
    (hXY : Indistinguishable X Y P) (ha : Adapted F Y) : IsSemimartingale Y F P := by
  intro T
  apply (_root_.Prove2MeSourceProof.h_f936c2ca6bfeffcec4d6a422 (hX T)) ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 hXY) _) ?_
  intro t
  change Measurable[F t] (fun ω ↦ Y (min t T) ω)
  exact (ha _).mono (F.mono (min_le_left t T)) le_rfl
end IsSemimartingale

variable [IsFiniteMeasure P]

end ProbabilityTheory


