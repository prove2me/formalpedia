-- Prove2me | Definitions.Def_SourceProof_3b6770fe33c80a2ec52a585f
-- name    : SourceProof_3b6770fe33c80a2ec52a585f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:08:46.728615+00:00
-- url     : https://prove2.me/theorems/a0d1143b-5989-4869-8383-3a05cf63f237
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedProcess_of_usual

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_272f7aebecefebc962a5704d
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Definitions.Def_SourceProof_dd5d93162907f5e6520ec487

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Optional sampling under the usual conditions

The original process need only have right-continuous paths on one full-measure
event. We use a progressive, everywhere-regular indistinguishable version, then
transport stopped values. Completeness places the exceptional null sets in
each stopping-time sigma-algebra. No joint measurability of arbitrary values
assigned on the exceptional trajectories is asserted.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace Martingale

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_3b6770fe33c80a2ec52a585f (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess X τ) F P := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX.stronglyAdapted) hF hr
  exact ((_root_.Prove2MeSourceProof.h_272f7aebecefebc962a5704d (hX.congr hprog.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq)))
    hreg hτ).congr ((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f hX.stronglyAdapted) hF hr hτ)
      (fun t ↦ ((_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 heq) τ)) t).symm)
end Martingale
end MeasureTheory


