-- Prove2me | Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
-- name    : SourceProof_d758c5fe1bf7eec6f7a3ad7f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:56:48.756382+00:00
-- url     : https://prove2.me/theorems/ecd8c143-7986-4a52-8bd1-c79344486337
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.stoppedProcess_of_usual

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
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

namespace StronglyAdapted
theorem _root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    StronglyAdapted F (MeasureTheory.stoppedProcess X τ) := by
  obtain ⟨Y, heq, hprog, _⟩ := (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX) hF hr
  intro t
  have hc : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) := fun A hA ↦
    F.mono bot_le A ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) A hA)
  exact ((_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc) (hprog.stronglyAdapted_stoppedProcess hτ t).measurable
    ((_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 heq) τ)) t).symm).stronglyMeasurable
end StronglyAdapted

namespace Martingale

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

end Martingale
end MeasureTheory


