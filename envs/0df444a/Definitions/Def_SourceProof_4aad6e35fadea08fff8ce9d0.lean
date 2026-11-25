-- Prove2me | Definitions.Def_SourceProof_4aad6e35fadea08fff8ce9d0
-- name    : SourceProof_4aad6e35fadea08fff8ce9d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:31.42294+00:00
-- url     : https://prove2.me/theorems/b7210dc0-b98b-4253-ad71-36ec3930a250
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.measurable_stoppedValue_of_usual

import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_59b26859132e89360b279698
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
theorem _root_.Prove2MeSourceProof.h_4aad6e35fadea08fff8ce9d0
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Measurable[hτ.measurableSpace] (stoppedValue X τ) := by
  obtain ⟨Y, heq, hprog, _⟩ := (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX) hF hr
  have hc : MeasureTheory.IsCompleteSubMeasurableSpace P hτ.measurableSpace := fun A hA ↦
    hτ.le_measurableSpace_of_const_le (fun _ ↦ bot_le) A ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) A hA)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc) (measurable_stoppedValue hprog hτ) ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) τ).symm
end StronglyAdapted

namespace Martingale

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

end Martingale
end MeasureTheory


