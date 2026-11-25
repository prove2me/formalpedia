-- Prove2me | Definitions.Def_SourceProof_dd5d93162907f5e6520ec487
-- name    : SourceProof_dd5d93162907f5e6520ec487
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:44.620402+00:00
-- url     : https://prove2.me/theorems/6ed16468-8265-47d9-98c3-78d6519a28e8
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.exists_progressive_indistinguishable_of_usual

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
import Definitions.Def_SourceProof_1b5811523ebf232c3a8b514f
import Definitions.Def_SourceProof_49dce693542b34ab5089b45b

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
theorem _root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, IsRightContinuousPath (Y · ω) := by
  obtain ⟨Y, hmod, hprog, hreg⟩ :=
    (_root_.Prove2MeSourceProof.h_49dce693542b34ab5089b45b hX) hF hr
  exact ⟨Y, (_root_.Prove2MeSourceProof.h_1b5811523ebf232c3a8b514f hmod) hr (ae_of_all _ hreg), hprog, hreg⟩
end StronglyAdapted

namespace Martingale

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

end Martingale
end MeasureTheory


