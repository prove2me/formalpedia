-- Prove2me | Definitions.Def_SourceProof_c0529761b77dfaa59304baae
-- name    : SourceProof_c0529761b77dfaa59304baae
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:04:06.85426+00:00
-- url     : https://prove2.me/theorems/63daa1bd-3da6-40c3-8057-e6e23d992df1
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integrable_stoppedValue_of_bounded_usual

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Definitions.Def_SourceProof_65f6558045cd9c27c326b519

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

theorem _root_.Prove2MeSourceProof.h_c0529761b77dfaa59304baae (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : Integrable (stoppedValue X τ) P :=
  integrable_condExp.congr
    ((_root_.Prove2MeSourceProof.h_65f6558045cd9c27c326b519 hX) hF hr hτ hbound).symm
end Martingale
end MeasureTheory


