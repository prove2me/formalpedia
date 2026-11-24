-- Prove2me | Definitions.Def_SourceProof_adff851f13316a352bc1b23e
-- name    : SourceProof_adff851f13316a352bc1b23e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:29.279801+00:00
-- url     : https://prove2.me/theorems/5851b763-11c1-4fdd-9299-dffd1d99e452
-- title:
--   StochLean source theorem: ProbabilityTheory.IsFundamentalSequence.isLocalizingSequence

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Protter local martingales and Klenke localization

The canonical local martingale uses masked stopped UI martingales (Protter I.6).
Klenke's unmasked localizer is witness data, not a competing process hierarchy.
The unmasked bridge requires integrability of the initial value. Time is `ℝ≥0`;
stopping times have values in `WithTop ℝ≥0`, and stopped processes are only
evaluated at finite deterministic times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsFundamentalSequence
theorem _root_.Prove2MeSourceProof.h_adff851f13316a352bc1b23e {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsFundamentalSequence X F P τ) : IsLocalizingSequence F τ P :=
  { hτ.1 with mono := ae_of_all _ fun ω _ _ hnm ↦ hτ.2.1 hnm ω }
end IsFundamentalSequence

end ProbabilityTheory


