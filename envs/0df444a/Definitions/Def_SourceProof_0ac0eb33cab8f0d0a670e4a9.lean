-- Prove2me | Definitions.Def_SourceProof_0ac0eb33cab8f0d0a670e4a9
-- name    : SourceProof_0ac0eb33cab8f0d0a670e4a9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:46.402135+00:00
-- url     : https://prove2.me/theorems/37c8dd02-8d58-4cf1-9d7c-15d443cceca1
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp_of_bounded_usual

import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Definitions.Def_SourceProof_4f5bf6289f5ec1ba588efedb
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


theorem _root_.Prove2MeSourceProof.h_0ac0eb33cab8f0d0a670e4a9 (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  obtain ⟨Y, heq, hp, hreg⟩ :=
    (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX.stronglyAdapted) hF hr
  have hY := hX.congr hp.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq)
  exact ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) _).trans
    (((_root_.Prove2MeSourceProof.h_4f5bf6289f5ec1ba588efedb hY) hp (ae_of_all _ hreg) hσ hτ hbound).trans
      (condExp_congr_ae ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) τ)).symm)
end Martingale
end MeasureTheory


