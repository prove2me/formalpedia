-- Prove2me | Definitions.Def_SourceProof_65f6558045cd9c27c326b519
-- name    : SourceProof_65f6558045cd9c27c326b519
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:59.023804+00:00
-- url     : https://prove2.me/theorems/f88a8d70-6abc-4845-bf51-7beca93f73a4
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_bounded_usual

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Definitions.Def_SourceProof_abd730752414d0d67e6d98a8
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

theorem _root_.Prove2MeSourceProof.h_65f6558045cd9c27c326b519 (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : stoppedValue X τ =ᵐ[P] P[X T | hτ.measurableSpace] := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX.stronglyAdapted) hF hr
  have hY := hX.congr hprog.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq)
  exact ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) τ).trans
    (((_root_.Prove2MeSourceProof.h_abd730752414d0d67e6d98a8 hY) hprog (ae_of_all _ hreg) hτ hbound).trans
      (condExp_congr_ae ((_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq) T)).symm)
end Martingale
end MeasureTheory


