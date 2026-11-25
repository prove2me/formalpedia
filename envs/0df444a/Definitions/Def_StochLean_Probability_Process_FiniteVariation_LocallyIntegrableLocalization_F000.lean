-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrableLocalization_F000
-- name    : StochLean_Probability_Process_FiniteVariation_LocallyIntegrableLocalization_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:05:14.981222+00:00
-- url     : https://prove2.me/theorems/4cdfa329-389e-46b8-a95c-18efee4d1f1d
-- title:
--   StochLean: Probability.Process.FiniteVariation.LocallyIntegrableLocalization F000

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrable_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_96331e337c0a0b8560074745
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
import Definitions.Def_SourceProof_de3c03ff359f630b7abb9271

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Iterated localization of integrable variation

The stable property includes adaptedness and common-event cadlag paths, which
supply the measurability of actual stopped variation. Bare integrable
variation is not asserted to be stable for arbitrary nonadapted processes.

Both levels retain Mathlib's positive-lifetime mask and their original
localizing sequences. The existing stable-property idempotence performs the
diagonal extraction; no additional local predicate or selector is introduced.
Finite measure is needed only for that extraction, not for the stability or
the same-sequence upgrade. Initial values need not vanish or be integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

private theorem adapted_cadlag_masked_stoppedProcess
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Adapted F (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) ∧
      HasCadlagPaths (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) P := by
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := hτ.measurableSet_gt 0
  have hcMask := (_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hc) {ω | 0 < τ ω}
  exact ⟨((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f ((_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 ha) hs).stronglyAdapted) hF
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hcMask) hτ).adapted, (_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hcMask) τ⟩
end ProbabilityTheory


