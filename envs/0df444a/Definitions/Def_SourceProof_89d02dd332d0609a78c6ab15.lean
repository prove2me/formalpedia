-- Prove2me | Definitions.Def_SourceProof_89d02dd332d0609a78c6ab15
-- name    : SourceProof_89d02dd332d0609a78c6ab15
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:50:56.416474+00:00
-- url     : https://prove2.me/theorems/841f06f0-9cc0-4eda-a23b-dcd5c254cf84
-- title:
--   StochLean source theorem: ProbabilityTheory.isStable_adapted_cadlag_integrableVariation

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrableLocalization_F000
import Definitions.Def_SourceProof_19ffdfb9260bf3a7628b85b5
import Definitions.Def_SourceProof_6cfb38f690669c2ac9e645b1

open private adapted_cadlag_masked_stoppedProcess from Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrableLocalization_F000
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


theorem _root_.Prove2MeSourceProof.h_89d02dd332d0609a78c6ab15 (hF : F.IsUsual P) :
    IsStable F (fun Y ↦ Adapted F Y ∧ HasCadlagPaths Y P ∧
      HasIntegrableVariation Y P) := by
  intro Y hY τ hτ
  have hs := adapted_cadlag_masked_stoppedProcess hY.1 hF hY.2.1 hτ
  exact ⟨hs.1, hs.2,
    (_root_.Prove2MeSourceProof.h_6cfb38f690669c2ac9e645b1 Y τ).mpr
      ((_root_.Prove2MeSourceProof.h_19ffdfb9260bf3a7628b85b5 hY.2.2) hY.1 hF hY.2.1 hτ)⟩
end ProbabilityTheory


