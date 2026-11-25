-- Prove2me | Definitions.Def_SourceProof_362f6277c2a889bfdf4decbb
-- name    : SourceProof_362f6277c2a889bfdf4decbb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:59:00.371143+00:00
-- url     : https://prove2.me/theorems/b0903be8-88ea-4176-9460-9130fc415ecd
-- title:
--   StochLean source theorem: ProbabilityTheory.hasLocallyIntegrableVariation_of_locally

import Definitions.Def_SourceProof_1c3de4a7052d8fa768a0b1a2
import Definitions.Def_SourceProof_89d02dd332d0609a78c6ab15
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4

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


theorem _root_.Prove2MeSourceProof.h_362f6277c2a889bfdf4decbb [IsFiniteMeasure P]
    (hF : F.IsUsual P) (ha : Adapted F X) (hc : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ HasLocallyIntegrableVariation Y F P) F X P) :
    HasLocallyIntegrableVariation X F P := by
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  have hLL : Locally (fun Y ↦ Locally (fun Z ↦ Adapted F Z ∧
      ProbabilityTheory.HasCadlagPaths Z P ∧ ProbabilityTheory.HasIntegrableVariation Z P) F Y P) F X P := by
    obtain ⟨τ, hτ, hv⟩ := hL
    refine ⟨τ, hτ, fun n ↦ ?_⟩
    have hs := adapted_cadlag_masked_stoppedProcess ha hF hc (hτ.isStoppingTime n)
    exact (_root_.Prove2MeSourceProof.h_1c3de4a7052d8fa768a0b1a2 (hv n)) hs.1 hF hs.2
  have hB := (_root_.Prove2MeSourceProof.h_89d02dd332d0609a78c6ab15 hF).locally_locally_iff.mp hLL
  exact hB.mono fun _ hY ↦ hY.2.2
end ProbabilityTheory


