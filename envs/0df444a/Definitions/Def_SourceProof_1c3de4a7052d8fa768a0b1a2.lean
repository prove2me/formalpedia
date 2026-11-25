-- Prove2me | Definitions.Def_SourceProof_1c3de4a7052d8fa768a0b1a2
-- name    : SourceProof_1c3de4a7052d8fa768a0b1a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:21:46.233628+00:00
-- url     : https://prove2.me/theorems/f76ef1d3-cb69-4f9d-8e52-0c6b0f067972
-- title:
--   StochLean source theorem: ProbabilityTheory.HasLocallyIntegrableVariation.locally_adapted_cadlag_integrableVariation

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrableLocalization_F000

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

namespace HasLocallyIntegrableVariation

theorem _root_.Prove2MeSourceProof.h_1c3de4a7052d8fa768a0b1a2
    (hX : HasLocallyIntegrableVariation X F P) (ha : Adapted F X)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Locally (fun Y ↦ Adapted F Y ∧ HasCadlagPaths Y P ∧
      HasIntegrableVariation Y P) F X P := by
  obtain ⟨τ, hτ, hv⟩ := hX
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  have hs := adapted_cadlag_masked_stoppedProcess ha hF hc (hτ.isStoppingTime n)
  exact ⟨hs.1, hs.2, hv n⟩
end HasLocallyIntegrableVariation

end ProbabilityTheory


