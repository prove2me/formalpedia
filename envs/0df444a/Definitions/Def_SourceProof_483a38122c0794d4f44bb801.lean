-- Prove2me | Definitions.Def_SourceProof_483a38122c0794d4f44bb801
-- name    : SourceProof_483a38122c0794d4f44bb801
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:33:13.331892+00:00
-- url     : https://prove2.me/theorems/0ef4b7b8-a7a3-4f11-b07f-ecd0c79afeee
-- title:
--   StochLean source theorem: ProbabilityTheory.isLocalMartingale_of_locally_cadlagUI

import Definitions.Def_SourceProof_0eeee2a3ca95a90462219fb9
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_a3c1e53eb5c3f652441db1d0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Iterated localization

The stable property used internally is the conjunction of the canonical UI
martingale and common-event cadlag predicates. Mathlib's diagonal extraction
and local-property idempotence are reused. An explicit tail infimum converts
its AE-monotone witness to the everywhere-monotone fundamental sequence used
by this project. No local-martingale theorem is assumed as a structure field.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_483a38122c0794d4f44bb801 (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsUIMartingale Y F P ∧ HasCadlagPaths Y P) F X P) :
    IsLocalMartingale X F P := by
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  obtain ⟨τ, hτ, hu⟩ := hL
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ ⨅ j ≥ n, τ j ω
  have hσ : IsLocalizingSequence F σ P := hτ.toIsPreLocalizingSequence.isLocalizingSequence_biInf
  have hsmall (n : ℕ) : σ n ≤ τ n := fun _ ↦ (iInf_le _ n).trans (iInf_le _ le_rfl)
  refine ⟨(_root_.Prove2MeSourceProof.h_a3c1e53eb5c3f652441db1d0 hτ.toIsPreLocalizingSequence) hF
    (fun n ↦ (hu n).1.1.stronglyAdapted.adapted), hcad,
    σ, hσ.toIsPreLocalizingSequence, ?_, fun n ↦ ?_⟩
  · intro n m hnm ω
    exact iInf_le_iInf_of_subset (fun j hj ↦ hnm.trans hj)
  · rw [stoppedProcess_indicator_comm',
      ← stoppedProcess_stoppedProcess_of_le_right (hsmall n),
      ← stoppedProcess_indicator_comm']
    convert ((_root_.Prove2MeSourceProof.h_0eeee2a3ca95a90462219fb9 hF) _ (hu n) (σ n) (hσ.isStoppingTime n)).1 using 2
    ext t
    rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
    congr with ω
    exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h (hsmall n ω)⟩, fun h ↦ h.1⟩
end ProbabilityTheory


