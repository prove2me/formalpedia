-- Prove2me | Definitions.Def_SourceProof_2439047738a37409f89b5f59
-- name    : SourceProof_2439047738a37409f89b5f59
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:38:01.962706+00:00
-- url     : https://prove2.me/theorems/d4413b22-4efd-4e2e-bbec-452cf96947b2
-- title:
--   StochLean source theorem: ProbabilityTheory.isLocalMartingale_of_locally_localMartingale

import Definitions.Def_SourceProof_0eeee2a3ca95a90462219fb9
import Definitions.Def_SourceProof_483a38122c0794d4f44bb801
import Definitions.Def_SourceProof_4d9ed9e8ca4be02b9f13e6fa
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4

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


theorem _root_.Prove2MeSourceProof.h_2439047738a37409f89b5f59 (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P) (hL : Locally (fun Y ↦ IsLocalMartingale Y F P) F X P) :
    IsLocalMartingale X F P := by
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  apply _root_.Prove2MeSourceProof.h_483a38122c0794d4f44bb801 hF hcad
  exact (_root_.Prove2MeSourceProof.h_0eeee2a3ca95a90462219fb9 hF).locally_induction
    (fun _ hY ↦ (_root_.Prove2MeSourceProof.h_4d9ed9e8ca4be02b9f13e6fa hY)) hL
end ProbabilityTheory


