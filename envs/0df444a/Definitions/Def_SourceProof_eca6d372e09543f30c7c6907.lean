-- Prove2me | Definitions.Def_SourceProof_eca6d372e09543f30c7c6907
-- name    : SourceProof_eca6d372e09543f30c7c6907
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:47:26.623819+00:00
-- url     : https://prove2.me/theorems/b5982b1c-7f8b-55b8-976e-fba510909dc7
-- title:
--   StochLean source theorem: ProbabilityTheory.isLocalMartingale_of_locally_squareIntegrableMartingale

import Definitions.Def_SourceProof_4a8bcb85f4270fc84f814740

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


theorem _root_.Prove2MeSourceProof.h_eca6d372e09543f30c7c6907 (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P) :
    IsLocalMartingale X F P :=
  _root_.Prove2MeSourceProof.h_4a8bcb85f4270fc84f814740 hF hcad (hL.mono (fun _ h ↦ h.1))
end ProbabilityTheory


