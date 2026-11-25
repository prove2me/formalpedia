-- Prove2me | Definitions.Def_SourceProof_4a8bcb85f4270fc84f814740
-- name    : SourceProof_4a8bcb85f4270fc84f814740
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:42:57.367113+00:00
-- url     : https://prove2.me/theorems/cfc973f8-308d-4bcf-b49f-5f5c6690ffb4
-- title:
--   StochLean source theorem: ProbabilityTheory.isLocalMartingale_of_locally_martingale

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_2439047738a37409f89b5f59
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_d10d9f3d5d51b3a9f867c81c

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


theorem _root_.Prove2MeSourceProof.h_4a8bcb85f4270fc84f814740 (hF : F.IsUsual P)
    (hcad : HasCadlagPaths X P) (hL : Locally (fun Y ↦ Martingale Y F P) F X P) :
    IsLocalMartingale X F P := by
  obtain ⟨τ, hτ, hu⟩ := hL
  apply _root_.Prove2MeSourceProof.h_2439047738a37409f89b5f59 hF hcad
  exact ⟨τ, hτ, fun n ↦ (_root_.Prove2MeSourceProof.h_d10d9f3d5d51b3a9f867c81c (hu n))
    ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hcad) {ω | 0 < τ n ω})) (τ n))⟩
end ProbabilityTheory


