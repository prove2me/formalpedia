-- Prove2me | Definitions.Def_SourceProof_4d9ed9e8ca4be02b9f13e6fa
-- name    : SourceProof_4d9ed9e8ca4be02b9f13e6fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:28:30.837245+00:00
-- url     : https://prove2.me/theorems/7a00164d-83c4-432d-83f3-7c0efe705a1f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.locally_cadlagUI

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_adff851f13316a352bc1b23e
import Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

namespace IsLocalMartingale
omit [IsFiniteMeasure P] in
theorem _root_.Prove2MeSourceProof.h_4d9ed9e8ca4be02b9f13e6fa (hX : IsLocalMartingale X F P) :
    Locally (fun Y ↦ IsUIMartingale Y F P ∧ HasCadlagPaths Y P) F X P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  exact ⟨τ, (_root_.Prove2MeSourceProof.h_adff851f13316a352bc1b23e hτ), fun n ↦
    ⟨hτ.2.2 n, (_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hX.2.1) {ω | 0 < τ n ω})) (τ n)⟩⟩
end IsLocalMartingale

end ProbabilityTheory


