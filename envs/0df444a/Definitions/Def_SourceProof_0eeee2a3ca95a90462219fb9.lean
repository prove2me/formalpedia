-- Prove2me | Definitions.Def_SourceProof_0eeee2a3ca95a90462219fb9
-- name    : SourceProof_0eeee2a3ca95a90462219fb9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:59.71496+00:00
-- url     : https://prove2.me/theorems/66e7c1e3-982e-4390-a50a-42313f1ab38d
-- title:
--   StochLean source theorem: ProbabilityTheory.isStable_cadlagUIMartingale

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_5ac3f4c5fe22f7841ec0a6bc
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_aa372c8273bcd3cd6307f406
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

theorem _root_.Prove2MeSourceProof.h_0eeee2a3ca95a90462219fb9 (hF : F.IsUsual P) :
    IsStable F (fun Y ↦ IsUIMartingale Y F P ∧ HasCadlagPaths Y P) := by
  intro Y hY τ hτ
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using (hτ 0).compl
  have hcad := (_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hY.2) {ω | 0 < τ ω}
  exact ⟨(_root_.Prove2MeSourceProof.h_aa372c8273bcd3cd6307f406 ((_root_.Prove2MeSourceProof.h_5ac3f4c5fe22f7841ec0a6bc hY.1) hs)) hF
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hcad) hτ, (_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hcad) τ⟩
end ProbabilityTheory


