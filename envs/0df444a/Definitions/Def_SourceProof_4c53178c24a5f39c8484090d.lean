-- Prove2me | Definitions.Def_SourceProof_4c53178c24a5f39c8484090d
-- name    : SourceProof_4c53178c24a5f39c8484090d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:47:37.505816+00:00
-- url     : https://prove2.me/theorems/2ef46951-6331-54aa-b8e9-f502f7113b35
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.nonempty_bracketRealization

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F000
import Definitions.Def_SourceProof_0f6a1de2f7189d335c4ff9a7
import Definitions.Def_SourceProof_10ef3e31a94985d23953e749
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_669e8684f0a562efdd6c1030
import Definitions.Def_SourceProof_7cf7a410d6e0dc72e8d3a915
import Definitions.Def_SourceProof_81d5b0d969fd9cee9a11b8b9
import Definitions.Def_SourceProof_98bda33797c63c6cacfeb839
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_ac8568c988f1a24f506610b2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable Stieltjes realizations of the canonical raw brackets

These are null-event versions of the already constructed brackets, not another
definition of stochastic quadratic variation. All three path identifications
are indistinguishability statements. Their canonical variation/energy integrals
will therefore have measurable random versions without assumptions on moments.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_4c53178c24a5f39c8484090d
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Nonempty (SemimartingaleBracketRealization hX hY hF) := by
  obtain ⟨A, heq, ha, hA⟩ :=
    (_root_.Prove2MeSourceProof.h_669e8684f0a562efdd6c1030 ((_root_.Prove2MeSourceProof.h_ac8568c988f1a24f506610b2 hX) hY hF))
      hF ((_root_.Prove2MeSourceProof.h_0f6a1de2f7189d335c4ff9a7 hX) hY hF)
      ((_root_.Prove2MeSourceProof.h_7cf7a410d6e0dc72e8d3a915 hX) hY hF)
  obtain ⟨B, hb, hB⟩ :=
    (_root_.Prove2MeSourceProof.h_10ef3e31a94985d23953e749 ((_root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839 hX) hF)) hF
      ((_root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9 hX) hF)
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hX) hF))
  obtain ⟨C, hc, hC⟩ :=
    (_root_.Prove2MeSourceProof.h_10ef3e31a94985d23953e749 ((_root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839 hY) hF)) hF
      ((_root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9 hY) hF)
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hY) hF))
  exact ⟨⟨A, ha.stronglyAdapted.adapted, fun ω ↦ (hA ω).2, fun ω ↦ (hA ω).1.1,
    heq, B, C, hb, hc, hB, hC⟩⟩
end IsSemimartingale

namespace SemimartingaleBracketRealization

variable {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
  (D : SemimartingaleBracketRealization hX hY hF)

end SemimartingaleBracketRealization

end ProbabilityTheory


