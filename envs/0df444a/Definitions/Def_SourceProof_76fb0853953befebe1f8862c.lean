-- Prove2me | Definitions.Def_SourceProof_76fb0853953befebe1f8862c
-- name    : SourceProof_76fb0853953befebe1f8862c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:37:50.16179+00:00
-- url     : https://prove2.me/theorems/3a4a0606-6093-5b08-922b-542cb245583d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_sub

import Definitions.Def_SourceProof_0324bf3338d0da79d1016fe2
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_6f12ceaef9e4802a31ac72de
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Subtraction for the canonical raw square bracket -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_76fb0853953befebe1f8862c
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hX) hY).quadraticVariation hF)
      (fun t ω ↦ hX.quadraticVariation hF t ω -
        2 * hX.quadraticCovariation hY hF t ω + hY.quadraticVariation hF t ω) P := by
  have he : ProbabilityTheory.Indistinguishable (X + (fun t ω ↦ (-1 : ℝ) * Y t ω)) (X - Y) P := by
    apply ae_of_all
    intro ω t
    simp only [Pi.add_apply, Pi.sub_apply, neg_one_mul, sub_eq_add_neg]
  filter_upwards [(_root_.Prove2MeSourceProof.h_0324bf3338d0da79d1016fe2 hX) hY hF (-1),
    (_root_.Prove2MeSourceProof.h_6f12ceaef9e4802a31ac72de ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) (-1)))) ((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hX) hY) hF he]
    with ω ha heω t
  rw [← heω t, ha t]
  ring
end IsSemimartingale

end ProbabilityTheory


