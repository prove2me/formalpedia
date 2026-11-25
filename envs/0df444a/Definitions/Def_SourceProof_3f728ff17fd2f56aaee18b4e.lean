-- Prove2me | Definitions.Def_SourceProof_3f728ff17fd2f56aaee18b4e
-- name    : SourceProof_3f728ff17fd2f56aaee18b4e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:47:39.1272+00:00
-- url     : https://prove2.me/theorems/e7238e03-2afc-5955-b304-03989c0b6e9c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_self

import Definitions.Def_SourceProof_1b4af77c646f5762a3a2d701
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_6443755938a3801e72d73393
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bilinearity and version invariance of the canonical raw covariation

Linearity is inherited from the actual finite increment sums by uniqueness
of UCP limits. All comparisons are on one event for every time.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3f728ff17fd2f56aaee18b4e
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation hX hF) (hX.quadraticVariation hF) P := by
  apply (_root_.Prove2MeSourceProof.h_6443755938a3801e72d73393 hX) hX hF
  · intro π hπ
    simpa only [_root_.Prove2MeSourceProof.h_1b4af77c646f5762a3a2d701] using
      (_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee hX) hF hπ
  · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hX) hF))
end IsSemimartingale

end ProbabilityTheory


