-- Prove2me | Definitions.Def_SourceProof_9a15eada3555a513322a1de0
-- name    : SourceProof_9a15eada3555a513322a1de0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:52:15.404485+00:00
-- url     : https://prove2.me/theorems/fa127638-0528-4de5-a28e-6c37ed948fc4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_quadraticCovariation

import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_0f6a1de2f7189d335c4ff9a7
import Definitions.Def_SourceProof_7cf7a410d6e0dc72e8d3a915
import Definitions.Def_SourceProof_ac8568c988f1a24f506610b2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw quadratic covariation by polarization of the canonical square bracket

This is the design's sole mixed bracket owner. It retains `X₀ Y₀`, is adapted
and cadlag, and has locally finite-variation paths. It is not asserted to be
increasing and is not a predictable compensator bracket.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.quadraticCovariation hY hF) F P :=
  (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f ((_root_.Prove2MeSourceProof.h_7cf7a410d6e0dc72e8d3a915 hX) hY hF))
    ((_root_.Prove2MeSourceProof.h_ac8568c988f1a24f506610b2 hX) hY hF) hF ((_root_.Prove2MeSourceProof.h_0f6a1de2f7189d335c4ff9a7 hX) hY hF)
end IsSemimartingale

end ProbabilityTheory


