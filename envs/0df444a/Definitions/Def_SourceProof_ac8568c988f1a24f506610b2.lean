-- Prove2me | Definitions.Def_SourceProof_ac8568c988f1a24f506610b2
-- name    : SourceProof_ac8568c988f1a24f506610b2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:14:01.06378+00:00
-- url     : https://prove2.me/theorems/42d4ee69-8733-5058-918d-5b2da90df5bd
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.adapted_quadraticCovariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_76e6f1c00540bd94935e0dc0
import Definitions.Def_SourceProof_98bda33797c63c6cacfeb839
import Definitions.Def_SourceProof_d0e331387f6701b34b2c711d

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
theorem _root_.Prove2MeSourceProof.h_ac8568c988f1a24f506610b2
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Adapted F (hX.quadraticCovariation hY hF) := fun t ↦
  ((((_root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) hF t).sub ((_root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839 hX) hF t)).sub
    ((_root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839 hY) hF t)).const_mul (1 / 2)
end IsSemimartingale

end ProbabilityTheory


