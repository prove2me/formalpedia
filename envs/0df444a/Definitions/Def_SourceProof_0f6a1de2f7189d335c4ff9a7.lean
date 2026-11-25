-- Prove2me | Definitions.Def_SourceProof_0f6a1de2f7189d335c4ff9a7
-- name    : SourceProof_0f6a1de2f7189d335c4ff9a7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:32:54.0396+00:00
-- url     : https://prove2.me/theorems/8d2f80c9-929d-5a46-9b24-bce1ff17f12d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasCadlagPaths_quadraticCovariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_76e6f1c00540bd94935e0dc0
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
theorem _root_.Prove2MeSourceProof.h_0f6a1de2f7189d335c4ff9a7
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    HasCadlagPaths (hX.quadraticCovariation hY hF) P := by
  have hq := ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) hF))
    ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hX) hF))) ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hY) hF))
  exact (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc hq) (continuous_const.mul continuous_id)
end IsSemimartingale

end ProbabilityTheory


