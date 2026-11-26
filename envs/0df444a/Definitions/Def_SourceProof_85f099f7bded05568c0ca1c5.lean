-- Prove2me | Definitions.Def_SourceProof_85f099f7bded05568c0ca1c5
-- name    : SourceProof_85f099f7bded05568c0ca1c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:34:30.706613+00:00
-- url     : https://prove2.me/theorems/9b799ec2-b43e-4c6f-b231-56b0598d0564
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isQuadraticPureJump_of_finiteVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_PureJump_F000
import Definitions.Def_SourceProof_27187552e7c655b929fb6618

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic pure-jump semimartingales

This is a property of the existing semimartingale and its sole continuous
bracket, not a competing process or bracket owner. Quadratic pure jump does
not mean a process is constant between jumps: continuous FV drift qualifies.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_85f099f7bded05568c0ca1c5
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P) :
    hX.IsQuadraticPureJump hF := (_root_.Prove2MeSourceProof.h_27187552e7c655b929fb6618 hX) hF hv
end IsSemimartingale

end ProbabilityTheory


