-- Prove2me | Definitions.Def_SourceProof_572c1c8cd05e41fc98478d36
-- name    : SourceProof_572c1c8cd05e41fc98478d36
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:21:10.993113+00:00
-- url     : https://prove2.me/theorems/737c34b7-f208-5a87-8c37-df16753586dc
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_stochasticExponential

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
import Definitions.Def_SourceProof_314794411901083e0cc253d3
import Definitions.Def_SourceProof_5fba6145a988c3f8a6970ab9
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_6f2fc61c5094ff5a778add37
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_ba54eeb3a2661e253611936f
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The product-defined stochastic exponential is a semimartingale

General cadlag adaptedness and finite variation of the product factor
are proved prerequisites. C2 preservation and multiplication then give
semimartingale regularity of the same canonical expression. This result
does not yet assert its stochastic equation or uniqueness.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_572c1c8cd05e41fc98478d36
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.stochasticExponential hF) F P := by
  have hK := (_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 ((_root_.Prove2MeSourceProof.h_314794411901083e0cc253d3 hX) hF)) (1 / 2))
  exact (_root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f ((_root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9 hK) hF Real.contDiff_exp))
    ((_root_.Prove2MeSourceProof.h_6f2fc61c5094ff5a778add37 hX) hF) hF
end IsSemimartingale

end ProbabilityTheory


