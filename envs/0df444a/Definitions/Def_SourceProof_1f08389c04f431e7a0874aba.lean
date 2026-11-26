-- Prove2me | Definitions.Def_SourceProof_1f08389c04f431e7a0874aba
-- name    : SourceProof_1f08389c04f431e7a0874aba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:23:29.637804+00:00
-- url     : https://prove2.me/theorems/fce34a8d-31f1-417f-b2af-c02d73d730b8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_stochasticExponential_of_continuous

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_314794411901083e0cc253d3
import Definitions.Def_SourceProof_5fba6145a988c3f8a6970ab9
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_80c4eebd8b1285b250fd01ee
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_c41f284109b0aab2c9e785eb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous paths of the single product-defined stochastic exponential

The continuous case is a theorem about the same product expression, not a
separate exponential owner. No global moment or boundedness premise is imposed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_1f08389c04f431e7a0874aba
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    IsSemimartingale (hX.stochasticExponential hF) F P := by
  have hK := (_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 ((_root_.Prove2MeSourceProof.h_314794411901083e0cc253d3 hX) hF)) (1 / 2))
  exact (_root_.Prove2MeSourceProof.h_c41f284109b0aab2c9e785eb ((_root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9 hK) hF Real.contDiff_exp)) hF
    (_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 ((_root_.Prove2MeSourceProof.h_80c4eebd8b1285b250fd01ee hX) hF hc))
end IsSemimartingale

end ProbabilityTheory


