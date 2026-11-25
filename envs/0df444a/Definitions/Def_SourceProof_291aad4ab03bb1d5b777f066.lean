-- Prove2me | Definitions.Def_SourceProof_291aad4ab03bb1d5b777f066
-- name    : SourceProof_291aad4ab03bb1d5b777f066
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:50:30.707912+00:00
-- url     : https://prove2.me/theorems/1a1a0263-2d19-4a7c-b3b3-1c4039cd110a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation_self

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
import Definitions.Def_SourceProof_1d0b25291561423c84395ca8
import Definitions.Def_SourceProof_3f728ff17fd2f56aaee18b4e
import Definitions.Def_SourceProof_7a2cd734cad19a873789e942

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bilinearity of continuous covariation

The common-event raw identities and absolutely summable jump series give the
algebraic identities. No varying-integrator UCP continuity principle is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_291aad4ab03bb1d5b777f066
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.continuousQuadraticCovariation hX hF)
      (hX.continuousQuadraticVariation hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_1d0b25291561423c84395ca8 hX) hX hF,
    (_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hX) hF, (_root_.Prove2MeSourceProof.h_3f728ff17fd2f56aaee18b4e hX) hF]
    with ω hmix hx hraw t
  have hm := (hmix t).2
  rw [hraw t] at hm
  simp only [← pow_two] at hm
  linarith [(hx t).2]
end IsSemimartingale

end ProbabilityTheory


