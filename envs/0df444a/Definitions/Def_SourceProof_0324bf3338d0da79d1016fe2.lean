-- Prove2me | Definitions.Def_SourceProof_0324bf3338d0da79d1016fe2
-- name    : SourceProof_0324bf3338d0da79d1016fe2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:31:02.566829+00:00
-- url     : https://prove2.me/theorems/7a3cdf33-5231-5bbd-a311-82033bb8d171
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_add_const_mul

import Definitions.Def_SourceProof_09b85a4e818342df792e99cc
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_3485556bf52a24d375b7ad3f
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_e2c06baac8cba6b9bab39b45

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic identities for the canonical raw square bracket -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_0324bf3338d0da79d1016fe2
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c)).quadraticVariation hF)
      (fun t ω ↦ hX.quadraticVariation hF t ω +
        2 * c * hX.quadraticCovariation hY hF t ω + c ^ 2 * hY.quadraticVariation hF t ω) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_3485556bf52a24d375b7ad3f hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c) hF,
    (_root_.Prove2MeSourceProof.h_e2c06baac8cba6b9bab39b45 hX) hY hF c, (_root_.Prove2MeSourceProof.h_09b85a4e818342df792e99cc hY) hF c]
    with ω hadd hcross hsq t
  rw [hadd t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcross t, hsq t]
  ring
end IsSemimartingale

end ProbabilityTheory


