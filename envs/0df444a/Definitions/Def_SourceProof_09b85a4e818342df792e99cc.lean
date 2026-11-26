-- Prove2me | Definitions.Def_SourceProof_09b85a4e818342df792e99cc
-- name    : SourceProof_09b85a4e818342df792e99cc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:10:18.917964+00:00
-- url     : https://prove2.me/theorems/64cd96f7-7987-52b9-8925-1178d220810e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_const_mul

import Definitions.Def_SourceProof_3f728ff17fd2f56aaee18b4e
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_e2c06baac8cba6b9bab39b45
import Definitions.Def_SourceProof_f3df3adc8be51e4f63a6abca

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
theorem _root_.Prove2MeSourceProof.h_09b85a4e818342df792e99cc
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c).quadraticVariation hF)
      ((c ^ 2) • hX.quadraticVariation hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_3f728ff17fd2f56aaee18b4e ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c)) hF,
    (_root_.Prove2MeSourceProof.h_f3df3adc8be51e4f63a6abca hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c) hF c,
    (_root_.Prove2MeSourceProof.h_e2c06baac8cba6b9bab39b45 hX) hX hF c, (_root_.Prove2MeSourceProof.h_3f728ff17fd2f56aaee18b4e hX) hF]
    with ω hself hleft hright hx t
  rw [← hself t, hleft t]
  simp only [Pi.smul_apply, smul_eq_mul, hright t, hx t]
  ring
end IsSemimartingale

end ProbabilityTheory


