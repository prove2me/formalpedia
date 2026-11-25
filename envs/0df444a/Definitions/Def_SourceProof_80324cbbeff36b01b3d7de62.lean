-- Prove2me | Definitions.Def_SourceProof_80324cbbeff36b01b3d7de62
-- name    : SourceProof_80324cbbeff36b01b3d7de62
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:11:54.886258+00:00
-- url     : https://prove2.me/theorems/44f8eb7b-9aa4-486d-a223-ed66baebe088
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_const_mul

import Definitions.Def_SourceProof_273ddc3f085d385a3a11a0a8
import Definitions.Def_SourceProof_291aad4ab03bb1d5b777f066
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_954e10b76576263a9def2e7a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic algebra of the existing continuous square component -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_80324cbbeff36b01b3d7de62
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c).continuousQuadraticVariation hF)
      ((c ^ 2) • hX.continuousQuadraticVariation hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_291aad4ab03bb1d5b777f066 ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c)) hF,
    (_root_.Prove2MeSourceProof.h_954e10b76576263a9def2e7a hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c) hF c,
    (_root_.Prove2MeSourceProof.h_273ddc3f085d385a3a11a0a8 hX) hX hF c,
    (_root_.Prove2MeSourceProof.h_291aad4ab03bb1d5b777f066 hX) hF] with ω hs hl hr hself t
  rw [← hs t, hl t]
  simp only [Pi.smul_apply, smul_eq_mul, hr t, hself t]
  ring
end IsSemimartingale

end ProbabilityTheory


