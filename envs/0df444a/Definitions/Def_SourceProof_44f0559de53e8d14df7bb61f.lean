-- Prove2me | Definitions.Def_SourceProof_44f0559de53e8d14df7bb61f
-- name    : SourceProof_44f0559de53e8d14df7bb61f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:19:10.443934+00:00
-- url     : https://prove2.me/theorems/1c36380b-f504-5366-8f33-127e9ce3eb22
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_add_const_mul

import Definitions.Def_SourceProof_273ddc3f085d385a3a11a0a8
import Definitions.Def_SourceProof_29ce176e0a41eb350a93631c
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_80324cbbeff36b01b3d7de62
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3

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
theorem _root_.Prove2MeSourceProof.h_44f0559de53e8d14df7bb61f
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c)).continuousQuadraticVariation hF)
      (fun t ω ↦ hX.continuousQuadraticVariation hF t ω +
        2 * c * hX.continuousQuadraticCovariation hY hF t ω +
        c ^ 2 * hY.continuousQuadraticVariation hF t ω) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_29ce176e0a41eb350a93631c hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c) hF,
    (_root_.Prove2MeSourceProof.h_273ddc3f085d385a3a11a0a8 hX) hY hF c,
    (_root_.Prove2MeSourceProof.h_80324cbbeff36b01b3d7de62 hY) hF c] with ω ha hc hq t
  rw [ha t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc t, hq t]
  ring
end IsSemimartingale

end ProbabilityTheory


