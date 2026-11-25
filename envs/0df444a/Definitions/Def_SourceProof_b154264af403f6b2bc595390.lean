-- Prove2me | Definitions.Def_SourceProof_b154264af403f6b2bc595390
-- name    : SourceProof_b154264af403f6b2bc595390
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:30:59.164959+00:00
-- url     : https://prove2.me/theorems/be248529-c2c8-48dc-a04f-403d6371dc72
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_congr

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_264d677d5da3fcd447059c80
import Definitions.Def_SourceProof_6f12ceaef9e4802a31ac72de
import Definitions.Def_SourceProof_7a2cd734cad19a873789e942

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Version invariance and continuous-path specialization of the continuous bracket -/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_b154264af403f6b2bc595390
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hXY : Indistinguishable X Y P) :
    Indistinguishable (hX.continuousQuadraticVariation hF)
      (hY.continuousQuadraticVariation hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hX) hF,
    (_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hY) hF,
    (_root_.Prove2MeSourceProof.h_6f12ceaef9e4802a31ac72de hX) hY hF hXY, hXY, (_root_.Prove2MeSourceProof.h_264d677d5da3fcd447059c80 hXY)]
    with ω hx hy hq hxy hj t
  have hsum : (∑' s : Ioc 0 t, (ProbabilityTheory.jumpProcess X s ω) ^ 2) =
      ∑' s : Ioc 0 t, (ProbabilityTheory.jumpProcess Y s ω) ^ 2 := by
    apply tsum_congr
    intro s
    rw [hj s]
  have h := (hx t).2
  rw [hq t, hxy 0, hsum] at h
  linarith [(hy t).2]
end IsSemimartingale

end ProbabilityTheory


