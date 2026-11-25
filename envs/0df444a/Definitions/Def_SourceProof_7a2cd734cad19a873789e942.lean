-- Prove2me | Definitions.Def_SourceProof_7a2cd734cad19a873789e942
-- name    : SourceProof_7a2cd734cad19a873789e942
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:17:37.276157+00:00
-- url     : https://prove2.me/theorems/f5c75693-bb3c-480d-b0ce-5d6cf4785b9a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_continuous_jump_decomposition

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_1883eb1f483d860c03239c47
import Definitions.Def_SourceProof_4429ff27e307e8c02b004131
import Definitions.Def_SourceProof_4c53178c24a5f39c8484090d
import Definitions.Def_SourceProof_97ac1be72f56ff014f1c8e3a
import Definitions.Def_SourceProof_c3d82db2ca7eee09ee06d809

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous component of the unique raw quadratic variation

The definition removes the point atoms of a genuine Stieltjes version of the
already constructed raw bracket. It is not a second quadratic-variation
construction. Its exact decomposition uses the squared jumps of the original
semimartingale, with the initial square separate and summability proved.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ (jumpProcess X s ω) ^ 2) ∧
      hX.quadraticVariation hF t ω = (X 0 ω) ^ 2 + hX.continuousQuadraticVariation hF t ω +
        ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2 := by
  let D := Classical.choice ((_root_.Prove2MeSourceProof.h_4c53178c24a5f39c8484090d hX) hX hF)
  filter_upwards [D.left_eq, (_root_.Prove2MeSourceProof.h_1883eb1f483d860c03239c47 hX) hF,
    (_root_.Prove2MeSourceProof.h_4429ff27e307e8c02b004131 hX) hF] with ω heq h0 hj t
  have hjump (s : Ioc 0 t) : D.left ω s - Function.leftLim (D.left ω) s =
      (ProbabilityTheory.jumpProcess X s ω) ^ 2 := by
    have hs : (s : ℝ≥0) ≠ 0 := ne_of_gt s.2.1
    have h := hj s
    change hX.quadraticVariation hF s ω - ProbabilityTheory.leftLimitProcess (hX.quadraticVariation hF) s ω = _ at h
    simp only [ProbabilityTheory.leftLimitProcess, if_neg hs, heq] at h
    exact h
  have hsum := _root_.Prove2MeSourceProof.h_c3d82db2ca7eee09ee06d809 (D.left ω) t
  have hdecomp := _root_.Prove2MeSourceProof.h_97ac1be72f56ff014f1c8e3a (D.left ω) t
  have hinit : D.left ω 0 = (X 0 ω) ^ 2 := (heq 0).symm.trans h0
  refine ⟨?_, ?_⟩
  · simpa only [hjump] using hsum
  · simpa only [hjump, hinit, heq, ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation] using hdecomp
end IsSemimartingale

end ProbabilityTheory


