-- Prove2me | Definitions.Def_SourceProof_291f8623e29c3647f4304312
-- name    : SourceProof_291f8623e29c3647f4304312
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:12:06.653094+00:00
-- url     : https://prove2.me/theorems/5a6ff553-c86f-53a3-bba8-0340a39e7ac5
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.stronglyAdapted_largeJumpSumProcesses_of_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_SourceProof_0f66df66fd1447d53fad2f1b
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_3416e99a223013e5435c7120
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_c8232beed6b358cd17e7323d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of the actual large-jump cumulative processes

The literal sums over positive times are identified with the existing countable
stopping-time enumeration. For almost-sure cadlag paths, an everywhere-cadlag
indistinguishable version and relative completeness recover measurability of
the original sums, not merely of a chosen replacement process.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_291f8623e29c3647f4304312
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (hb : 0 < b) :
    StronglyAdapted F (largeJumpSumProcess X b) ∧
      StronglyAdapted F (largeJumpNormSumProcess X b) := by
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  have hsa : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  obtain ⟨Y, hXY, hYa, hYc⟩ := (_root_.Prove2MeSourceProof.h_c8232beed6b358cd17e7323d hsa) hF hc
  have haY := hYa.stronglyAdapted.adapted
  obtain ⟨hA, hC⟩ := (_root_.Prove2MeSourceProof.h_3416e99a223013e5435c7120 haY) hYc hb
  obtain ⟨heA, heC⟩ := (_root_.Prove2MeSourceProof.h_0f66df66fd1447d53fad2f1b hXY) b
  have hcomplete (t : ℝ≥0) : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  constructor
  · intro t
    exact ((_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 (hcomplete t)) (hA t).measurable
      ((_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 heA).mono fun _ hω ↦ hω t)).stronglyMeasurable
  · intro t
    exact ((_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 (hcomplete t)) (hC t).measurable
      ((_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 heC).mono fun _ hω ↦ hω t)).stronglyMeasurable
end Adapted

end MeasureTheory


