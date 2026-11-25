-- Prove2me | Definitions.Def_SourceProof_0e901fd5681db7f241412ea5
-- name    : SourceProof_0e901fd5681db7f241412ea5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:14:58.948069+00:00
-- url     : https://prove2.me/theorems/8f625be8-6a87-47f8-9533-068d64026f40
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.eTotalVariationProcess_of_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_06a61994cd7744e3d7c117fb
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_aca8cdff6ae80e53b5557648
import Definitions.Def_SourceProof_c8232beed6b358cd17e7323d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The adapted total-variation process

Variation is first kept in ENNReal, including infinite values. Right continuity,
not continuity, makes actual finite-partition sums converge to it. Real-valued
variation is the canonical Mathlib conversion; its finite-variation interpretation
requires the common-event locally BV hypothesis.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_0e901fd5681db7f241412ea5 (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.eTotalVariationProcess X) := by
  have hs : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  obtain ⟨Y, hXY, hYp, hYc⟩ := (_root_.Prove2MeSourceProof.h_c8232beed6b358cd17e7323d hs) hF hc
  have hYa : Adapted F Y := fun t ↦ (hYp.stronglyAdapted t).measurable
  have hv := (_root_.Prove2MeSourceProof.h_06a61994cd7744e3d7c117fb hYa) (fun ω ↦ (hYc ω).1)
  intro t
  have hcomplete : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hcomplete) (hv t)
    ((_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 (_root_.Prove2MeSourceProof.h_aca8cdff6ae80e53b5557648 hXY)).mono (fun _ hω ↦ hω t))
end Adapted

end MeasureTheory


