-- Prove2me | Definitions.Def_SourceProof_46e00cd1de49de31920230f6
-- name    : SourceProof_46e00cd1de49de31920230f6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:15:48.045577+00:00
-- url     : https://prove2.me/theorems/45726c61-a18a-4e04-8670-8eee29694922
-- title:
--   StochLean source theorem: MeasureTheory.IsCompleteSubMeasurableSpace.measurable_congr_ae

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F000
import Definitions.Def_SourceProof_7c6e147e93638a97c49079d1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Complete and usual filtrations

Right continuity and completeness are kept as separate requirements. In particular, applying
`Filtration.rightCont` does not manufacture subsets of null sets in the initial sigma-algebra.
This file defines the property only; a completed right-continuation must change to the genuinely
completed measurable-space/measure setting and is deliberately not faked on the same ambient
space.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

namespace IsCompleteSubMeasurableSpace

variable {P : Measure Ω} {m' : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 {E : Type*} [MeasurableSpace E] {f g : Ω → E}
    (hc : IsCompleteSubMeasurableSpace P m') (hf : Measurable[m'] f)
    (hfg : f =ᵐ[P] g) : Measurable[m'] g := by
  have hnull : P {ω | f ω ≠ g ω} = 0 := ae_iff.mp hfg
  intro s hs
  have heq : g ⁻¹' s = (f ⁻¹' s \ {ω | f ω ≠ g ω}) ∪
      ((g ⁻¹' s) ∩ {ω | f ω ≠ g ω}) := by
    ext ω
    by_cases h : f ω = g ω <;> simp [h]
  rw [heq]
  exact ((hf hs).diff (hc _ hnull)).union
    ((_root_.Prove2MeSourceProof.h_7c6e147e93638a97c49079d1 hc) hnull inter_subset_right)
end IsCompleteSubMeasurableSpace

namespace Filtration

variable [PartialOrder ι] [OrderBot ι]

namespace IsUsual

variable {ℱ : Filtration ι m} {P : Measure Ω}

end IsUsual

end Filtration

end MeasureTheory


