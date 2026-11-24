-- Prove2me | Definitions.Def_SourceProof_7c6e147e93638a97c49079d1
-- name    : SourceProof_7c6e147e93638a97c49079d1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:49.796292+00:00
-- url     : https://prove2.me/theorems/58a23e01-e701-4bd0-994a-7b4725afb106
-- title:
--   StochLean source theorem: MeasureTheory.IsCompleteSubMeasurableSpace.mono_null

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F000

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

theorem _root_.Prove2MeSourceProof.h_7c6e147e93638a97c49079d1 (h : IsCompleteSubMeasurableSpace P m')
    {s t : Set Ω} (hs0 : P s = 0) (hts : t ⊆ s) :
    MeasurableSet[m'] t :=
  h t (measure_mono_null hts hs0)
end IsCompleteSubMeasurableSpace

namespace Filtration

variable [PartialOrder ι] [OrderBot ι]

namespace IsUsual

variable {ℱ : Filtration ι m} {P : Measure Ω}

end IsUsual

end Filtration

end MeasureTheory


