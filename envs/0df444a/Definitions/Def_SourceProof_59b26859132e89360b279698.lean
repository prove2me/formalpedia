-- Prove2me | Definitions.Def_SourceProof_59b26859132e89360b279698
-- name    : SourceProof_59b26859132e89360b279698
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:56:10.671599+00:00
-- url     : https://prove2.me/theorems/39621ddf-43eb-4c12-85e7-c9a73a7528f4
-- title:
--   StochLean source theorem: MeasureTheory.Filtration.IsUsual.complete_initial

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001

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

end IsCompleteSubMeasurableSpace

namespace Filtration

variable [PartialOrder ι] [OrderBot ι]

namespace IsUsual

variable {ℱ : Filtration ι m} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_59b26859132e89360b279698 (h : IsUsual ℱ P) :
    IsCompleteSubMeasurableSpace P (ℱ ⊥) :=
  h.2
end IsUsual

end Filtration

end MeasureTheory


