-- Prove2me | Definitions.Def_SourceProof_94fc4811fced36c599242ba4
-- name    : SourceProof_94fc4811fced36c599242ba4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:56:08.443422+00:00
-- url     : https://prove2.me/theorems/04e16edd-d272-4c69-9104-735e886b270a
-- title:
--   StochLean source theorem: MeasureTheory.Filtration.IsUsual.rightContinuous

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

theorem _root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 (h : IsUsual ℱ P) : ℱ.IsRightContinuous :=
  h.1
end IsUsual

end Filtration

end MeasureTheory


