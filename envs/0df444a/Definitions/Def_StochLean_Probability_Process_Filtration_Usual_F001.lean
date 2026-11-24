-- Prove2me | Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
-- name    : StochLean_Probability_Process_Filtration_Usual_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:09.853052+00:00
-- url     : https://prove2.me/theorems/738400ea-4386-4cba-8630-d99d543f0149
-- title:
--   StochLean: Probability.Process.Filtration.Usual F001

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

end IsCompleteSubMeasurableSpace

namespace Filtration

variable [PartialOrder ι] [OrderBot ι]

/-- The usual conditions: right continuity together with `P`-completeness of the initial
sigma-algebra. Neither conjunct is silently inferred from the other. -/
def IsUsual (ℱ : Filtration ι m) (P : Measure Ω) : Prop :=
  ℱ.IsRightContinuous ∧ IsCompleteSubMeasurableSpace P (ℱ ⊥)
namespace IsUsual

variable {ℱ : Filtration ι m} {P : Measure Ω}

end IsUsual

end Filtration

end MeasureTheory


