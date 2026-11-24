-- Prove2me | Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F000
-- name    : StochLean_Probability_Process_Filtration_Usual_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:47.334801+00:00
-- url     : https://prove2.me/theorems/0c6242ab-d42a-4334-80b7-cac6e6b0b060
-- title:
--   Completeness relative to an ambient measure
-- statement:
--   A sub-sigma-algebra is complete relative to a measure when every set of measure zero belongs to that sub-sigma-algebra.

import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration

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

/-- A sub-sigma-algebra is complete for `P` relative to the ambient probability space when it
contains every `P`-null subset of the ambient space. For the initial sigma-algebra of a usual
filtration this is the standard, stronger requirement: the null set need not already belong to
the smaller sigma-algebra. -/
def IsCompleteSubMeasurableSpace (P : Measure Ω) (m' : MeasurableSpace Ω) : Prop :=
  ∀ s, P s = 0 → MeasurableSet[m'] s
namespace IsCompleteSubMeasurableSpace

variable {P : Measure Ω} {m' : MeasurableSpace Ω}

end IsCompleteSubMeasurableSpace

namespace Filtration

variable [PartialOrder ι] [OrderBot ι]

namespace IsUsual

variable {ℱ : Filtration ι m} {P : Measure Ω}

end IsUsual

end Filtration

end MeasureTheory


