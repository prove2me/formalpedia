-- Prove2me | Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
-- name    : LevyStochCalc_Probability_IntegerValuedMeasure_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:04:25.63961+00:00
-- url     : https://prove2.me/theorems/5abef360-38ff-4663-8ccf-46663f3b10bd
-- title:
--   Source declarations: LevyStochCalc.Probability.IntegerValuedMeasure
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.IntegerValuedMeasure, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.PiSystem

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integer-valued finite measures

A measure is integer-valued when every measurable set carries a natural mass. On a measurable
space with a countable separating family such a measure, if finite, is a finite sum of Dirac
masses: a binary search along the separating family isolates a point of mass at least one, and
removing it lowers the total mass by at least one, so the recursion terminates.

Integrality on a generating π-system already gives integrality everywhere, since the sets of
natural mass form a Dynkin system as soon as the ambient measure is finite.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-- A measure is *integer-valued* when every measurable set carries a natural mass. -/
def IsIntegerValued (μ : Measure α) : Prop := ∀ B, MeasurableSet B → ∃ n : ℕ, μ B = n
section PiSystem

end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

end Atom

end LevyStochCalc.Probability


