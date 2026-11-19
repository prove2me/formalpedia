-- Prove2me | Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F001
-- name    : LevyStochCalc_Probability_IntegerValuedMeasure_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:27:34.157431+00:00
-- url     : https://prove2.me/theorems/6b434680-d697-4031-9c5f-e9aea6aac5f5
-- title:
--   Source declarations: LevyStochCalc.Probability.IntegerValuedMeasure
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.IntegerValuedMeasure. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

section PiSystem

/-- The finite intersections of a sequence of sets. -/
def finInters (s : ℕ → Set α) : Set (Set α) :=
  Set.range fun t : Finset ℕ => ⋂ i ∈ t, s i
omit [MeasurableSpace α] in
theorem mem_finInters_iff {s : ℕ → Set α} {B : Set α} :
    B ∈ finInters s ↔ ∃ t : Finset ℕ, (⋂ i ∈ t, s i) = B := Iff.rfl
omit [MeasurableSpace α] in
theorem countable_finInters (s : ℕ → Set α) : (finInters s).Countable :=
  Set.countable_range _
end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

end Atom

end LevyStochCalc.Probability


