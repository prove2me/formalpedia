-- Prove2me | Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002
-- name    : LevyStochCalc_Probability_IntegerValuedMeasure_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:28:10.090029+00:00
-- url     : https://prove2.me/theorems/7c730785-a185-4f80-a613-d53b89e28814
-- title:
--   Source declarations: LevyStochCalc.Probability.IntegerValuedMeasure
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.IntegerValuedMeasure. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F001

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

theorem measurableSet_of_mem_finInters {s : ℕ → Set α} (hs : ∀ i, MeasurableSet (s i)) :
    ∀ B ∈ finInters s, MeasurableSet B := by
  rintro _ ⟨t, rfl⟩
  exact MeasurableSet.biInter t.countable_toSet fun i _ => hs i
omit [MeasurableSpace α] in
theorem generateFrom_finInters (s : ℕ → Set α) :
    MeasurableSpace.generateFrom (finInters s)
      = MeasurableSpace.generateFrom (Set.range s) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_)
    (MeasurableSpace.generateFrom_mono ?_)
  · rintro _ ⟨t, rfl⟩
    exact MeasurableSet.biInter t.countable_toSet fun i _ =>
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  · rintro _ ⟨i, rfl⟩
    exact ⟨{i}, by simp⟩
end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

end Atom

end LevyStochCalc.Probability


