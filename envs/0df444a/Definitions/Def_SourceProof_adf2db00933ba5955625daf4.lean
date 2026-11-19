-- Prove2me | Definitions.Def_SourceProof_adf2db00933ba5955625daf4
-- name    : SourceProof_adf2db00933ba5955625daf4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:27:59.383201+00:00
-- url     : https://prove2.me/theorems/c62aee72-b0fa-4048-89c5-e808c2433ba6
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.isPiSystem_finInters
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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

omit [MeasurableSpace α] in
theorem _root_.Prove2MeSourceProof.h_adf2db00933ba5955625daf4 (s : ℕ → Set α) : IsPiSystem (finInters s) := by
  rintro _ ⟨t₁, rfl⟩ _ ⟨t₂, rfl⟩ _
  refine ⟨t₁ ∪ t₂, ?_⟩
  change (⋂ i ∈ t₁ ∪ t₂, s i) = (⋂ i ∈ t₁, s i) ∩ (⋂ i ∈ t₂, s i)
  ext x
  constructor
  · intro hx
    exact ⟨Set.mem_iInter₂.mpr fun i hi =>
        Set.mem_iInter₂.mp hx i (Finset.mem_union_left _ hi),
      Set.mem_iInter₂.mpr fun i hi =>
        Set.mem_iInter₂.mp hx i (Finset.mem_union_right _ hi)⟩
  · rintro ⟨h1, h2⟩
    refine Set.mem_iInter₂.mpr fun i hi => ?_
    rcases Finset.mem_union.mp hi with h | h
    · exact Set.mem_iInter₂.mp h1 i h
    · exact Set.mem_iInter₂.mp h2 i h
end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

end Atom

end LevyStochCalc.Probability


