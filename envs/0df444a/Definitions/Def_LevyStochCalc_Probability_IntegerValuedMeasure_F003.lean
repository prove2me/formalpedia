-- Prove2me | Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
-- name    : LevyStochCalc_Probability_IntegerValuedMeasure_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:28:40.012113+00:00
-- url     : https://prove2.me/theorems/319872cc-4cef-4a21-b0b0-4dd5f7929470
-- title:
--   Source declarations: LevyStochCalc.Probability.IntegerValuedMeasure
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.IntegerValuedMeasure. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
import Definitions.Def_SourceProof_2a1773b20cfe1824b270a872

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

end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

private theorem exists_finset_ae_mem_aux :
    ∀ n : ℕ, ∀ μ : Measure α, μ Set.univ = n → IsIntegerValued μ →
      ∃ s : Finset α, ∀ᵐ a ∂μ, a ∈ s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro μ hn hint
    classical
    haveI : IsFiniteMeasure μ := ⟨by rw [hn]; exact ENNReal.natCast_lt_top n⟩
    haveI : MeasurableSingletonClass α :=
      MeasurableSpace.measurableSingletonClass_of_countablySeparated
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · refine ⟨∅, ?_⟩
      have huniv : μ Set.univ = 0 := by rw [hn, h0]; simp
      rw [MeasureTheory.Measure.measure_univ_eq_zero.mp huniv]
      simp
    · have hne0 : μ Set.univ ≠ 0 := by rw [hn]; exact_mod_cast hpos.ne'
      obtain ⟨x, hx⟩ := _root_.Prove2MeSourceProof.h_2a1773b20cfe1824b270a872 μ hint hne0
      have hxm : MeasurableSet ({x} : Set α) := measurableSet_singleton x
      have hint' : IsIntegerValued (μ.restrict {x}ᶜ) := by
        intro B hB
        rw [Measure.restrict_apply hB]
        exact hint _ (hB.inter hxm.compl)
      obtain ⟨m, hm⟩ := hint' Set.univ MeasurableSet.univ
      have hmlt : m < n := by
        have h1 : (μ.restrict {x}ᶜ) Set.univ = μ {x}ᶜ := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        have h2 : μ {x} + μ {x}ᶜ = (n : ℝ≥0∞) := by
          rw [measure_add_measure_compl hxm, hn]
        have h3 : (1 : ℝ≥0∞) + (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
          rw [← h2]
          exact add_le_add hx (le_of_eq (by rw [← h1, hm]))
        have h4 : (1 + m : ℕ) ≤ n := by exact_mod_cast h3
        omega
      obtain ⟨s', hs'⟩ := ih m hmlt (μ.restrict {x}ᶜ) hm hint'
      refine ⟨insert x s', ?_⟩
      filter_upwards [(ae_restrict_iff' hxm.compl).mp hs'] with a ha
      by_cases hax : a = x
      · simp [hax]
      · exact Finset.mem_insert_of_mem (ha (by simpa using hax))
/-- An integer-valued measure on a countably separated space is carried by a finite set. -/
theorem exists_finset_ae_mem {μ : Measure α} (hint : IsIntegerValued μ) :
    ∃ s : Finset α, ∀ᵐ a ∂μ, a ∈ s := by
  obtain ⟨n, hn⟩ := hint Set.univ MeasurableSet.univ
  exact exists_finset_ae_mem_aux n μ hn hint
/-- **An integer-valued measure on a countably separated space is a finite sum of Dirac
masses.** -/
theorem exists_eq_sum_dirac {μ : Measure α} (hint : IsIntegerValued μ) :
    ∃ s : Finset α, μ = ∑ a ∈ s, μ {a} • Measure.dirac a := by
  haveI : MeasurableSingletonClass α :=
    MeasurableSpace.measurableSingletonClass_of_countablySeparated
  obtain ⟨s, hs⟩ := exists_finset_ae_mem hint
  exact ⟨s, Measure.ae_mem_finset_iff.mp hs⟩
end Atom

end LevyStochCalc.Probability


