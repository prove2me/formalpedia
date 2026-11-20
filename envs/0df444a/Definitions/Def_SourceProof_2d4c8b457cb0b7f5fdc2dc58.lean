-- Prove2me | Definitions.Def_SourceProof_2d4c8b457cb0b7f5fdc2dc58
-- name    : SourceProof_2d4c8b457cb0b7f5fdc2dc58
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:48:11.237659+00:00
-- url     : https://prove2.me/theorems/945d24bd-031f-4fb1-ac23-003d1782501d
-- title:
--   LevyStochCalc source module: SourceProof_2d4c8b457cb0b7f5fdc2dc58
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_isIntegerValued_restrict` comes from the `LevyStochCalc.Poisson.Atomic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_SourceProof_3d9324e122196ddc3f47a23f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Atomicity of a Poisson random measure on a finite-activity window

A Poisson random measure carries a natural mass on each measurable set of finite intensity, one
set at a time and only almost surely. Over a window of finite intensity the counts on a countable
generating π-system are simultaneously natural on a single event of full measure, and the sets of
natural mass form a Dynkin system, so on that event the restricted measure is integer-valued. On
a countably separated mark space it is then a finite sum of Dirac masses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section CountablyGenerated

variable [MeasurableSpace.CountablyGenerated E]


theorem _root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, Probability.IsIntegerValued ((N.N ω).restrict R) := by
  classical
  have hcell : ∀ t : Finset ℕ,
      MeasurableSet (⋂ i ∈ t, MeasurableSpace.natGeneratingSequence (ℝ × E) i) :=
    fun t => MeasurableSet.biInter t.countable_toSet
      fun i _ => MeasurableSpace.measurableSet_natGeneratingSequence i
  have hgen : ∀ t : Finset ℕ, ∀ᵐ ω ∂P, ∃ n : ℕ,
      N.N ω ((⋂ i ∈ t, MeasurableSpace.natGeneratingSequence (ℝ × E) i) ∩ R) = n := by
    intro t
    refine N.integer_valued ((hcell t).inter hRm) ?_
    exact ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_right)
  have huniv : ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω R = n := N.integer_valued hRm hRfin
  filter_upwards [ae_all_iff.mpr hgen, huniv] with ω hω hωu
  have hmass : ∃ n : ℕ, ((N.N ω).restrict R) Set.univ = n := by
    obtain ⟨n, hn⟩ := hωu
    exact ⟨n, by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hn⟩
  haveI : IsFiniteMeasure ((N.N ω).restrict R) := by
    obtain ⟨n, hn⟩ := hmass
    exact ⟨by rw [hn]; exact ENNReal.natCast_lt_top n⟩
  refine _root_.Prove2MeSourceProof.h_3d9324e122196ddc3f47a23f (C := LevyStochCalc.Poisson.markPiSystem E)
    LevyStochCalc.Poisson.generateFrom_markPiSystem.symm LevyStochCalc.Poisson.isPiSystem_markPiSystem ?_ hmass
  intro B hB
  obtain ⟨t, rfl⟩ := LevyStochCalc.Probability.mem_finInters_iff.mp hB
  obtain ⟨n, hn⟩ := hω t
  exact ⟨n, by rw [Measure.restrict_apply (hcell t)]; exact hn⟩
end CountablyGenerated

section Atomic

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end Atomic

end LevyStochCalc.Poisson


