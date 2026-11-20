-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Atomic_F001
-- name    : LevyStochCalc_Poisson_Atomic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:48:47.587234+00:00
-- url     : https://prove2.me/theorems/3bac22a9-7783-47d4-b5ae-5ec4c442a933
-- title:
--   Source declarations: LevyStochCalc.Poisson.Atomic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Atomic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_FiniteActivity_F000
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
import Definitions.Def_SourceProof_2d4c8b457cb0b7f5fdc2dc58

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

end CountablyGenerated

section Atomic

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **Atomicity on a set of finite intensity.** The Poisson random measure restricted to a set of
finite intensity is almost surely a finite sum of Dirac masses. -/
theorem ae_exists_eq_sum_dirac (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (N.N ω).restrict R = ∑ p ∈ s, ((N.N ω).restrict R) {p} • Measure.dirac p := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N hRm hRfin] with ω hω
  exact Probability.exists_eq_sum_dirac hω
/-- A set of finite intensity almost surely carries the Poisson random measure on finitely many
time–mark points. -/
theorem ae_exists_finset_support (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E), N.N ω (R \ (s : Set (ℝ × E))) = 0 := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N hRm hRfin] with ω hω
  obtain ⟨s, hs⟩ := Probability.exists_finset_ae_mem hω
  refine ⟨s, ?_⟩
  rw [MeasureTheory.ae_iff, Measure.restrict_apply] at hs
  · rw [← hs]
    congr 1
    ext p
    simp [and_comm]
  · exact s.measurableSet.compl
/-- **Atomicity on a finite-activity window.** Over a bounded time window and a mark set of finite
intensity, the Poisson random measure is almost surely a finite sum of Dirac masses. -/
theorem ae_exists_eq_sum_dirac_Ioc (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} • Measure.dirac p :=
  ae_exists_eq_sum_dirac N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν T)
/-- **Finite activity, support half.** Over a bounded time window and a mark set of finite
intensity, the Poisson random measure is almost surely carried by finitely many time–mark
points. -/
theorem ae_exists_finset_support_Ioc (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      N.N ω ((Set.Ioc (0 : ℝ) T ×ˢ A) \ (s : Set (ℝ × E))) = 0 :=
  ae_exists_finset_support N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν T)
end Atomic

end LevyStochCalc.Poisson


