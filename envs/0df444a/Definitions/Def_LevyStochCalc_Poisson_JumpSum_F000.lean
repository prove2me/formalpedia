-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpSum_F000
-- name    : LevyStochCalc_Poisson_JumpSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:49:21.521173+00:00
-- url     : https://prove2.me/theorems/50f55f21-a610-4918-91d3-f9180ba50acf
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pathwise jump sum on a finite-activity window

A measure that is a finite sum of Dirac masses integrates every function as the corresponding
finite sum, so on a set of finite intensity the integral against a Poisson random measure is
almost surely a finite sum over its atoms. The distinct times among those atoms are the jump
times of the window, and a finite set of reals carries a strictly monotone enumeration.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

section SumDirac

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The lower integral against a finite sum of Dirac masses. -/
theorem lintegral_of_eq_sum_dirac {μ : Measure α} {s : Finset α}
    (hμ : μ = ∑ p ∈ s, μ {p} • Measure.dirac p) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ = ∑ p ∈ s, μ {p} * g p := by
  conv_lhs => rw [hμ]
  rw [lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun p _ => by rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
/-- The integral against a finite sum of Dirac masses. -/
theorem integral_of_eq_sum_dirac {μ : Measure α} [IsFiniteMeasure μ] {s : Finset α}
    (hμ : μ = ∑ p ∈ s, μ {p} • Measure.dirac p) (g : α → ℝ) :
    ∫ a, g a ∂μ = ∑ p ∈ s, (μ {p}).toReal * g p := by
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  exact Finset.sum_congr rfl fun p _ => by
    rw [integral_smul_measure, integral_dirac, smul_eq_mul]
end SumDirac

section Enumeration

/-- A finite set of reals carries a strictly monotone enumeration. -/
theorem exists_strictMono_enum (s : Finset ℝ) :
    ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧ Set.range e = (s : Set ℝ) := by
  refine ⟨s.card, fun i => (s.orderIsoOfFin rfl i : ℝ), fun i j hij => ?_, ?_⟩
  · exact Subtype.coe_lt_coe.mpr ((s.orderIsoOfFin rfl).lt_iff_lt.mpr hij)
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.orderIsoOfFin rfl i).2
    · intro hx
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp⟩
end Enumeration

section Poisson

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- The times at which a finite set of time–mark points sits. -/
noncomputable def jumpTimes (s : Finset (ℝ × E)) : Finset ℝ := s.image Prod.fst
/-- **The pathwise jump sum.** On a set of finite intensity the integral against a Poisson random
measure is almost surely a finite sum over finitely many time–mark points, in both the lower and
the Bochner form, with a strictly monotone enumeration of the times involved. -/
theorem ae_exists_finset_integral_eq_sum (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (∀ g : ℝ × E → ℝ≥0∞,
        ∫⁻ p in R, g p ∂(N.N ω) = ∑ p ∈ s, ((N.N ω).restrict R) {p} * g p) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in R, g p ∂(N.N ω) = ∑ p ∈ s, (((N.N ω).restrict R) {p}).toReal * g p) ∧
      ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧ Set.range e = (jumpTimes s : Set ℝ) := by
  filter_upwards [ae_exists_eq_sum_dirac N hRm hRfin, N.integer_valued hRm hRfin] with ω hω hωn
  obtain ⟨s, hs⟩ := hω
  haveI : IsFiniteMeasure ((N.N ω).restrict R) := by
    obtain ⟨n, hn⟩ := hωn
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hn]
    exact ENNReal.natCast_lt_top n
  exact ⟨s, fun g => lintegral_of_eq_sum_dirac hs g, fun g => integral_of_eq_sum_dirac hs g,
    exists_strictMono_enum (jumpTimes s)⟩
/-- **The pathwise jump sum on a finite-activity window.** -/
theorem ae_exists_finset_integral_eq_sum_Ioc (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (∀ g : ℝ × E → ℝ≥0∞,
        ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
          = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
          = ∑ p ∈ s, (((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p}).toReal * g p) ∧
      ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧ Set.range e = (jumpTimes s : Set ℝ) :=
  ae_exists_finset_integral_eq_sum N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν T)
end Poisson

end LevyStochCalc.Poisson


