-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F002
-- name    : LevyStochCalc_Poisson_MarkStepPathwise_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:43:46.582513+00:00
-- url     : https://prove2.me/theorems/b7307a29-36be-4272-a3a4-a24f3f3a9789
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepPathwise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepPathwise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-step approximants are pathwise and predictable

The approximants the compensated integral is built from are finite combinations of indicators of
time–mark rectangles with coefficients known at the left endpoint of their piece. Their integral
against any measure finite on those rectangles is the matching finite combination, so over the
whole horizon the approximant's compensated integral is the difference of its integrals against
the random measure and against the reference intensity. Adaptedness of the coefficients makes the
approximant predictable, which is what the compensator identity asks for.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P] {g : TimeGrid}

namespace MarkStep

/-- A mark-step integrand vanishes at nonpositive times. -/
theorem eval_eq_zero_of_nonpos (G : MarkStep Ω E ν g) {s : ℝ} (hs : s ≤ 0) (e : E) (ω : Ω) :
    G.eval s e ω = 0 := by
  classical
  refine Finset.sum_eq_zero fun i hi => ?_
  have hnot : s ∉ Set.Ioc (g.p i) (g.p (i + 1)) := by
    intro hmem
    have h0 : 0 ≤ g.p i := g.p_nonneg (le_of_lt (Finset.mem_range.mp hi))
    exact absurd (lt_of_le_of_lt h0 hmem.1) (not_lt.mpr hs)
  rw [Set.indicator_of_notMem hnot, zero_mul]
section RestrictMarks

variable {A : Set E}

/-- A mark-step integrand with its mark sets cut down to `A`. -/
noncomputable def restrictMarks (G : MarkStep Ω E ν g) (hA : MeasurableSet A) :
    MarkStep Ω E ν g where
  K := G.K
  B := fun k => G.B k ∩ A
  B_measurable := fun k => (G.B_measurable k).inter hA
  B_finite := fun k => ne_top_of_le_ne_top (G.B_finite k) (measure_mono Set.inter_subset_left)
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable
theorem restrictMarks_B_subset (G : MarkStep Ω E ν g) (hA : MeasurableSet A) (k : Fin G.K) :
    (G.restrictMarks hA).B k ⊆ A := Set.inter_subset_right
theorem restrictMarks_adapted (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hG : G.Adapted ℱ) :
    (G.restrictMarks hA).Adapted ℱ := hG
theorem eval_restrictMarks_of_mem (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    (s : ℝ) {e : E} (he : e ∈ A) (ω : Ω) :
    (G.restrictMarks hA).eval s e ω = G.eval s e ω := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  change (G.B k ∩ A).indicator (fun _ => (1 : ℝ)) e = (G.B k).indicator (fun _ => (1 : ℝ)) e
  by_cases hb : e ∈ G.B k
  · rw [Set.indicator_of_mem (show e ∈ G.B k ∩ A from ⟨hb, he⟩),
      Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem (fun h => hb h.1), Set.indicator_of_notMem hb]
theorem eval_restrictMarks_of_notMem (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    (s : ℝ) {e : E} (he : e ∉ A) (ω : Ω) :
    (G.restrictMarks hA).eval s e ω = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _ => ?_
  have hzero : ∑ k : Fin (G.restrictMarks hA).K, (G.restrictMarks hA).ξ i k ω
      * ((G.restrictMarks hA).B k).indicator (fun _ => (1 : ℝ)) e = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Set.indicator_of_notMem (fun h => he h.2), mul_zero]
  rw [hzero, mul_zero]
/-- Cutting the marks down to a set the integrand is carried by cannot increase the error. -/
theorem abs_sub_eval_restrictMarks_le (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    {φ : Ω → ℝ → E → ℝ} (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (ω : Ω) (s : ℝ) (e : E) :
    |φ ω s e - (G.restrictMarks hA).eval s e ω| ≤ |φ ω s e - G.eval s e ω| := by
  by_cases he : e ∈ A
  · rw [G.eval_restrictMarks_of_mem hA s he ω]
  · rw [G.eval_restrictMarks_of_notMem hA s he ω, hsupp ω s e he, sub_zero, abs_zero]
    exact abs_nonneg _
/-- **The mark-restricted approximant is at least as close in energy.** -/
theorem lintegral_sq_sub_eval_restrictMarks_le (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    {φ : Ω → ℝ → E → ℝ} (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (T : ℝ)
    (P : Measure Ω) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - (G.restrictMarks hA).eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => ?_
  refine pow_le_pow_left' ?_ 2
  refine ENNReal.coe_le_coe.mpr ?_
  have habs := G.abs_sub_eval_restrictMarks_le hA hsupp ω s e
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs] at habs
  exact_mod_cast habs
/-- **Restricting the marks moves the compensated integral by at most the energy error.** -/
theorem lintegral_integral_sub_restrictMarks_le (N : PoissonRandomMeasure P ν)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)
    (G : MarkStep Ω E ν g) (hG : G.Adapted ℱ) (hA : MeasurableSet A)
    {φ : Ω → ℝ → E → ℝ} (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω - (G.restrictMarks hA).integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  rw [MarkStep.lintegral_integral_sub_sq_at N hℱ G (G.restrictMarks hA) hG
    (G.restrictMarks_adapted hA hG) ht]
  refine lintegral_mono fun ω => lintegral_mono fun e => lintegral_mono fun s => ?_
  refine pow_le_pow_left' (ENNReal.coe_le_coe.mpr ?_) 2
  by_cases he : e ∈ A
  · rw [G.eval_restrictMarks_of_mem hA s he ω, sub_self]
    simp
  · rw [G.eval_restrictMarks_of_notMem hA s he ω, sub_zero, hsupp ω s e he, zero_sub,
      nnnorm_neg]
end RestrictMarks

end MarkStep

end LevyStochCalc.Poisson.Compensated


