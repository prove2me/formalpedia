-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepPolarised_F000
-- name    : LevyStochCalc_Poisson_MarkStepPolarised_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:28:52.663004+00:00
-- url     : https://prove2.me/theorems/426b0b9d-7543-431f-b324-22d22f20d565
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepPolarised
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepPolarised. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear form of the `L²` isometry for mark-step integrands

For two adapted mark-step integrands `G, G'` on a common time grid, the expectation of the
product of their compensated integrals up to a time `t ≥ 0` is the expectation of the time-mark
integral of the product of the integrands,
`E[(∫_0^t ∫_E G dÑ)(∫_0^t ∫_E G' dÑ)] = E[∫_E ∫_0^t G(s, e) G'(s, e) ds ν(de)]`, and the same
identity holds for the integrals over the whole horizon. It comes from the isometry for a
difference applied to the pairs `G, G'` and `G, G'.neg`, together with the polarisation identity
`4 a a' = (a + a') ^ 2 - (a - a') ^ 2`. Splitting the nested integral of that identity into its
two halves uses the boundedness of a mark-step integrand and the finite intensity of its mark
sets.

## Main statements

* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` — the bilinear identity up to a
  time `t ≥ 0`.
* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_full_mul` — the bilinear identity for the
  integrals over the whole horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Polarisation

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- Integrability at each of the three levels of the nested integral
`∫_Ω ∫_E ∫_{[0, T]}`, for a jointly measurable function bounded by `C` and vanishing for marks
outside a set `S` of finite `ν`-measure. -/
private lemma triple_integrable {T : ℝ} (h : Ω → ℝ → E → ℝ)
    (hmeas : Measurable fun q : Ω × ℝ × E => h q.1 q.2.1 q.2.2)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω s e, |h ω s e| ≤ C)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ S → h ω s e = 0) :
    (∀ ω e, Integrable (fun s => h ω s e) (volume.restrict (Set.Icc (0 : ℝ) T)))
      ∧ (∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume) ν)
      ∧ Integrable (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume ∂ν) P := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hsm : ∀ ω e, Measurable fun s => h ω s e := fun ω e =>
    hmeas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h1 : ∀ ω e, Integrable (fun s => h ω s e) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun ω e => Integrable.mono' (integrable_const C) (hsm ω e).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hC ω s e)
  obtain ⟨D, hD0, hDb⟩ : ∃ D : ℝ, 0 ≤ D
      ∧ ∀ ω e, ‖∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume‖ ≤ D := by
    refine ⟨C * (volume.restrict (Set.Icc (0 : ℝ) T)).real Set.univ,
      mul_nonneg hC0 measureReal_nonneg, fun ω e => ?_⟩
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hC ω s e)
  have hDs : ∀ ω e, e ∉ S → (∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume) = 0 := by
    intro ω e he
    have hz : ∀ s, h ω s e = 0 := fun s => hsupp ω s e he
    simp only [hz, integral_zero]
  have hDm : Measurable fun q : Ω × E => ∫ s in Set.Icc (0 : ℝ) T, h q.1 s q.2 ∂volume := by
    have hr : Measurable fun p : (Ω × E) × ℝ => h p.1.1 p.2 p.1.2 :=
      hmeas.comp (by fun_prop : Measurable fun p : (Ω × E) × ℝ =>
        ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
    exact (hr.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))).measurable
  have hdom : Integrable (S.indicator fun _ => D) ν :=
    (integrable_indicator_iff hS).2 (integrableOn_const hSfin)
  have hpt : ∀ ω e, ‖∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume‖
      ≤ S.indicator (fun _ => D) e := by
    intro ω e
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he]
      exact hDb ω e
    · rw [Set.indicator_of_notMem he, hDs ω e he, norm_zero]
  have h2 : ∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume) ν :=
    fun ω => Integrable.mono' hdom (hDm.comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall (hpt ω))
  refine ⟨h1, h2, Integrable.mono' (integrable_const (D * (ν S).toReal))
    ((hDm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)⟩
  calc ‖∫ e, ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume ∂ν‖
      ≤ ∫ e, ‖∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ e, S.indicator (fun _ => D) e ∂ν := integral_mono (h2 ω).norm hdom (hpt ω)
    _ = D * (ν S).toReal := by
        rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (hℱ : IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

end Polarisation

end MarkStep

end LevyStochCalc.Poisson.Compensated


