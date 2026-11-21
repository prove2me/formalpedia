-- Prove2me | Definitions.Def_SourceProof_c795c860ec71dd220bc36203
-- name    : SourceProof_c795c860ec71dd220bc36203
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:35:35.792902+00:00
-- url     : https://prove2.me/theorems/f28dbebe-e3d9-46eb-929b-57abe4be6c69
-- title:
--   LevyStochCalc source module: SourceProof_c795c860ec71dd220bc36203
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.triple_ofReal_integral_eq_lintegral` comes from the `LevyStochCalc.Poisson.CompensatedDensityLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_c795c860ec71dd220bc36203
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (h : Ω → ℝ → E → ℝ) (hmeas : Measurable (fun p : Ω × ℝ × E => h p.1 p.2.1 p.2.2))
    {C : ℝ} (hC : ∀ ω s e, |h ω s e| ≤ C) {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ S → h ω s e = 0) :
    ENNReal.ofReal (∫ ω, ∫ e, ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume ∂ν ∂P)
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖h ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set vT : ℝ := (volume (Set.Icc (0 : ℝ) T)).toReal with hvT
  have hvT0 : 0 ≤ vT := ENNReal.toReal_nonneg
  -- innermost `s`-integrand measurability and integrability.
  have hsm : ∀ ω e, Measurable (fun s => (h ω s e) ^ 2) := fun ω e =>
    ((hmeas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))).pow_const 2)
  have hsint : ∀ ω e, MeasureTheory.Integrable (fun s => (h ω s e) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := fun ω e =>
    MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (C ^ 2))
      (hsm ω e).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hC ω s e, abs_nonneg (h ω s e), sq_abs (h ω s e)]))
  set g1 : Ω → E → ℝ := fun ω e => ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume with hg1
  have hg1_nonneg : ∀ ω e, 0 ≤ g1 ω e := fun ω e =>
    MeasureTheory.integral_nonneg (fun s => sq_nonneg _)
  have hg1_supp : ∀ ω e, e ∉ S → g1 ω e = 0 := fun ω e he => by
    change ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume = 0
    have hz : ∀ s, (h ω s e) ^ 2 = 0 := fun s => by rw [hsupp ω s e he]; ring
    simp only [hz, integral_zero]
  have hg1_bound : ∀ ω e, g1 ω e ≤ C ^ 2 * vT := fun ω e => by
    calc g1 ω e ≤ ∫ _s in Set.Icc (0 : ℝ) T, C ^ 2 ∂volume :=
          MeasureTheory.setIntegral_mono_on (hsint ω e)
            (MeasureTheory.integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc
            (fun s _ => by nlinarith [hC ω s e, abs_nonneg (h ω s e), sq_abs (h ω s e)])
      _ = C ^ 2 * vT := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm, hvT,
              MeasureTheory.measureReal_def]
  -- joint measurability of `g1` and its `ν`-integral.
  have hg1m : Measurable (fun q : Ω × E => g1 q.1 q.2) := by
    have hr : Measurable (fun p : (Ω × E) × ℝ => (h p.1.1 p.2 p.1.2) ^ 2) :=
      ((hmeas.comp (by fun_prop : Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2)
        : Ω × ℝ × E))).pow_const 2)
    exact (hr.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))).measurable
  have hdom_e : MeasureTheory.Integrable (S.indicator (fun _ => C ^ 2 * vT)) ν :=
    (MeasureTheory.integrable_indicator_iff hS).mpr (MeasureTheory.integrableOn_const hSfin)
  have heint : ∀ ω, MeasureTheory.Integrable (fun e => g1 ω e) ν := fun ω =>
    MeasureTheory.Integrable.mono' hdom_e
      (hg1m.comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e => by
        by_cases he : e ∈ S
        · rw [Set.indicator_of_mem he, Real.norm_eq_abs, abs_of_nonneg (hg1_nonneg ω e)]
          exact hg1_bound ω e
        · rw [Set.indicator_of_notMem he, hg1_supp ω e he, norm_zero]))
  set g2 : Ω → ℝ := fun ω => ∫ e, g1 ω e ∂ν with hg2
  have hg2_nonneg : ∀ ω, 0 ≤ g2 ω := fun ω =>
    MeasureTheory.integral_nonneg (fun e => hg1_nonneg ω e)
  have hg2m : Measurable g2 :=
    (hg1m.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have homega : MeasureTheory.Integrable g2 P :=
    MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const ((C ^ 2 * vT) * (ν S).toReal)) hg2m.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg2_nonneg ω)]
        calc g2 ω = ∫ e, g1 ω e ∂ν := rfl
          _ ≤ ∫ e, S.indicator (fun _ => C ^ 2 * vT) e ∂ν :=
              MeasureTheory.integral_mono (heint ω) hdom_e (fun e => by
                by_cases he : e ∈ S
                · rw [Set.indicator_of_mem he]; exact hg1_bound ω e
                · rw [Set.indicator_of_notMem he, hg1_supp ω e he])
          _ = (C ^ 2 * vT) * (ν S).toReal := by
              rw [MeasureTheory.integral_indicator hS, MeasureTheory.setIntegral_const,
                smul_eq_mul, mul_comm, MeasureTheory.measureReal_def]))
  -- nested `ofReal` ↦ `∫⁻`.
  rw [show (∫ ω, ∫ e, ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume ∂ν ∂P) = ∫ ω, g2 ω ∂P
      from rfl,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal homega
      (Filter.Eventually.of_forall hg2_nonneg)]
  refine lintegral_congr (fun ω => ?_)
  rw [hg2, MeasureTheory.ofReal_integral_eq_lintegral_ofReal (heint ω)
    (Filter.Eventually.of_forall (fun e => hg1_nonneg ω e))]
  refine lintegral_congr (fun e => ?_)
  rw [hg1, MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsint ω e)
    (Filter.Eventually.of_forall (fun s => sq_nonneg _))]
  refine lintegral_congr (fun s => ?_)
  rw [show ((h ω s e) ^ 2) = ‖h ω s e‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs],
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
/-! ### Path regularity bricks (toward the càdlàg conjunct of #6)

The compensated step integral is càdlàg in `t`: the compensator part is continuous,
and the count part is a Stieltjes function of `t` (monotone, right-continuous with
left limits via measure continuity). These bricks give the right-continuity and
left-limit existence of monotone `ℝ≥0∞`-valued functions, the substrate for the
Doob `L²` càdlàg modification. -/

end LevyStochCalc.Poisson.Compensated


