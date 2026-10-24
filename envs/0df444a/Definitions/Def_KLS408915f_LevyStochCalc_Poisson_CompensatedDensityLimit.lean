-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
-- name    : KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:18:20.817002+00:00
-- url     : https://prove2.me/theorems/621edad5-0853-443f-af01-c158e8ad7e74
-- title:
--   Integral bridges between real and `ENNReal` $L^2$ expressions
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`). `lintegral_sq_eq_ofReal_integral` converts the `ENNReal` integral of squared nonnegative norms of an `L^2(P)` real function into `ENNReal.ofReal` of its real squared integral. Under joint measurability, a uniform bound, measurable finite mark support, and vanishing outside that support, `triple_ofReal_integral_eq_lintegral` converts `ENNReal.ofReal` of the nested real integral over $P$, $\nu$, and $[0,T]$ into the corresponding nested `ENNReal` integrals.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedDensityLimit.lean#L76-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedDensityLimit`, definition bundle `KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedDensityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²(P)`. -/
lemma lintegral_sq_eq_ofReal_integral {P : Measure Ω} {g : Ω → ℝ}
    (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm _).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
/-- **Real↔`ℝ≥0∞` triple-integral bridge.** For a bounded `φ`-difference-style function
`h` supported on marks in a finite-measure set `S`,
`ofReal (∫ω∫e∫_{[0,T]} h²) = ∫⁻ω∫⁻e∫⁻_{[0,T]} ‖h‖²`. (Nested
`ofReal_integral_eq_lintegral_ofReal`; integrability at each level from the bound and
the finite mark support.) -/
lemma triple_ofReal_integral_eq_lintegral
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
end Compensated
end Poisson
end LevyStochCalc


