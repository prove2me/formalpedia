-- Prove2me | Definitions.Def_SourceProof_9fe041c50928f190f90f5621
-- name    : SourceProof_9fe041c50928f190f90f5621
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:12:14.366971+00:00
-- url     : https://prove2.me/theorems/df3772d3-4d38-4f2c-9f34-de6f08e983f9
-- title:
--   LevyStochCalc source module: SourceProof_9fe041c50928f190f90f5621
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian_L2_converges` comes from the `LevyStochCalc.Brownian.ItoDensityPointwise` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000

open private dyadicSimplePredictable_brownian_ae_tendsto from Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere convergence of the dyadic averages

Lebesgue differentiation for a bounded jointly measurable integrand: the dyadic cell
averages, shifted and unshifted, converge to the integrand at almost every point of
`Ω × [0,T]`, and for the unshifted family the convergence also holds in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.Prove2MeSourceProof.h_9fe041c50928f190f90f5621
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  -- Setup: finite measure on the product.
  haveI h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- The constant bound: 2(|M|+1) ≥ |g - eval| everywhere (using triangle ineq + boundedness).
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  -- Integrand on product space.
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  -- F n p ≤ ENNReal.ofReal (CC²) everywhere.
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| ≤ M :=
        _root_.Prove2MeSourceProof.h_d85ab88de821d59dc1b96591 hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h12 : |g p.1 p.2 -
          (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2|
            + |(LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ := norm_nonneg _
    change (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  -- AEMeasurable of F n on the product.
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.succ))
      · exact (LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  -- Bound is integrable (constant on finite measure space).
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  -- a.e. convergence on the product (consumes sub-lemma A).
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := dyadicSimplePredictable_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    -- F n p = ‖g - eval‖² → 0 since ‖g - eval‖ → 0 (from eval → g).
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    -- Compose: (·)² is continuous on ℝ≥0∞, so tendsto preserves it.
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by
      exact ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
  -- Apply DCT on the product space.
  have h_DCT : Filter.Tendsto
      (fun n => ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
      Filter.atTop (nhds 0) := by
    have h_target : Filter.Tendsto (fun n => ∫⁻ p, F n p
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop
        (nhds (∫⁻ _ : Ω × ℝ, (0 : ℝ≥0∞)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))) := by
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun _ => ENNReal.ofReal (CC ^ 2))
        (fun n => (h_F_meas n).aemeasurable)
        ?_ h_bound_integrable h_F_ae
      intro n
      exact Filter.Eventually.of_forall (fun p => h_F_bound n p)
    simpa using h_target
  -- Convert iterated to product via Fubini.
  -- The iterated form ∫⁻ ω, ∫⁻ s in Icc 0 T, F p_swapped ∂vol ∂P equals
  -- ∫⁻ p, F p ∂(P × vol.restrict (Icc 0 T)).
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT
end LevyStochCalc.Brownian.Ito


