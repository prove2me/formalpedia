-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityPredictableL2
-- name    : KLSModular_LevyStochCalc_Brownian_ItoDensityPredictableL2
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:58:06.563028+00:00
-- url     : https://prove2.me/theorems/36feb9b9-02b5-4c75-821f-6ecf3c0909c9
-- title:
--   L² convergence and adapted density for bounded predictable Brownian approximations
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a probability measure $P$ on $\Omega$, bounded jointly measurable $g$, and $T>0$, `predictableDyadicSimple_brownian_L2_converges` gives convergence to zero of the iterated $\operatorname{ENNReal}$ squared error integral over $P$ and volume on $[0,T]$. The bundle also proves a.e. convergence on $\Omega\times[0,T]$, measurability of the convergence set, and `SimplePredictable.eval_jointly_measurable`. With progressive measurability relative to a filtration, `adaptedSimple_dense_L2_bounded_brownian` produces adapted `SimplePredictable` approximants whose coefficients are strongly measurable at their partition times and whose same $L^2$ error tends to zero.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoDensityPointwise
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   private lemma predictable_convergence_set_measurable
--       {T : ℝ} (hT : 0 < T)
--       (g : Ω → ℝ → ℝ)
--       (h_meas : Measurable (Function.uncurry g))
--       (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
--       MeasurableSet
--         {p : Ω × ℝ | Filter.Tendsto
--           (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
--           Filter.atTop (nhds (g p.1 p.2))}
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoDensityPointwise`](https://prove2.me/theorems/a6789458-c313-4564-9fce-c87a1818fed2).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoDensityPredictableL2.lean) · `LevyStochCalc.Brownian.ItoDensityPredictableL2` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoDensityPredictableL2.lean#L27-L350 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoDensityPredictableL2`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoDensityPredictableL2`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityPointwise

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoDensityPredictableL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Joint measurability of the predictable convergence set.** -/
 lemma predictable_convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas
/-- **a.e. convergence on the product (predictable case).** -/
 lemma predictableDyadicSimple_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (LevyStochCalc.Brownian.Ito.predictable_convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact predictable_pointwise_tendsto_per_omega hT g h_meas M h_bound ω
/-- **L² convergence of predictable shifted dyadic to g.** Mirror of
`dyadicSimplePredictable_brownian_L2_converges`, but with `M` replaced by
`max M 0` for the eval bound, and using `predictable_pointwise_tendsto_per_omega`. -/
lemma predictableDyadicSimple_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  haveI h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- Bound: 2(|M|+1) ≥ |g - eval|.
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖
        ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ max M 0 :=
        predictableDyadicSimple_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h_max_le : max M 0 ≤ |M| + 1 := by
        by_cases hM : M ≤ 0
        · rw [max_eq_right hM]
          have : (0 : ℝ) ≤ |M| := abs_nonneg _
          linarith
        · push Not at hM
          rw [max_eq_left hM.le]
          linarith [le_abs_self M]
      have h12 : |g p.1 p.2 -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2| +
              |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      norm_nonneg _
    change (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub
        h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) :=
      ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
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
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT
/-- **Adapted bounded density (Brownian).** Bounded progressively measurable
functions are L²-approximable by ADAPTED `SimplePredictable`s.

Construction via `predictableDyadicSimple_brownian` (the left-shifted dyadic
average), which is `ℱ_{t_i}`-StronglyMeasurable for progressively measurable `g`. -/
lemma adaptedSimple_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n,
   fun n i => predictableDyadicSimple_brownian_adapted ℱ hT g h_meas M h_bound
     h_progMeas n i,
   predictableDyadicSimple_brownian_L2_converges hT g h_meas M h_bound⟩
/-- **Generic joint measurability of `SimplePredictable.eval`.** For any
`SimplePredictable Ω T`, the function `(p : Ω × ℝ) ↦ H.eval p.2 p.1` is measurable.

Proof: `eval` is a finite sum of indicator-times-coefficient terms, each measurable
since the indicator's set is `{p | partition i.castSucc < p.2 ≤ partition i.succ}`
(measurable in `snd`) and the coefficient is `H.ξ i ∘ fst` (measurable since
`H.ξ_measurable i`). -/
lemma SimplePredictable.eval_jointly_measurable
    {T : ℝ} (H : SimplePredictable Ω T) :
    Measurable (fun (p : Ω × ℝ) => H.eval p.2 p.1) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_snd (measurableSet_Ioi (a := H.partition i.castSucc))
    · exact measurable_snd (measurableSet_Iic (a := H.partition i.succ))
  · exact (H.ξ_measurable i).comp measurable_fst
end Ito
end Brownian
end LevyStochCalc


