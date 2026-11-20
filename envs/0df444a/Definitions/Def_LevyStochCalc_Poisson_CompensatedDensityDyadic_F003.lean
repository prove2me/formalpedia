-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F003
-- name    : LevyStochCalc_Poisson_CompensatedDensityDyadic_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:59:19.023265+00:00
-- url     : https://prove2.me/theorems/3c55ed18-070b-494a-a68f-b8ad7f83ed36
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityDyadic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityDyadic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F002
import Definitions.Def_SourceProof_41999f352e28c058ae5e27f5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic time-discretisation of a mark-dependent integrand

The dyadic partition `tᵢ = i·T/2ⁿ` of `[0,T]`, the interval time-averages of a bounded
integrand `φ : Ω → ℝ → E → ℝ` with the mark carried as a parameter, and the piecewise-constant
evaluation `dyadicEval` built from them. For a bounded jointly measurable `φ`, the Lebesgue
density theorem gives almost-everywhere convergence of `dyadicEval` to `φ` in the time variable,
and dominated convergence upgrades it to convergence in `L²(P ⊗ ds ⊗ ν)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `dyadicEval` inherits the bound `M`: at most one partition indicator fires, and each
dyadic average is bounded by `M`. -/
lemma dyadicEval_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) :
    |dyadicEval T φ n s ω e| ≤ M := by
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM ω 0 e)
  unfold dyadicEval
  by_cases h : ∃ i : Fin (2 ^ n),
      dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
  · obtain ⟨i₀, hi₀⟩ := h
    have huniq : ∀ j : Fin (2 ^ n), j ≠ i₀ →
        ¬(dyadicPartition T n j.castSucc < s ∧ s ≤ dyadicPartition T n j.succ) := by
      intro j hj ⟨hj1, hj2⟩
      rcases lt_trichotomy i₀ j with hlt | heq | hgt
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hi₀.2]
      · exact hj heq.symm
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.1]
    rw [Finset.sum_eq_single i₀ (fun j _ hj => if_neg (huniq j hj))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hi₀]
    exact dyadicAvg_bounded hT φ hM n i₀ ω e
  · rw [not_exists] at h
    rw [Finset.sum_eq_zero (fun i _ => if_neg (h i)), abs_zero]; exact hM_nn
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `s ↦ dyadicEval T φ n s ω e` is measurable (finite sum of interval-indicators
times constants). -/
lemma dyadicEval_measurable_in_time {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (ω : Ω) (e : E) :
    Measurable (fun s => dyadicEval T φ n s ω e) := by
  unfold dyadicEval
  exact Finset.measurable_sum _ (fun i _ =>
    Measurable.ite measurableSet_Ioc measurable_const measurable_const)
/-- **Per-`(ω,e)` `L²` time convergence:** for fixed `(ω, e)`, the time-`L²` error of
the dyadic eval tends to `0`. Dominated convergence on the finite interval `[0,T]`
(bound `(2M)²`, a.e. pointwise convergence from `dyadicEval_ae_tendsto_per_param`). -/
lemma dyadicEval_inner_L2_tendsto
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    Filter.Tendsto
      (fun n => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM ω 0 e)
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have hsq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => ENNReal.ofReal ((2 * M) ^ 2)) ?_ ?_ ?_ ?_
  · intro n
    exact ((ENNReal.continuous_coe.measurable.comp
      (h_meas_slice.sub (dyadicEval_measurable_in_time φ n ω e)).nnnorm).pow_const 2).aemeasurable
  · intro n
    refine Filter.Eventually.of_forall (fun s => ?_)
    simp only []
    rw [hsq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ‖φ ω s e - dyadicEval T φ n s ω e‖ ≤ 2 * M := by
      rw [Real.norm_eq_abs]
      calc |φ ω s e - dyadicEval T φ n s ω e|
          ≤ |φ ω s e| + |dyadicEval T φ n s ω e| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM ω s e) (dyadicEval_bounded hT φ hM n s ω e)
        _ = 2 * M := by ring
    nlinarith [norm_nonneg (φ ω s e - dyadicEval T φ n s ω e), hb, hM_nn]
  · rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  · filter_upwards [_root_.Prove2MeSourceProof.h_41999f352e28c058ae5e27f5 hT φ h_meas hM ω e] with s hs
    have hdiff : Filter.Tendsto (fun n => φ ω s e - dyadicEval T φ n s ω e)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := φ ω s e)).sub hs
    have hg : Continuous (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)
    simpa [Function.comp_def] using (hg.tendsto 0).comp hdiff
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- If `φ(ω, ·, e)` vanishes identically in time, so does its dyadic eval. -/
lemma dyadicEval_eq_zero {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E)
    (h0 : ∀ u, φ ω u e = 0) : dyadicEval T φ n s ω e = 0 := by
  unfold dyadicEval
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have havg : dyadicAvg T φ n i ω e = 0 := by unfold dyadicAvg; simp [h0]
  split_ifs with h
  · exact havg
  · rfl
/-- Joint `(s, e)`-measurability of `dyadicEval` (with `ω` fixed). -/
lemma dyadicEval_measurable_prod
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) (ω : Ω) :
    Measurable (fun q : ℝ × E => dyadicEval T φ n q.1 ω q.2) := by
  unfold dyadicEval
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite (measurable_fst measurableSet_Ioc) ?_ measurable_const
  exact (dyadicAvg_measurable T φ h_meas n i).comp
    (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.2) : Ω × E))
/-- Joint `(ω, s, e)`-measurability of `dyadicEval`. -/
lemma dyadicEval_measurable_triple
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Ω × ℝ × E => dyadicEval T φ n p.2.1 p.1 p.2.2) := by
  unfold dyadicEval
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ((measurable_fst.comp measurable_snd) measurableSet_Ioc) ?_
    measurable_const
  exact (dyadicAvg_measurable T φ h_meas n i).comp
    (by fun_prop : Measurable fun p : Ω × ℝ × E => ((p.1, p.2.2) : Ω × E))
end LevyStochCalc.Poisson.Compensated


