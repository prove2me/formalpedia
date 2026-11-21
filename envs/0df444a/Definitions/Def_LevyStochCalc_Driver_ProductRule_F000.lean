-- Prove2me | Definitions.Def_LevyStochCalc_Driver_ProductRule_F000
-- name    : LevyStochCalc_Driver_ProductRule_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:30.918907+00:00
-- url     : https://prove2.me/theorems/b357fbd7-8ddd-4085-8cf8-20cb2c16988a
-- title:
--   Source declarations: LevyStochCalc.Driver.ProductRule
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.ProductRule. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F001
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F001
import Definitions.Def_SourceProof_730af81efd0792a1160b2da3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The product rule for a continuous Itô process and a pure-jump process

For a continuous version `X` of an Itô process and a bounded adapted process `Y` whose paths are
the sums of finitely many jumps, at the atoms of a Poisson random measure on a window of finite
intensity, the product satisfies

  `X_t Y_t − X_0 Y_0 = ∫_0^t Y_{s−} dX_s + Σ_{atoms (τ, e), τ ≤ t} X_τ ΔY_(τ, e)`

with no covariation term: on the dyadic grids of `[0, t]` the telescoping identity
`Σ Y_{t_k} (X_{t_{k+1}} − X_{t_k}) + Σ X_{t_{k+1}} (Y_{t_{k+1}} − Y_{t_k})` is exact, the first sum
is the Itô integral of the frozen process (`Brownian/LeftFreeze.lean`) plus a Riemann sum of the
drift, and the second converges pathwise to the jump sum (`Analysis/FiniteJumpSum.lean`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Driver

open LevyStochCalc.Analysis LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

section Core

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t)

omit [MeasurableSpace Ω] in
/-- The telescoping identity over the dyadic grid. -/
theorem telescope_dyadic (X : ℝ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    X t ω * Y t ω - X 0 ω * Y 0 ω
      = (∑ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
          * (X (dyadicPartition t n k.succ) ω - X (dyadicPartition t n k.castSucc) ω))
        + ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ) ω
          * (Y (dyadicPartition t n k.succ) ω - Y (dyadicPartition t n k.castSucc) ω) := by
  rw [← Finset.sum_add_distrib]
  have hpt : ∀ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
        * (X (dyadicPartition t n k.succ) ω - X (dyadicPartition t n k.castSucc) ω)
      + X (dyadicPartition t n k.succ) ω
        * (Y (dyadicPartition t n k.succ) ω - Y (dyadicPartition t n k.castSucc) ω)
      = X (dyadicPartition t n k.succ) ω * Y (dyadicPartition t n k.succ) ω
        - X (dyadicPartition t n k.castSucc) ω * Y (dyadicPartition t n k.castSucc) ω :=
    fun k => by ring
  simp_rw [hpt]
  set f : ℕ → ℝ := fun j => X (((j : ℕ) : ℝ) * t / 2 ^ n) ω * Y (((j : ℕ) : ℝ) * t / 2 ^ n) ω
    with hf
  have hsum : (∑ k : Fin (2 ^ n), (X (dyadicPartition t n k.succ) ω
        * Y (dyadicPartition t n k.succ) ω
        - X (dyadicPartition t n k.castSucc) ω * Y (dyadicPartition t n k.castSucc) ω))
      = ∑ k ∈ Finset.range (2 ^ n), (f (k + 1) - f k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => f (k + 1) - f k) (2 ^ n)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf, dyadicPartition, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  rw [hsum, Finset.sum_range_sub]
  simp only [hf, Nat.cast_zero, zero_mul, zero_div, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm ((2 : ℝ) ^ n) t, mul_div_assoc, div_self (by positivity), mul_one]
/-- The Riemann sum of the drift over the grid is the integral of the frozen process against
the drift. -/
theorem sum_mul_setIntegral_eq_integral_leftFreeze (ω : Ω) {b : ℝ → ℝ} (hbm : Measurable b)
    {B : ℝ} (hB : ∀ s, |b s| ≤ B) (n : ℕ) :
    (∑ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
        * ∫ s in Set.Ioc (dyadicPartition t n k.castSucc) (dyadicPartition t n k.succ), b s)
      = ∫ s in Set.Ioc (0 : ℝ) t, (leftFreeze Y hYb hYm ht n).eval s ω * b s := by
  have hbint : IntegrableOn b (Set.Ioc (0 : ℝ) t) volume := by
    refine Integrable.mono' (integrable_const B) hbm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs]; exact hB s
  have heval : ∀ s, (leftFreeze Y hYb hYm ht n).eval s ω * b s
      = ∑ k : Fin (2 ^ n), (Set.Ioc (dyadicPartition t n k.castSucc)
          (dyadicPartition t n k.succ)).indicator (fun s => Y (dyadicPartition t n k.castSucc) ω
            * b s) s := by
    intro s
    rw [eval_eq_sum_indicator, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [leftFreeze]
    rw [← Set.indicator_mul_left]
  simp_rw [heval]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hsub : Set.Ioc (dyadicPartition t n k.castSucc) (dyadicPartition t n k.succ)
        ⊆ Set.Ioc (0 : ℝ) t := by
      have h0 : 0 ≤ dyadicPartition t n k.castSucc := by
        rw [← dyadicPartition_zero t n]
        exact (dyadicPartition_strictMono ht n).monotone (Fin.zero_le _)
      exact Set.Ioc_subset_Ioc h0 (dyadicPartition_le ht n _)
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr hsub, integral_const_mul]
  · intro k _
    exact (hbint.const_mul (Y (dyadicPartition t n k.castSucc) ω)).indicator measurableSet_Ioc
omit [MeasurableSpace E] in
/-- The frozen drift integrals converge to the integral of the left limits against the
drift. -/
theorem tendsto_integral_leftFreeze_mul (ω : Ω) {b : ℝ → ℝ} (hbm : Measurable b) {B : ℝ}
    (hB : ∀ s, |b s| ≤ B) {S : Finset (ℝ × E)} {c : ℝ × E → ℝ}
    (hY : ∀ s, Y s ω = Y 0 ω + jumpSum S c s) {Yminus : ℝ → Ω → ℝ}
    (hYminus : ∀ s, Yminus s ω = Y 0 ω + jumpSumStrict S c s) :
    Tendsto (fun n : ℕ => ∫ s in Set.Ioc (0 : ℝ) t, (leftFreeze Y hYb hYm ht n).eval s ω * b s)
      atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * b s)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hYb 0 ω)
  refine tendsto_integral_of_dominated_convergence (fun _ => C * B) ?_ (integrable_const _) ?_ ?_
  · intro n
    exact (((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval.comp
      (measurable_prodMk_left (x := ω))).mul hbm).aestronglyMeasurable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_leftFreeze_eval_le Y hYb hYm ht n hs.1 hs.2 ω) (hB s) (abs_nonneg _)
      hC0
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    refine Tendsto.mul_const (b s) ?_
    have hev := _root_.Prove2MeSourceProof.h_730af81efd0792a1160b2da3 S c ht hs.1
    refine (tendsto_const_nhds (x := Yminus s ω)).congr' ?_
    filter_upwards [hev] with n hn
    rw [_root_.Prove2MeSourceProof.h_80616d8197bf2b1beeb50920 Y hYb hYm ht n hs.1 hs.2, hY, hn, ← hYminus]
omit [MeasurableSpace E] in
/-- **The pathwise core of the product rule.** At a sample point where the increments of `X` over
the grid cells split into the drift integrals and the increments of `I`, where `Y` and its left
limits are the jump sums of finitely many weighted points, and where the frozen elementary
integrals converge along a subsequence to `L`, the product identity holds with `L` as the
stochastic term. -/
theorem product_rule_core (ω : Ω) {X : ℝ → Ω → ℝ} (hXc : Continuous fun s => X s ω)
    {b : ℝ → ℝ} (hbm : Measurable b) {B : ℝ} (hB : ∀ s, |b s| ≤ B) {I : ℝ → Ω → ℝ}
    (hinc : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      X (dyadicPartition t n k.succ) ω - X (dyadicPartition t n k.castSucc) ω
        = (∫ s in Set.Ioc (dyadicPartition t n k.castSucc) (dyadicPartition t n k.succ), b s)
          + (I (dyadicPartition t n k.succ) ω - I (dyadicPartition t n k.castSucc) ω))
    {S : Finset (ℝ × E)} {c : ℝ × E → ℝ} (hY : ∀ s, Y s ω = Y 0 ω + jumpSum S c s)
    {Yminus : ℝ → Ω → ℝ} (hYminus : ∀ s, Yminus s ω = Y 0 ω + jumpSumStrict S c s)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {L : ℝ}
    (hL : Tendsto (fun j => (leftFreeze Y hYb hYm ht (φ j)).integralAgainst I t ω) atTop
      (𝓝 L)) :
    X t ω * Y t ω - X 0 ω * Y 0 ω
      = L + (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * b s)
        + ∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ t then X p.1 ω * c p else 0 := by
  classical
  -- the elementary integral for each level
  have hJ : ∀ n : ℕ, (leftFreeze Y hYb hYm ht n).integralAgainst I t ω
      = (X t ω * Y t ω - X 0 ω * Y 0 ω)
        - (∫ s in Set.Ioc (0 : ℝ) t, (leftFreeze Y hYb hYm ht n).eval s ω * b s)
        - ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ) ω
          * (jumpSum S c (dyadicPartition t n k.succ)
            - jumpSum S c (dyadicPartition t n k.castSucc)) := by
    intro n
    have htel := telescope_dyadic Y (t := t) X ω n
    have hA : (∑ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
          * (X (dyadicPartition t n k.succ) ω - X (dyadicPartition t n k.castSucc) ω))
        = (∑ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
            * ∫ s in Set.Ioc (dyadicPartition t n k.castSucc) (dyadicPartition t n k.succ), b s)
          + (leftFreeze Y hYb hYm ht n).integralAgainst I t ω := by
      rw [leftFreeze_integralAgainst, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hinc n k]
      ring
    have hB' : (∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ) ω
          * (Y (dyadicPartition t n k.succ) ω - Y (dyadicPartition t n k.castSucc) ω))
        = ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ) ω
          * (jumpSum S c (dyadicPartition t n k.succ)
            - jumpSum S c (dyadicPartition t n k.castSucc)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hY (dyadicPartition t n k.succ), hY (dyadicPartition t n k.castSucc)]
      ring
    rw [hA, hB', sum_mul_setIntegral_eq_integral_leftFreeze Y hYb hYm ht ω hbm hB n] at htel
    linarith
  have hDlim := tendsto_integral_leftFreeze_mul Y hYb hYm ht ω hbm hB hY hYminus
  have hBlim := tendsto_sum_mul_jumpSum_sub S c hXc ht
  have hlim2 : Tendsto (fun j => (leftFreeze Y hYb hYm ht (φ j)).integralAgainst I t ω) atTop
      (𝓝 ((X t ω * Y t ω - X 0 ω * Y 0 ω)
        - (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * b s)
        - ∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ t then X p.1 ω * c p else 0)) := by
    simp_rw [hJ]
    exact ((tendsto_const_nhds.sub (hDlim.comp hφ.tendsto_atTop)).sub
      (hBlim.comp hφ.tendsto_atTop))
  have := tendsto_nhds_unique hL hlim2
  linarith
end Core

section Wrapper

variable [MeasurableSingletonClass E] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] (N : Poisson.PoissonRandomMeasure P ν)

omit [MeasurableSpace.CountablyGenerated E] in
/-- On a window carrying finitely many atoms, the integral over the times in `(0, s]` is the
jump sum of the masses times the values. -/
theorem setIntegral_Ioc_eq_jumpSum {R : Set (ℝ × E)} {ω : Ω} {S : Finset (ℝ × E)}
    [IsFiniteMeasure ((N.N ω).restrict R)]
    (hS : (N.N ω).restrict R = ∑ p ∈ S, ((N.N ω).restrict R) {p} • Measure.dirac p)
    (g : ℝ × E → ℝ) (s : ℝ) :
    ∫ p in R ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ, g p ∂(N.N ω)
      = jumpSum S (fun p => (((N.N ω).restrict R) {p}).toReal * g p) s := by
  rw [Set.inter_comm, ← Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ)]
  exact setIntegral_Ioc_of_eq_sum_dirac hS g s
omit [MeasurableSpace.CountablyGenerated E] in
/-- The strict-past version. -/
theorem setIntegral_Ioo_eq_jumpSumStrict {R : Set (ℝ × E)} {ω : Ω} {S : Finset (ℝ × E)}
    [IsFiniteMeasure ((N.N ω).restrict R)]
    (hS : (N.N ω).restrict R = ∑ p ∈ S, ((N.N ω).restrict R) {p} • Measure.dirac p)
    (g : ℝ × E → ℝ) (s : ℝ) :
    ∫ p in R ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ, g p ∂(N.N ω)
      = jumpSumStrict S (fun p => (((N.N ω).restrict R) {p}).toReal * g p) s := by
  rw [Set.inter_comm, ← Measure.restrict_restrict (measurableSet_Ioo.prod MeasurableSet.univ)]
  exact setIntegral_Ioo_of_eq_sum_dirac hS g s
omit [MeasurableSingletonClass E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Convergence of the squared `L²` distances to zero is convergence of the `L²` seminorms. -/
theorem tendsto_eLpNorm_two_of_tendsto_lintegral_sq {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : Tendsto (fun n => ∫⁻ ω, (‖f n ω - g ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 2 P) atTop (𝓝 0) := by
  have h2 : ∀ n, eLpNorm (f n - g) 2 P
      = (∫⁻ ω, (‖f n ω - g ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply, enorm_eq_nnnorm]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.rpow_two]
  simp_rw [h2]
  have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  exact this
variable (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
  (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Wrapper

end LevyStochCalc.Driver


