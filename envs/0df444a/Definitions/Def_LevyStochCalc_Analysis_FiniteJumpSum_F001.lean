-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F001
-- name    : LevyStochCalc_Analysis_FiniteJumpSum_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:17:45.523324+00:00
-- url     : https://prove2.me/theorems/55011e81-c81f-4bec-9464-e6c12b366dce
-- title:
--   Source declarations: LevyStochCalc.Analysis.FiniteJumpSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Analysis.FiniteJumpSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F000
import Definitions.Def_SourceProof_68e898bacd09d59b5244b471

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums of finitely many jumps along a dyadic grid

A finite set of points of `ℝ × E` with weights defines a step function of the time,
`jumpSum S c s`, the sum of the weights of the points with time in `(0, s]`, and its strict-past
version `jumpSumStrict S c s`. Along the dyadic grid of `[0, t]` the frozen values
`jumpSum S c (leftPt t n s)` are eventually the strict-past value, and the sums of the increments
over the cells weighted by a continuous function at the right endpoints converge to the sum of
the weights times the function at the points. A finite sum of Dirac masses integrates a function
over a time window to such a jump sum.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace LevyStochCalc.Analysis

variable {E : Type*}

section Sums

/-- The right endpoint of the cell of the dyadic partition of level `n` containing `s`. -/
noncomputable def rightPt (t : ℝ) (n : ℕ) (s : ℝ) : ℝ := leftPt t n s + t / 2 ^ n
theorem tendsto_rightPt {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => rightPt t n s) atTop (𝓝 s) := by
  have hlim : Tendsto (fun n : ℕ => t / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul t
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  simpa [rightPt] using (_root_.Prove2MeSourceProof.h_68e898bacd09d59b5244b471 ht hs).add hlim
theorem rightPt_eq_dyadicPartition_succ {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hst : s ≤ t) :
    rightPt t n s
      = dyadicPartition t n (Fin.succ ⟨leftIdx t n s, leftIdx_lt ht n hs hst⟩) := by
  rw [dyadicPartition_succ]
  rfl
open scoped Classical in
/-- **The Riemann sum of a continuous function against the jumps.** Weighting the increments of
the jump sum over the cells of the dyadic grid by a function at the right endpoints gives the
sum of the weights times the function at the right endpoints of the cells of the points. -/
theorem sum_mul_jumpSum_sub (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) (X : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) (n : ℕ) :
    ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ)
        * (jumpSum S c (dyadicPartition t n k.succ) - jumpSum S c (dyadicPartition t n k.castSucc))
      = ∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ t then X (rightPt t n p.1) * c p else 0 := by
  have hmono := dyadicPartition_strictMono ht n
  have h0 : ∀ k : Fin (2 ^ n), 0 ≤ dyadicPartition t n k.castSucc := fun k => by
    rw [← dyadicPartition_zero t n]
    exact hmono.monotone (Fin.zero_le _)
  simp_rw [fun k : Fin (2 ^ n) => jumpSum_sub S c (h0 k)
    (hmono (Fin.castSucc_lt_succ (i := k))).le, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : 0 < p.1 ∧ p.1 ≤ t
  · rw [if_pos hp]
    set k : Fin (2 ^ n) := ⟨leftIdx t n p.1, leftIdx_lt ht n hp.1 hp.2⟩ with hk
    have hmem : dyadicPartition t n k.castSucc < p.1 ∧ p.1 ≤ dyadicPartition t n k.succ := by
      refine ⟨leftPt_lt ht n hp.1, ?_⟩
      rw [dyadicPartition_succ]
      exact le_leftPt_add ht n hp.1
    rw [Finset.sum_eq_single k]
    · rw [if_pos hmem, rightPt_eq_dyadicPartition_succ ht n hp.1 hp.2]
    · intro i _ hik
      rw [mul_ite, mul_zero, if_neg]
      rintro ⟨h1, h2⟩
      apply hik
      have hi1 : i.castSucc < k.succ := hmono.lt_iff_lt.mp (h1.trans_le hmem.2)
      have hi2 : k.castSucc < i.succ := hmono.lt_iff_lt.mp (hmem.1.trans_le h2)
      apply Fin.ext
      have e1 : (i : ℕ) < (k : ℕ) + 1 := by simpa [Fin.lt_def] using hi1
      have e2 : (k : ℕ) < (i : ℕ) + 1 := by simpa [Fin.lt_def] using hi2
      omega
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_ite, mul_zero, if_neg]
    rintro ⟨h1, h2⟩
    exact hp ⟨(h0 k).trans_lt h1, h2.trans (dyadicPartition_le ht n _)⟩
open scoped Classical in
/-- The Riemann sums of a continuous function against the jumps converge to the sum of the
weights times the function at the points. -/
theorem tendsto_sum_mul_jumpSum_sub (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {X : ℝ → ℝ}
    (hX : Continuous X) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ)
        * (jumpSum S c (dyadicPartition t n k.succ)
          - jumpSum S c (dyadicPartition t n k.castSucc)))
      atTop (𝓝 (∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ t then X p.1 * c p else 0)) := by
  simp_rw [sum_mul_jumpSum_sub S c X ht]
  refine tendsto_finsetSum _ fun p _ => ?_
  by_cases hp : 0 < p.1 ∧ p.1 ≤ t
  · simp only [if_pos hp]
    exact ((hX.tendsto _).comp (tendsto_rightPt ht hp.1)).mul_const _
  · simp only [if_neg hp]
    exact tendsto_const_nhds
end Sums

section Dirac

variable [MeasurableSpace E] [MeasurableSingletonClass E]

open scoped Classical in
/-- A finite sum of Dirac masses integrates a function over a time window to the jump sum of
the masses times the values. -/
theorem setIntegral_Ioc_of_eq_sum_dirac {μ : Measure (ℝ × E)} [IsFiniteMeasure μ]
    {S : Finset (ℝ × E)} (hμ : μ = ∑ p ∈ S, μ {p} • Measure.dirac p) (g : ℝ × E → ℝ)
    (s : ℝ) :
    ∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.univ, g p ∂μ
      = jumpSum S (fun p => (μ {p}).toReal * g p) s := by
  rw [← integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  unfold jumpSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  by_cases hp : 0 < p.1 ∧ p.1 ≤ s
  · rw [if_pos hp, Set.indicator_of_mem (by simpa using hp)]
  · rw [if_neg hp, Set.indicator_of_notMem (by simpa using hp), mul_zero]
open scoped Classical in
/-- The strict-past version. -/
theorem setIntegral_Ioo_of_eq_sum_dirac {μ : Measure (ℝ × E)} [IsFiniteMeasure μ]
    {S : Finset (ℝ × E)} (hμ : μ = ∑ p ∈ S, μ {p} • Measure.dirac p) (g : ℝ × E → ℝ)
    (s : ℝ) :
    ∫ p in Set.Ioo (0 : ℝ) s ×ˢ Set.univ, g p ∂μ
      = jumpSumStrict S (fun p => (μ {p}).toReal * g p) s := by
  rw [← integral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  unfold jumpSumStrict
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  by_cases hp : 0 < p.1 ∧ p.1 < s
  · rw [if_pos hp, Set.indicator_of_mem (by simpa using hp)]
  · rw [if_neg hp, Set.indicator_of_notMem (by simpa using hp), mul_zero]
end Dirac

end LevyStochCalc.Analysis


