-- Prove2me | solution 1 for ApproxOLO.FullInfo.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:46:51.706876+00:00
-- url     : https://prove2.me/submissions/030562ca-71af-4d54-a32a-4f33d4cb53a0

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

set_option autoImplicit false

namespace ApproxOLO.FullInfo.EuclideanProof

open Matrix
open scoped RealInnerProductSpace

lemma euclNorm_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclNorm x := Real.sqrt_nonneg _

lemma euclNorm_eq_norm {d : ℕ} (x : Vec d) :
    euclNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [euclNorm, dotProduct, Real.norm_eq_abs, pow_two]

lemma dot_eq_inner {d : ℕ} (x y : Vec d) :
    x ⬝ᵥ y = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y) := by
  simp [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

lemma euclNorm_sq {d : ℕ} (x : Vec d) : euclNorm x ^ 2 = x ⬝ᵥ x := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma euclNorm_zero {d : ℕ} : euclNorm (0 : Vec d) = 0 := by simp [euclNorm]

lemma euclNorm_eq_zero {d : ℕ} (x : Vec d) : euclNorm x = 0 ↔ x = 0 := by
  rw [euclNorm_eq_norm, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

lemma euclNorm_sub_comm {d : ℕ} (x y : Vec d) : euclNorm (x - y) = euclNorm (y - x) := by
  simp only [euclNorm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_rev _ _

lemma euclNorm_smul {d : ℕ} (a : ℝ) (x : Vec d) : euclNorm (a • x) = |a| * euclNorm x := by
  simp only [euclNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma euclNorm_neg {d : ℕ} (x : Vec d) : euclNorm (-x) = euclNorm x := by
  simp only [euclNorm_eq_norm, WithLp.toLp_neg, norm_neg]

lemma euclNorm_add_le {d : ℕ} (x y : Vec d) : euclNorm (x + y) ≤ euclNorm x + euclNorm y := by
  simpa only [euclNorm_eq_norm, WithLp.toLp_add] using
    norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma euclNorm_sub_le {d : ℕ} (x y : Vec d) : euclNorm (x - y) ≤ euclNorm x + euclNorm y := by
  simpa only [euclNorm_eq_norm, WithLp.toLp_sub] using
    norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma abs_dot_le_norm_mul {d : ℕ} (x y : Vec d) : |x ⬝ᵥ y| ≤ euclNorm x * euclNorm y := by
  simpa only [euclNorm_eq_norm, dot_eq_inner] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma dot_le_norm_mul {d : ℕ} (x y : Vec d) : x ⬝ᵥ y ≤ euclNorm x * euclNorm y :=
  (le_abs_self _).trans (abs_dot_le_norm_mul x y)

lemma neg_norm_mul_le_dot {d : ℕ} (x y : Vec d) : -(euclNorm x * euclNorm y) ≤ x ⬝ᵥ y :=
  (abs_le.mp (abs_dot_le_norm_mul x y)).1

lemma euclNorm_sub_sq {d : ℕ} (x y : Vec d) :
    euclNorm (x - y) ^ 2 = euclNorm x ^ 2 + euclNorm y ^ 2 - 2 * (x ⬝ᵥ y) := by
  simp only [euclNorm_sq, sub_dotProduct, dotProduct_sub, dotProduct_comm y x]
  ring

lemma euclNorm_step_sq {d : ℕ} (x z w : Vec d) (eps : ℝ) :
    euclNorm (x - eps • w - z) ^ 2 = euclNorm (x - z) ^ 2 +
      eps ^ 2 * euclNorm w ^ 2 - 2 * eps * ((x - z) ⬝ᵥ w) := by
  have heq : x - eps • w - z = (x - z) - eps • w := by abel
  rw [heq, euclNorm_sub_sq]
  simp only [euclNorm_sq, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end ApproxOLO.FullInfo.EuclideanProof

namespace ApproxOLO.FullInfo.GradientProof
open Matrix
open EuclideanProof

lemma telescope (D : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (D t - D (t + 1))) = D 1 - D (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

lemma loss_bound {d : ℕ} (eta : ℝ) (heta : 0 < eta) (T : ℕ) (hT : 1 ≤ T)
    (xs fs : ℕ → Vec d) (x : Vec d)
    (hproj : ∀ t, 1 ≤ t → t < T →
      euclNorm (x - xs (t + 1)) ^ 2 ≤ euclNorm (x - (xs t - eta • fs t)) ^ 2) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
        - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
      ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
        + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 := by
  let D : ℕ → ℝ := fun t => if t ≤ T then euclNorm (xs t - x) ^ 2 else 0
  have hstep (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
      2 * eta * (xs t ⬝ᵥ fs t - x ⬝ᵥ fs t) ≤
        (D t - D (t + 1)) + eta ^ 2 * euclNorm (fs t) ^ 2 := by
    have hnext : D (t + 1) ≤ euclNorm (x - (xs t - eta • fs t)) ^ 2 := by
      by_cases hlt : t < T
      · simpa only [D, if_pos (show t + 1 ≤ T by omega), euclNorm_sub_comm (xs (t + 1)) x]
          using hproj t ht1 hlt
      · have heq : t = T := by omega
        simp only [D, heq, if_neg (show ¬T + 1 ≤ T by omega)]
        exact sq_nonneg _
    rw [euclNorm_sub_comm, euclNorm_step_sq, sub_dotProduct] at hnext
    simp only [D, if_pos htT]
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 T) fun t ht =>
    hstep t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have htel : (∑ t ∈ Finset.Icc 1 T, D t) - (∑ t ∈ Finset.Icc 1 T, D (t + 1)) =
      D 1 - D (T + 1) := by rw [← Finset.sum_sub_distrib, telescope]
  rw [htel] at hsum
  simp only [D, if_pos hT, if_neg (show ¬T + 1 ≤ T by omega), sub_zero] at hsum
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hT0 : (T : ℝ) ≠ 0 := ne_of_gt hTr
  have heta0 : eta ≠ 0 := ne_of_gt heta
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * (T : ℝ) * eta by positivity)).mp
  calc
    (2 * (T : ℝ) * eta) *
        (1 / (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t -
          1 / (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) =
        2 * eta * ((∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t) -
          ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) := by field_simp
    _ ≤ euclNorm (xs 1 - x) ^ 2 + eta ^ 2 *
        ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 := hsum
    _ = (2 * (T : ℝ) * eta) *
        (1 / (2 * (T : ℝ) * eta) * euclNorm (xs 1 - x) ^ 2 +
          eta / (2 * (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) := by
      field_simp

lemma payoff_bound {d : ℕ} (eta : ℝ) (heta : 0 < eta) (T : ℕ) (hT : 1 ≤ T)
    (xs fs : ℕ → Vec d) (x : Vec d)
    (hproj : ∀ t, 1 ≤ t → t < T →
      euclNorm (x - xs (t + 1)) ^ 2 ≤ euclNorm (x - (xs t + eta • fs t)) ^ 2) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
        - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
      ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
        + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 := by
  have h := loss_bound eta heta T hT xs (fun t => -fs t) x (by
    simpa only [smul_neg, sub_neg_eq_add] using hproj)
  simpa only [dotProduct_neg, Finset.sum_neg_distrib, euclNorm_neg, mul_neg,
    neg_sub_neg] using h

end ApproxOLO.FullInfo.GradientProof

open ApproxOLO.FullInfo Matrix

theorem solution {d : ℕ} (S : Set (Vec d)) (hS : Convex ℝ S) (hSc : IsCompact S)
    (eta : ℝ) (heta : 0 < eta) (T : ℕ) (hT : 1 ≤ T) (xs fs : ℕ → Vec d) (hx1 : xs 1 ∈ S) :
    ((∀ t, 1 ≤ t → t < T → ∀ z ∈ S,
        euclNorm (z - xs (t + 1)) ^ 2 ≤ euclNorm (z - (xs t - eta • fs t)) ^ 2) →
      ∀ x ∈ S,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
            - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
          ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
            + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) ∧
    ((∀ t, 1 ≤ t → t < T → ∀ z ∈ S,
        euclNorm (z - xs (t + 1)) ^ 2 ≤ euclNorm (z - (xs t + eta • fs t)) ^ 2) →
      ∀ x ∈ S,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
            - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
          ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
            + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) := by
  have _ := hS
  have _ := hSc
  have _ := hx1
  constructor
  · intro hproj x hx
    exact GradientProof.loss_bound eta heta T hT xs fs x
      (fun t ht hlt => hproj t ht hlt x hx)
  · intro hproj x hx
    exact GradientProof.payoff_bound eta heta T hT xs fs x
      (fun t ht hlt => hproj t ht hlt x hx)
