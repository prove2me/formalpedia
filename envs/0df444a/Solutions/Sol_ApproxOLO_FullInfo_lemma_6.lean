-- Prove2me | solution 1 for ApproxOLO.FullInfo.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:46:53.282535+00:00
-- url     : https://prove2.me/submissions/cb8f31b6-7cb7-4cf4-9e67-ca63ec8a21ff

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



set_option autoImplicit false

namespace ApproxOLO.FullInfo.DistanceProof
open Matrix

lemma quadratic_direction_nonneg (A B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ t * (2 * A + t * B)) : 0 ≤ A := by
  by_contra hA
  have hA' : A < 0 := lt_of_not_ge hA
  let t : ℝ := min 1 (-A / (B + 1))
  have hden : 0 < B + 1 := by linarith
  have ht : 0 < t := lt_min zero_lt_one (div_pos (neg_pos.mpr hA') hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htB : t * (B + 1) ≤ -A := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hp : 0 ≤ 2 * A + t * B := nonneg_of_mul_nonneg_right (h t ht.le ht1) ht
  nlinarith

lemma simplex_opt_dot_variational {d N : ℕ} (x : Vec d) (v : Fin N → Vec d)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1)
    (hopt : ∀ b : Fin N → ℝ, (∀ i, 0 ≤ b i) → ∑ i, b i = 1 →
      (∑ i, a i • v i - x) ⬝ᵥ (∑ i, a i • v i - x) ≤
      (∑ i, b i • v i - x) ⬝ᵥ (∑ i, b i • v i - x)) (i : Fin N) :
    0 ≤ (∑ j, a j • v j - x) ⬝ᵥ (v i - ∑ j, a j • v j) := by
  classical
  let p : Vec d := ∑ j, a j • v j
  let r : Vec d := p - x
  let q : Vec d := v i - p
  change 0 ≤ r ⬝ᵥ q
  apply quadratic_direction_nonneg (r ⬝ᵥ q) (q ⬝ᵥ q)
  · exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (q j))
  intro t ht ht1
  let b : Fin N → ℝ := fun j => (1-t)*a j + if j=i then t else 0
  have hb (j : Fin N) : 0 ≤ b j := by
    dsimp [b]
    exact add_nonneg (mul_nonneg (by linarith) (ha j)) (by split_ifs <;> positivity)
  have hbsum : ∑ j, b j = 1 := by
    simp [b, Finset.sum_add_distrib, ← Finset.mul_sum, hasum]
  have hbpoint : ∑ j, b j • v j = (1-t) • p + t • v i := by
    dsimp [b, p]
    simp [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, ite_smul]
  have hbr : (∑ j, b j • v j) - x = r + t • q := by
    rw [hbpoint]
    ext l
    simp only [r, q, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hh := hopt b hb hbsum
  change r ⬝ᵥ r ≤ _ at hh
  rw [hbr] at hh
  have he : (r + t • q) ⬝ᵥ (r + t • q) =
      r ⬝ᵥ r + t * (2 * (r ⬝ᵥ q) + t * (q ⬝ᵥ q)) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm q r]
    ring
  rw [he] at hh
  linarith

end ApproxOLO.FullInfo.DistanceProof

namespace ApproxOLO.FullInfo.DistanceProof
open Matrix EuclideanProof

lemma simplex_opt_variational {d N : ℕ} (x : Vec d) (v : Fin N → Vec d)
    (a : Fin N → ℝ) (ha : IsSimplexOpt v x a) (i : Fin N) :
    0 ≤ (∑ j, a j • v j - x) ⬝ᵥ (v i - ∑ j, a j • v j) := by
  apply simplex_opt_dot_variational x v a ha.1 ha.2.1 _ i
  intro b hb hbsum
  have h := ha.2.2 b hb hbsum
  simp only [euclNorm_sq] at h
  linarith

end ApproxOLO.FullInfo.DistanceProof

open ApproxOLO.FullInfo Matrix

theorem solution {d N : ℕ} (hN : 1 ≤ N) (x : Vec d) (v : Fin N → Vec d) (eps : ℝ)
    (heps : 0 < eps) (hmin : ∀ w : Vec d, euclNorm w = 1 → ∃ i, (x - v i) ⬝ᵥ w ≤ eps)
    (a : Fin N → ℝ) (ha : IsSimplexOpt v x a) :
    euclNorm (∑ i, a i • v i - x) ≤ eps := by
  have _hN := hN
  let p : Vec d := ∑ i, a i • v i
  change euclNorm (p-x) ≤ eps
  by_contra hbound
  have hgap : eps < euclNorm (p-x) := lt_of_not_ge hbound
  let s : ℝ := euclNorm (x-p)
  have hs : 0 < s := by
    dsimp [s]
    rw [EuclideanProof.euclNorm_sub_comm]
    linarith
  have hunit : euclNorm (s⁻¹ • (x-p)) = 1 := by
    rw [EuclideanProof.euclNorm_smul, abs_of_pos (inv_pos.mpr hs)]
    change s⁻¹ * s = 1
    exact inv_mul_cancel₀ hs.ne'
  obtain ⟨i, hi⟩ := hmin (s⁻¹ • (x-p)) hunit
  have hvar : 0 ≤ (p-x) ⬝ᵥ (v i-p) := DistanceProof.simplex_opt_variational x v a ha i
  have hrel : (x-v i) ⬝ᵥ (x-p) =
      (x-p) ⬝ᵥ (x-p) + (p-x) ⬝ᵥ (v i-p) := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm (v i) x, dotProduct_comm (v i) p, dotProduct_comm p x]
    ring
  have hlo : s^2 ≤ (x-v i) ⬝ᵥ (x-p) := by
    rw [hrel]
    have hsq : s^2 = (x-p) ⬝ᵥ (x-p) := EuclideanProof.euclNorm_sq (x-p)
    linarith
  rw [dotProduct_smul, smul_eq_mul] at hi
  have hscale := mul_le_mul_of_nonneg_left hi hs.le
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hscale
  have hgap' : eps < s := by
    dsimp [s]
    rw [EuclideanProof.euclNorm_sub_comm]
    exact hgap
  have hprod := mul_pos hs (sub_pos.mpr hgap')
  nlinarith
