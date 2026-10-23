-- Prove2me | solution 1 for ApproxOLO.FullInfo.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:51:31.89065+00:00
-- url     : https://prove2.me/submissions/e1de569c-ad76-46f3-8731-576ea2f23a11

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

namespace ApproxOLO.FullInfo.OracleProof

open Matrix EuclideanProof

lemma dot_nonneg {d : ℕ} (x y : Vec d) (hx : IsNonneg x) (hy : IsNonneg y) :
    0 ≤ x ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hy i))

lemma dot_nonpos {d : ℕ} (x y : Vec d) (hx : IsNonneg x) (hy : ∀ i, y i ≤ 0) :
    x ⬝ᵥ y ≤ 0 := Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hx i) (hy i))

lemma pos_nonneg {d : ℕ} (c : Vec d) : IsNonneg (posCoord c) := fun i => le_max_right (c i) 0
lemma neg_nonpos {d : ℕ} (c : Vec d) (i : Fin d) : negCoord c i ≤ 0 := min_le_right (c i) 0
lemma neg_neg_nonneg {d : ℕ} (c : Vec d) : IsNonneg (-negCoord c) :=
  fun i => neg_nonneg.mpr (neg_nonpos c i)

lemma coord_decomp {d : ℕ} (c : Vec d) : posCoord c + negCoord c = c := by
  ext i
  exact (max_add_min (c i) 0).trans (add_zero _)

lemma coord_orthogonal {d : ℕ} (c : Vec d) : posCoord c ⬝ᵥ negCoord c = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  change max (c i) 0 * min (c i) 0 = 0
  by_cases h : 0 ≤ c i
  · simp [max_eq_left h, min_eq_right h]
  · simp [max_eq_right (le_of_not_ge h), min_eq_left (le_of_not_ge h)]

lemma unitDir_norm_le {d : ℕ} (x : Vec d) : euclNorm (unitDir x) ≤ 1 := by
  by_cases hx : 0 < euclNorm x
  · rw [unitDir, if_pos hx, euclNorm_smul, abs_of_nonneg (inv_nonneg.mpr hx.le)]
    simp only [inv_mul_cancel₀ hx.ne', le_refl]
  · simp only [unitDir, if_neg hx, euclNorm_zero, zero_le_one]

lemma unitDir_nonneg {d : ℕ} (x : Vec d) (hx : IsNonneg x) : IsNonneg (unitDir x) := by
  unfold unitDir
  split_ifs with hp
  · intro i
    exact mul_nonneg (inv_nonneg.mpr (euclNorm_nonneg x)) (hx i)
  · intro i
    exact le_rfl

lemma unitDir_nonpos {d : ℕ} (x : Vec d) (hx : ∀ i, x i ≤ 0) :
    ∀ i, unitDir x i ≤ 0 := by
  unfold unitDir
  split_ifs with hp
  · intro i
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (euclNorm_nonneg x)) (hx i)
  · intro i
    exact le_rfl

lemma unitDir_dot_self {d : ℕ} (x : Vec d) : unitDir x ⬝ᵥ x = euclNorm x := by
  by_cases hx : 0 < euclNorm x
  · rw [unitDir, if_pos hx, smul_dotProduct, smul_eq_mul, ← euclNorm_sq]
    field_simp
  · have hz : x = 0 := (euclNorm_eq_zero x).mp (le_antisymm (le_of_not_gt hx) (euclNorm_nonneg x))
    subst x
    simp [euclNorm_zero]

lemma unitDir_dot_orthogonal {d : ℕ} (x y : Vec d) (hxy : x ⬝ᵥ y = 0) :
    unitDir x ⬝ᵥ y = 0 := by
  unfold unitDir
  split_ifs <;> simp [smul_dotProduct, hxy]

lemma unit_neg_dot {d : ℕ} (c : Vec d) : unitDir (negCoord c) ⬝ᵥ c = euclNorm (negCoord c) := by
  calc
    _ = unitDir (negCoord c) ⬝ᵥ (posCoord c + negCoord c) := by rw [coord_decomp]
    _ = _ := by rw [dotProduct_add, unitDir_dot_self,
    unitDir_dot_orthogonal _ _ (by rw [dotProduct_comm]; exact coord_orthogonal c), zero_add]

lemma unit_pos_dot {d : ℕ} (c : Vec d) : unitDir (posCoord c) ⬝ᵥ c = euclNorm (posCoord c) := by
  calc
    _ = unitDir (posCoord c) ⬝ᵥ (posCoord c + negCoord c) := by rw [coord_decomp]
    _ = _ := by rw [dotProduct_add, unitDir_dot_self,
      unitDir_dot_orthogonal _ _ (coord_orthogonal c), add_zero]

lemma dot_coord {d : ℕ} (x c : Vec d) : x ⬝ᵥ c = x ⬝ᵥ posCoord c + x ⬝ᵥ negCoord c := by
  rw [← dotProduct_add, coord_decomp]

lemma shifted_distance {d : ℕ} (s u : Vec d) (a : ℝ) (ha : 0 ≤ a)
    (hu : euclNorm u ≤ 1) : euclNorm (s - a • u - s) ≤ a := by
  have heq : s - a • u - s = -(a • u) := by abel
  rw [heq, euclNorm_neg, euclNorm_smul, abs_of_nonneg ha]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hu ha

lemma shifted_norm {d : ℕ} (s u : Vec d) (R a : ℝ) (hs : euclNorm s ≤ R)
    (ha : 0 ≤ a) (hu : euclNorm u ≤ 1) : euclNorm (s - a • u) ≤ R + a := by
  calc
    _ ≤ euclNorm s + euclNorm (a • u) := euclNorm_sub_le _ _
    _ = euclNorm s + a * euclNorm u := by rw [euclNorm_smul, abs_of_nonneg ha]
    _ ≤ R + a := by nlinarith

end ApproxOLO.FullInfo.OracleProof

open ApproxOLO.FullInfo ApproxOLO.FullInfo.EuclideanProof ApproxOLO.FullInfo.OracleProof Matrix

theorem solution {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (hO : IsApproxOracle K alpha O)
    (c : Vec d) :
    (extOracle O alpha R c).2 ∈ K ∧
    (∃ k ∈ K, euclNorm ((extOracle O alpha R c).1 - k) ≤ (1 + alpha) * R) ∧
    (∀ z ∈ K, (extOracle O alpha R c).1 ⬝ᵥ c ≤ (alpha • z) ⬝ᵥ c) ∧
    (∀ f ∈ Fs, (1 ≤ alpha → (extOracle O alpha R c).2 ⬝ᵥ f ≤ (extOracle O alpha R c).1 ⬝ᵥ f) ∧
      (alpha < 1 → (extOracle O alpha R c).1 ⬝ᵥ f ≤ (extOracle O alpha R c).2 ⬝ᵥ f)) ∧
    euclNorm (extOracle O alpha R c).1 ≤ (alpha + 2) * R := by
  obtain ⟨_, _, _, hKpos, hFpos, hR, _, _, hKnorm, _, _⟩ := hinst
  by_cases ha : 1 ≤ alpha
  · obtain ⟨hs, hmin, _⟩ := hO (posCoord c) (pos_nonneg c)
    simp only [extOracle, if_pos ha]
    refine ⟨hs, ⟨O (posCoord c), hs, ?_⟩, ?_, ?_, ?_⟩
    · have hb := shifted_distance (O (posCoord c)) (unitDir (negCoord c)) (alpha * R)
        (mul_nonneg halpha.le hR.le) (unitDir_norm_le _)
      linarith
    · intro z hz
      have hpos := hmin ha z hz
      have hsneg := dot_nonpos (O (posCoord c)) (negCoord c) (hKpos _ hs) (neg_nonpos c)
      have hlow : -(R * euclNorm (negCoord c)) ≤ z ⬝ᵥ negCoord c := by
        have hcs := neg_norm_mul_le_dot z (negCoord c)
        have hb := mul_le_mul_of_nonneg_right (hKnorm z hz) (euclNorm_nonneg (negCoord c))
        linarith
      have halow := mul_le_mul_of_nonneg_left hlow halpha.le
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, unit_neg_dot]
      rw [dot_coord (O (posCoord c)) c, dot_coord z c]
      nlinarith
    · intro f hf
      constructor
      · intro _
        have huf : unitDir (negCoord c) ⬝ᵥ f ≤ 0 := by
          rw [dotProduct_comm]
          exact dot_nonpos f _ (hFpos f hf) (unitDir_nonpos _ (neg_nonpos c))
        simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg halpha.le hR.le) huf
        linarith
      · intro hlt
        exact (not_lt_of_ge ha hlt).elim
    · have hb := shifted_norm (O (posCoord c)) (unitDir (negCoord c)) R (alpha * R)
        (hKnorm _ hs) (mul_nonneg halpha.le hR.le) (unitDir_norm_le _)
      linarith
  · have ha' : alpha < 1 := lt_of_not_ge ha
    obtain ⟨hs, _, hmax⟩ := hO (-negCoord c) (neg_neg_nonneg c)
    simp only [extOracle, if_neg ha]
    refine ⟨hs, ⟨O (-negCoord c), hs, ?_⟩, ?_, ?_, ?_⟩
    · have hb := shifted_distance (O (-negCoord c)) (unitDir (posCoord c)) R hR.le (unitDir_norm_le _)
      nlinarith
    · intro z hz
      have hneg : O (-negCoord c) ⬝ᵥ negCoord c ≤ alpha * (z ⬝ᵥ negCoord c) := by
        have ho := hmax ha' z hz
        simp only [dotProduct_neg] at ho
        linarith
      have hspos : O (-negCoord c) ⬝ᵥ posCoord c ≤ R * euclNorm (posCoord c) :=
        (dot_le_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (hKnorm _ hs) (euclNorm_nonneg _))
      have hzpos := dot_nonneg z (posCoord c) (hKpos z hz) (pos_nonneg c)
      have hap := mul_nonneg halpha.le hzpos
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, unit_pos_dot]
      rw [dot_coord (O (-negCoord c)) c, dot_coord z c]
      nlinarith
    · intro f hf
      constructor
      · intro hge
        exact (ha hge).elim
      · intro _
        have huf := dot_nonneg (unitDir (posCoord c)) f (unitDir_nonneg _ (pos_nonneg c)) (hFpos f hf)
        simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have := mul_nonneg hR.le huf
        linarith
    · have hb := shifted_norm (O (-negCoord c)) (unitDir (posCoord c)) R R
        (hKnorm _ hs) hR.le (unitDir_norm_le _)
      nlinarith
