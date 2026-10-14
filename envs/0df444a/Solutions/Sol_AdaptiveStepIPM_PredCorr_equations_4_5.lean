-- Prove2me | solution 1 for AdaptiveStepIPM.PredCorr.equations_4_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:39:19.046278+00:00
-- url     : https://prove2.me/submissions/01124f89-c750-47da-817c-e4cd5a66deaa

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix


namespace AdaptiveStepIPM.PredCorr

lemma pc_mu_pos {n : ℕ} (hn : 1 ≤ n) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) : 0 < mu x s := by
  unfold mu
  apply div_pos
  · unfold dotProduct
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun j _ => mul_pos (hx j) (hs j)) Finset.univ_nonempty
  · exact_mod_cast hn

lemma pc_sum_w {n : ℕ} (hn : 1 ≤ n) (x s : Fin n → ℝ) :
    ∑ j, x j * s j = n * mu x s := by
  unfold mu
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ this]; rfl

lemma pc_orth {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s γ dx dy ds) :
    ∑ j, dx j * ds j = 0 := by
  have hds : ds = -(Aᵀ *ᵥ dy) := by
    have := hd.2.2; rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have : dx ⬝ᵥ ds = 0 := by
    rw [hds, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, hd.2.1, zero_dotProduct,
      neg_zero]
  exact this

lemma pc_prod_step {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s γ dx dy ds) (t : ℝ) (j : Fin n) :
    (x j + t * dx j) * (s j + t * ds j) =
      x j * s j + t * (γ * mu x s - x j * s j) + t ^ 2 * (dx j * ds j) := by
  rw [← hd.1 j]; ring

lemma pc_mu_step {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (γ : ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s γ dx dy ds) (t : ℝ) :
    mu (stepX x dx t) (stepS s ds t) = (1 - t + t * γ) * mu x s := by
  have h1 : (stepX x dx t) ⬝ᵥ (stepS s ds t) = ∑ j, (x j * s j +
      t * (γ * mu x s - x j * s j) + t ^ 2 * (dx j * ds j)) := by
    unfold dotProduct
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← pc_prod_step A x s γ dx dy ds hd t j]
    rfl
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [show mu (stepX x dx t) (stepS s ds t) =
    ((stepX x dx t) ⬝ᵥ (stepS s ds t)) / n from rfl, h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, pc_orth A x s γ dx dy ds hd, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, pc_sum_w hn]
  field_simp
  ring

lemma pc_dev_eq {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (γ : ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s γ dx dy ds) (t : ℝ) (j : Fin n) :
    stepX x dx t j * stepS s ds t j - mu (stepX x dx t) (stepS s ds t) =
      (1 - t) * (x j * s j - mu x s) + t ^ 2 * (dx j * ds j) := by
  rw [pc_mu_step hn A x s γ dx dy ds hd t]
  show (x j + t * dx j) * (s j + t * ds j) - _ = _
  rw [pc_prod_step A x s γ dx dy ds hd t j]
  ring

theorem equations_4_5_core {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (x s dx ds : Fin n → ℝ)
    (dy : Fin m → ℝ) (γ θ : ℝ)
    (hd : SearchDirection A x s γ dx dy ds) :
    mu (stepX x dx θ) (stepS s ds θ) =
      (1 - θ) * mu x s + θ * γ * mu x s ∧
    (fun j => stepX x dx θ j * stepS s ds θ j -
      mu (stepX x dx θ) (stepS s ds θ)) =
      (fun j => (1 - θ) * (x j * s j - mu x s) + θ ^ 2 * (dx j * ds j)) := by
  refine ⟨?_, ?_⟩
  · rw [pc_mu_step hn A x s γ dx dy ds hd θ]; ring
  · funext j
    exact pc_dev_eq hn A x s γ dx dy ds hd θ j

/-! ### the Euclidean norm -/

lemma pc_l2_sq {n : ℕ} (v : Fin n → ℝ) : l2Norm v ^ 2 = ∑ j, v j ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (v j)))]

lemma pc_l2_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ l2Norm v := Real.sqrt_nonneg _

lemma pc_abs_le_l2 {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : |v j| ≤ l2Norm v := by
  unfold l2Norm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun k => v k ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ j)

lemma pc_l2_eq_norm {n : ℕ} (v : Fin n → ℝ) :
    l2Norm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold l2Norm
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Real.norm_eq_abs, sq_abs]

lemma pc_l2_comb {n : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (u v : Fin n → ℝ) :
    l2Norm (fun j => a * u j + b * v j) ≤ a * l2Norm u + b * l2Norm v := by
  rw [pc_l2_eq_norm, pc_l2_eq_norm u, pc_l2_eq_norm v]
  have : (WithLp.toLp 2 (fun j => a * u j + b * v j) : EuclideanSpace ℝ (Fin n)) =
      a • (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) +
        b • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) := by
    ext j; simp
  rw [this]
  calc _ ≤ ‖a • (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ +
        ‖b • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

lemma pc_Pq {n : ℕ} (x s dx ds : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (j : Fin n) : Pq x s dx ds j = dx j * ds j := by
  unfold Pq scaledP scaledQ
  have hx' := hx j; have hs' := hs j
  have : Real.sqrt (s j / x j) * Real.sqrt (x j / s j) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg hs'.le hx'.le)]
    rw [show s j / x j * (x j / s j) = 1 by field_simp]
    simp
  calc Real.sqrt (s j / x j) * dx j * (Real.sqrt (x j / s j) * ds j)
      = (Real.sqrt (s j / x j) * Real.sqrt (x j / s j)) * (dx j * ds j) := by ring
    _ = dx j * ds j := by rw [this, one_mul]

lemma pc_Pq_fun {n : ℕ} (x s dx ds : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    Pq x s dx ds = fun j => dx j * ds j := by
  funext j; exact pc_Pq x s dx ds hx hs j

lemma pc_rsq {n : ℕ} (γ : ℝ) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (j : Fin n) :
    scaledR x s γ j ^ 2 = (γ * mu x s - x j * s j) ^ 2 / (x j * s j) := by
  unfold scaledR
  rw [div_pow, Real.sq_sqrt (mul_pos (hx j) (hs j)).le]

theorem lemma_2a_core {n : ℕ} (hn : 1 ≤ n) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) :
    (l2Norm (scaledR x s 0)) ^ 2 = (n : ℝ) * mu x s := by
  rw [pc_l2_sq, ← pc_sum_w hn]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pc_rsq 0 x s hx hs j]
  have := (mul_pos (hx j) (hs j)).ne'
  rw [show (0 * mu x s - x j * s j) ^ 2 = (x j * s j) * (x j * s j) by ring, mul_div_assoc,
    div_self this, mul_one]

theorem lemma_2b_core {n : ℕ} (hn : 1 ≤ n) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) (β : ℝ) (hβ1 : β < 1)
    (hN : l2Norm (fun j => x j * s j - mu x s) ≤ β * mu x s) :
    (l2Norm (scaledR x s 1)) ^ 2 ≤ β ^ 2 * mu x s / (1 - β) := by
  have hμ := pc_mu_pos hn x s hx hs
  have hβμ : 0 ≤ β * mu x s := le_trans (pc_l2_nonneg _) hN
  have hc : 0 < (1 - β) * mu x s := mul_pos (by linarith) hμ
  have hlow : ∀ j, (1 - β) * mu x s ≤ x j * s j := by
    intro j
    have h := pc_abs_le_l2 (fun j => x j * s j - mu x s) j
    have h2 := le_trans h hN
    have h3 := neg_abs_le (x j * s j - mu x s)
    linarith
  have hsum : ∑ j, (x j * s j - mu x s) ^ 2 ≤ (β * mu x s) ^ 2 := by
    rw [← pc_l2_sq (fun j => x j * s j - mu x s)]
    exact pow_le_pow_left₀ (pc_l2_nonneg _) hN 2
  rw [pc_l2_sq]
  calc ∑ j, scaledR x s 1 j ^ 2
      ≤ ∑ j, (x j * s j - mu x s) ^ 2 / ((1 - β) * mu x s) := by
        apply Finset.sum_le_sum
        intro j _
        rw [pc_rsq 1 x s hx hs j]
        rw [show (1 * mu x s - x j * s j) ^ 2 = (x j * s j - mu x s) ^ 2 by ring]
        exact div_le_div_of_nonneg_left (sq_nonneg _) hc (hlow j)
    _ = (∑ j, (x j * s j - mu x s) ^ 2) / ((1 - β) * mu x s) := by
        rw [Finset.sum_div]
    _ ≤ (β * mu x s) ^ 2 / ((1 - β) * mu x s) := div_le_div_of_nonneg_right hsum hc.le
    _ = β ^ 2 * mu x s / (1 - β) := by
        have : (1 - β) ≠ 0 := by linarith
        field_simp

theorem lemma_1a_core {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s γ dx dy ds) :
    l2Norm (Pq x s dx ds) ≤ (Real.sqrt 2 / 4) * (l2Norm (scaledR x s γ)) ^ 2 := by
  set R := (l2Norm (scaledR x s γ)) ^ 2 with hR
  have key : ∀ k, 4 * (dx k * ds k) ≤ scaledR x s γ k ^ 2 := by
    intro k
    rw [pc_rsq γ x s hx hs k, ← hd.1 k, le_div_iff₀ (mul_pos (hx k) (hs k))]
    nlinarith [sq_nonneg (s k * dx k - x k * ds k)]
  set a : Fin n → ℝ := fun j => dx j * ds j with ha
  have hsum0 : ∑ j, a j = 0 := pc_orth A x s γ dx dy ds hd
  set P := ∑ j, max (a j) 0 with hP
  set N := ∑ j, max (-a j) 0 with hN
  have hPN : P = N := by
    have : ∑ j, (max (a j) 0 - max (-a j) 0) = ∑ j, a j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases le_total (a j) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rw [Finset.sum_sub_distrib, hsum0] at this
    linarith
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hsq : ∀ j, a j ^ 2 = max (a j) 0 ^ 2 + max (-a j) 0 ^ 2 := by
    intro j
    rcases le_total (a j) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hsq_le : ∀ (f : Fin n → ℝ), (∀ j, 0 ≤ f j) → ∑ j, f j ^ 2 ≤ (∑ j, f j) ^ 2 := by
    intro f hf
    have hj : ∀ j, f j ≤ ∑ k, f k := fun j =>
      Finset.single_le_sum (f := f) (fun k _ => hf k) (Finset.mem_univ j)
    calc ∑ j, f j ^ 2 ≤ ∑ j, f j * ∑ k, f k := by
          apply Finset.sum_le_sum; intro j _
          rw [sq]; exact mul_le_mul_of_nonneg_left (hj j) (hf j)
      _ = (∑ j, f j) ^ 2 := by rw [← Finset.sum_mul, sq]
  have hA2 : ∑ j, a j ^ 2 ≤ 2 * P ^ 2 := by
    have e : ∑ j, a j ^ 2 = ∑ j, max (a j) 0 ^ 2 + ∑ j, max (-a j) 0 ^ 2 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => hsq j)
    have h1 := hsq_le (fun j => max (a j) 0) (fun j => le_max_right _ _)
    have h2 := hsq_le (fun j => max (-a j) 0) (fun j => le_max_right _ _)
    rw [e, ← hP, ← hN] at *
    rw [← hPN] at h2
    linarith
  have h4P : 4 * P ≤ R := by
    rw [hR, pc_l2_sq, hP, Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    rcases le_total (a j) 0 with h | h
    · rw [max_eq_right h, mul_zero]; exact sq_nonneg _
    · rw [max_eq_left h]; exact key j
  have hfin : ∑ j, a j ^ 2 ≤ (Real.sqrt 2 / 4 * R) ^ 2 := by
    have e : (Real.sqrt 2 / 4 * R) ^ 2 = 2 * (R / 4) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    rw [e]
    have : P ^ 2 ≤ (R / 4) ^ 2 := pow_le_pow_left₀ hP0 (by linarith) 2
    linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  rw [pc_Pq_fun x s dx ds hx hs]
  unfold l2Norm
  calc Real.sqrt (∑ j, (dx j * ds j) ^ 2) ≤ Real.sqrt ((Real.sqrt 2 / 4 * R) ^ 2) :=
        Real.sqrt_le_sqrt hfin
    _ = Real.sqrt 2 / 4 * R := Real.sqrt_sq (by positivity)

end AdaptiveStepIPM.PredCorr

open AdaptiveStepIPM.PredCorr


theorem solution {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (x s dx ds : Fin n → ℝ)
    (dy : Fin m → ℝ) (γ θ : ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hd : SearchDirection A x s γ dx dy ds) :
    mu (stepX x dx θ) (stepS s ds θ) =
      (1 - θ) * mu x s + θ * γ * mu x s ∧
    (fun j => stepX x dx θ j * stepS s ds θ j -
      mu (stepX x dx θ) (stepS s ds θ)) =
      (fun j => (1 - θ) * (x j * s j - mu x s) + θ ^ 2 * (dx j * ds j)) := by
  exact equations_4_5_core hn A x s dx ds dy γ θ hd
