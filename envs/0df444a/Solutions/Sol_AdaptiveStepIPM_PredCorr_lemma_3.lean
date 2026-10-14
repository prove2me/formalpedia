-- Prove2me | solution 1 for AdaptiveStepIPM.PredCorr.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:43:22.477181+00:00
-- url     : https://prove2.me/submissions/372c0a6b-efb3-4b85-823e-bcf0a08f2822

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

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

/-! ### Algorithm 1 -/

lemma pc_pos_of_prod_left {a b da db θ : ℝ} (ha : 0 < a) (hθ : 0 ≤ θ)
    (h : ∀ t, 0 ≤ t → t ≤ θ → 0 < (a + t * da) * (b + t * db)) : 0 < a + θ * da := by
  by_contra hc
  push_neg at hc
  have hda : da < 0 := by nlinarith
  have hne : da ≠ 0 := ne_of_lt hda
  have ht0 : 0 ≤ a / (-da) := div_nonneg ha.le (by linarith)
  have ht0θ : a / (-da) ≤ θ := by rw [div_le_iff₀ (by linarith)]; linarith
  have h0 : a + a / (-da) * da = 0 := by
    rw [div_neg, neg_mul, div_mul_cancel₀ a hne]; ring
  have := h _ ht0 ht0θ
  rw [h0, zero_mul] at this
  exact lt_irrefl _ this

lemma pc_pos_of_prod {a b da db θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ)
    (h : ∀ t, 0 ≤ t → t ≤ θ → 0 < (a + t * da) * (b + t * db)) :
    0 < a + θ * da ∧ 0 < b + θ * db :=
  ⟨pc_pos_of_prod_left ha hθ h,
    pc_pos_of_prod_left hb hθ (fun t h0 h1 => by rw [mul_comm]; exact h t h0 h1)⟩

lemma pc_step_F0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s : Fin n → ℝ) (hF : F0 A b c x s) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s γ dx dy ds) (θ : ℝ) (hθ : 0 ≤ θ)
    (hprod : ∀ t, 0 ≤ t → t ≤ θ → ∀ j, 0 < (x j + t * dx j) * (s j + t * ds j)) :
    F0 A b c (stepX x dx θ) (stepS s ds θ) := by
  obtain ⟨hfeas, ⟨y, hy⟩, hx, hs⟩ := hF
  rw [LinearOptimization.generalFeasibleSet_stdFormLP] at hfeas
  obtain ⟨hAx, -⟩ := hfeas
  have hpos := fun j => pc_pos_of_prod (hx j) (hs j) hθ (fun t h0 h1 => hprod t h0 h1 j)
  refine ⟨?_, ⟨y + θ • dy, ?_⟩, fun j => (hpos j).1, fun j => (hpos j).2⟩
  · rw [LinearOptimization.generalFeasibleSet_stdFormLP]
    refine ⟨?_, ?_⟩
    · show A *ᵥ (x + θ • dx) = b
      rw [mulVec_add, mulVec_smul, hd.2.1, smul_zero, add_zero]; exact hAx
    · intro j; exact (hpos j).1.le
  · show Aᵀ *ᵥ (y + θ • dy) + (s + θ • ds) = c
    rw [mulVec_add, mulVec_smul]
    have e : Aᵀ *ᵥ y + θ • Aᵀ *ᵥ dy + (s + θ • ds) = (Aᵀ *ᵥ y + s) + θ • (Aᵀ *ᵥ dy + ds) := by
      rw [smul_add]; abel
    rw [e, hy, hd.2.2, smul_zero, add_zero]

lemma pc_sqrt2_le : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem pc_corrector {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x s : Fin n → ℝ) (hN : N2 A b c (1 / 2) x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s 1 dx dy ds) :
    N2 A b c (1 / 4) (stepX x dx 1) (stepS s ds 1) ∧
      mu (stepX x dx 1) (stepS s ds 1) = mu x s := by
  obtain ⟨hF, hdev⟩ := hN
  have hx := hF.2.2.1
  have hs := hF.2.2.2
  have hμ := pc_mu_pos hn x s hx hs
  have hmu1 : mu (stepX x dx 1) (stepS s ds 1) = mu x s := by
    rw [pc_mu_step hn A x s 1 dx dy ds hd 1]; ring
  have hr := lemma_2b_core hn x s hx hs (1 / 2) (by norm_num) hdev
  have hr' : l2Norm (scaledR x s 1) ^ 2 ≤ mu x s / 2 := by
    calc _ ≤ _ := hr
      _ = mu x s / 2 := by ring
  have hPq := lemma_1a_core A x s 1 hx hs dx dy ds hd
  have hPqb : l2Norm (Pq x s dx ds) ≤ mu x s / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hr' (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 4)
    have h2 := pc_sqrt2_le
    nlinarith
  have hdxds : ∀ j, |dx j * ds j| ≤ mu x s / 4 := fun j => by
    rw [← pc_Pq x s dx ds hx hs j]; exact le_trans (pc_abs_le_l2 _ j) hPqb
  have hxsdev : ∀ j, |x j * s j - mu x s| ≤ mu x s / 2 := fun j =>
    le_trans (pc_abs_le_l2 (fun j => x j * s j - mu x s) j) (by linarith [hdev])
  refine ⟨⟨pc_step_F0 A b c x s hF 1 dx dy ds hd 1 zero_le_one ?_, ?_⟩, hmu1⟩
  · intro t h0 h1 j
    rw [pc_prod_step A x s 1 dx dy ds hd t j]
    have a1 := abs_le.1 (hdxds j)
    have a2 := abs_le.1 (hxsdev j)
    have e1 : -((1 - t) * (mu x s / 2)) ≤ (1 - t) * (x j * s j - mu x s) := by
      nlinarith
    have e2 : -(t ^ 2 * (mu x s / 4)) ≤ t ^ 2 * (dx j * ds j) := by
      nlinarith [sq_nonneg t]
    have e3 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · have e : (fun j => stepX x dx 1 j * stepS s ds 1 j - mu (stepX x dx 1) (stepS s ds 1)) =
        fun j => dx j * ds j := by
      funext j; rw [pc_dev_eq hn A x s 1 dx dy ds hd 1 j]; ring
    rw [e, hmu1, ← pc_Pq_fun x s dx ds hx hs]; linarith

theorem pc_predictor {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x s : Fin n → ℝ) (hN : N2 A b c (1 / 4) x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : SearchDirection A x s 0 dx dy ds) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hPu : u ^ 2 * l2Norm (Pq x s dx ds) ≤ mu x s / 8) :
    N2 A b c (1 / 2) (stepX x dx u) (stepS s ds u) := by
  obtain ⟨hF, hdev⟩ := hN
  have hx := hF.2.2.1
  have hs := hF.2.2.2
  have hμ := pc_mu_pos hn x s hx hs
  have hmu : mu (stepX x dx u) (stepS s ds u) = (1 - u) * mu x s := by
    rw [pc_mu_step hn A x s 0 dx dy ds hd u]; ring
  have hP0 : 0 ≤ l2Norm (Pq x s dx ds) := pc_l2_nonneg _
  have hdd : ∀ j, |dx j * ds j| ≤ l2Norm (Pq x s dx ds) := fun j => by
    rw [← pc_Pq x s dx ds hx hs j]; exact pc_abs_le_l2 _ j
  have hxsdev : ∀ j, |x j * s j - mu x s| ≤ mu x s / 4 := fun j =>
    le_trans (pc_abs_le_l2 (fun j => x j * s j - mu x s) j) (by linarith [hdev])
  refine ⟨pc_step_F0 A b c x s hF 0 dx dy ds hd u hu0 ?_, ?_⟩
  · intro t h0 h1 j
    rw [pc_prod_step A x s 0 dx dy ds hd t j]
    have ht2 : t ^ 2 * l2Norm (Pq x s dx ds) ≤ mu x s / 8 :=
      le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) hP0) hPu
    have a1 := abs_le.1 (hdd j)
    have a2 := abs_le.1 (hxsdev j)
    have e1 : -((1 - t) * (mu x s / 4)) ≤ (1 - t) * (x j * s j - mu x s) := by
      nlinarith
    have e2 : -(t ^ 2 * l2Norm (Pq x s dx ds)) ≤ t ^ 2 * (dx j * ds j) := by
      nlinarith [sq_nonneg t]
    nlinarith
  · have e : (fun j => stepX x dx u j * stepS s ds u j - mu (stepX x dx u) (stepS s ds u)) =
        fun j => (1 - u) * (x j * s j - mu x s) + u ^ 2 * (dx j * ds j) :=
      funext (pc_dev_eq hn A x s 0 dx dy ds hd u)
    rw [e, hmu]
    refine le_trans (pc_l2_comb (1 - u) (u ^ 2) (by linarith) (sq_nonneg u)
      (fun j => x j * s j - mu x s) (fun j => dx j * ds j)) ?_
    rw [← pc_Pq_fun x s dx ds hx hs]
    have h1 := mul_le_mul_of_nonneg_left hdev (by linarith : (0:ℝ) ≤ 1 - u)
    nlinarith

lemma pc_theta1_nonneg {n : ℕ} (x s dx ds : Fin n → ℝ) : 0 ≤ theta1 x s dx ds := by
  unfold theta1
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (Real.sqrt_nonneg _)

lemma pc_theta1_le {n : ℕ} (x s dx ds : Fin n → ℝ) : theta1 x s dx ds ≤ 1 / 2 := by
  unfold theta1
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem lemma_4_core {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s dx ds : Fin n → ℝ) (dy : Fin m → ℝ) (θbar : ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hd : SearchDirection A x s 0 dx dy ds)
    (hmax : IsGreatest {θ : ℝ | PredictorAdmissible A b c x s dx ds θ} θbar) :
    PredictorAdmissible A b c x s dx ds (theta1 x s dx ds) ∧
      theta1 x s dx ds ≤ θbar := by
  have hx := hxs.1.2.2.1
  have hs := hxs.1.2.2.2
  have hμ := pc_mu_pos hn x s hx hs
  have hadm : PredictorAdmissible A b c x s dx ds (theta1 x s dx ds) := by
    refine ⟨pc_theta1_nonneg x s dx ds, fun u hu => pc_predictor hn A b c x s hxs dx dy ds hd u
      hu.1 (le_trans hu.2 (pc_theta1_le x s dx ds)) ?_⟩
    by_cases hP : l2Norm (Pq x s dx ds) = 0
    · rw [hP, mul_zero]; positivity
    · have hPpos : 0 < l2Norm (Pq x s dx ds) := lt_of_le_of_ne (pc_l2_nonneg _) (Ne.symm hP)
      have hle : theta1 x s dx ds ≤ Real.sqrt (mu x s / (8 * l2Norm (Pq x s dx ds))) := by
        unfold theta1; rw [if_neg hP]; exact min_le_right _ _
      have hu2 : u ^ 2 ≤ mu x s / (8 * l2Norm (Pq x s dx ds)) := by
        have := pow_le_pow_left₀ hu.1 (le_trans hu.2 hle) 2
        rwa [Real.sq_sqrt (by positivity)] at this
      calc u ^ 2 * l2Norm (Pq x s dx ds)
          ≤ mu x s / (8 * l2Norm (Pq x s dx ds)) * l2Norm (Pq x s dx ds) :=
            mul_le_mul_of_nonneg_right hu2 hPpos.le
        _ = mu x s / 8 := by field_simp
  exact ⟨hadm, hmax.2 hadm⟩

theorem lemma_3_core {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hstep : Alg1Step A b c x s xNext sNext) :
    N2 A b c (1 / 4) xNext sNext := by
  obtain ⟨dx, dy, ds, θbar, dx', dy', ds', hd, hmax, hd', rfl, rfl⟩ := hstep
  have hN := hmax.1.2 θbar ⟨hmax.1.1, le_rfl⟩
  exact (pc_corrector hn A b c _ _ hN dx' dy' ds' hd').1

lemma pc_sqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8:ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

lemma pc_c_sq (n : ℕ) (hn : 1 ≤ n) :
    ((8 : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (Real.sqrt 8 * n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((n:ℝ) ^ (-(1 / 2 : ℝ))),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hnR.le]
  norm_num
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg_one, ← Real.sqrt_eq_rpow]
  field_simp

lemma pc_theta1_ge {m n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x s : Fin n → ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s) (hd : SearchDirection A x s 0 dx dy ds) :
    (8 : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ theta1 x s dx ds := by
  have hn1 : 1 ≤ n := by omega
  have hx := hxs.1.2.2.1
  have hs := hxs.1.2.2.2
  have hμ := pc_mu_pos hn1 x s hx hs
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hc2 := pc_c_sq n hn1
  set cc := (8 : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) with hcc
  have hc0 : 0 ≤ cc := by positivity
  have hs8 : 2 ≤ Real.sqrt 8 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num), Real.sqrt_nonneg 8]
  have hP : l2Norm (Pq x s dx ds) ≤ Real.sqrt 2 / 4 * (n * mu x s) := by
    have := lemma_1a_core A x s 0 hx hs dx dy ds hd
    rwa [lemma_2a_core hn1 x s hx hs] at this
  have hhalf : cc ≤ 1 / 2 := by
    have : cc ^ 2 ≤ 1 / 4 := by
      rw [hc2, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  unfold theta1
  split_ifs with h0
  · exact hhalf
  · have hPpos : 0 < l2Norm (Pq x s dx ds) := lt_of_le_of_ne (pc_l2_nonneg _) (Ne.symm h0)
    apply le_min hhalf
    have hsq : cc ^ 2 ≤ mu x s / (8 * l2Norm (Pq x s dx ds)) := by
      rw [hc2, div_le_div_iff₀ (by positivity) (by positivity), pc_sqrt8]
      have h2 := Real.sqrt_nonneg 2
      nlinarith
    calc cc = Real.sqrt (cc ^ 2) := (Real.sqrt_sq hc0).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq

theorem contraction_core {m n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hstep : Alg1Step A b c x s xNext sNext) :
    mu xNext sNext ≤
      (1 - (8 : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))) * mu x s := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨dx, dy, ds, θbar, dx', dy', ds', hd, hmax, hd', rfl, rfl⟩ := hstep
  have hN := hmax.1.2 θbar ⟨hmax.1.1, le_rfl⟩
  rw [(pc_corrector hn1 A b c _ _ hN dx' dy' ds' hd').2, pc_mu_step hn1 A x s 0 dx dy ds hd θbar]
  have h4 := (lemma_4_core hn1 A b c x s dx ds dy θbar hxs hd hmax).2
  have hθ := pc_theta1_ge hn A b c x s dx dy ds hxs hd
  have hμ := pc_mu_pos hn1 x s hxs.1.2.2.1 hxs.1.2.2.2
  have := mul_le_mul_of_nonneg_right (le_trans hθ h4) hμ.le
  nlinarith

end AdaptiveStepIPM.PredCorr

open AdaptiveStepIPM.PredCorr


theorem solution {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hstep : Alg1Step A b c x s xNext sNext) :
    N2 A b c (1 / 4) xNext sNext := by
  exact lemma_3_core hn A b c x s xNext sNext hstep
