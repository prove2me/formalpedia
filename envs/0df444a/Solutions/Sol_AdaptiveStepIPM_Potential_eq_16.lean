-- Prove2me | solution 1 for AdaptiveStepIPM.Potential.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:08:31.883114+00:00
-- url     : https://prove2.me/submissions/e6fa1a9e-4ebb-406f-8836-ce9815000cfb

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3

open Matrix


namespace AdaptiveStepIPM.Potential

lemma g8_dot_zero {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {γ : ℝ} {x s dx ds : Fin n → ℝ}
    {dy : Fin m → ℝ} (hd : IsNewtonDirection A γ x s dx dy ds) : ∑ j, dx j * ds j = 0 := by
  obtain ⟨_, h2, h3⟩ := hd
  have hds : ds = -(Aᵀ *ᵥ dy) := eq_neg_of_add_eq_zero_right h3
  have : dx ⬝ᵥ ds = 0 := by
    rw [hds, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, h2, zero_dotProduct, neg_zero]
  simpa [dotProduct] using this

lemma g8_prod {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {γ : ℝ} {x s dx ds : Fin n → ℝ}
    {dy : Fin m → ℝ} (hd : IsNewtonDirection A γ x s dx dy ds) (θ : ℝ) (j : Fin n) :
    lineStep x dx θ j * lineStep s ds θ j =
      (1 - θ) * (x j * s j) + θ * (γ * PredCorr.mu x s) + θ ^ 2 * (dx j * ds j) := by
  have := hd.1 j
  simp only [lineStep]
  linear_combination θ * this

lemma g8_dot {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {γ : ℝ} {x s dx ds : Fin n → ℝ}
    {dy : Fin m → ℝ} (hn : 1 ≤ n) (hd : IsNewtonDirection A γ x s dx dy ds) (θ : ℝ) :
    lineStep x dx θ ⬝ᵥ lineStep s ds θ = (1 - θ * (1 - γ)) * (x ⬝ᵥ s) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h0 := g8_dot_zero hd
  have e1 : lineStep x dx θ ⬝ᵥ lineStep s ds θ =
      ∑ j, ((1 - θ) * (x j * s j) + θ * (γ * PredCorr.mu x s) + θ ^ 2 * (dx j * ds j)) := by
    unfold dotProduct
    exact Finset.sum_congr rfl (fun j _ => g8_prod hd θ j)
  rw [e1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum (s := Finset.univ)
    (f := fun j => dx j * ds j) (a := θ ^ 2), h0, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, PredCorr.mu]
  have : ∑ j, x j * s j = x ⬝ᵥ s := rfl
  rw [this]
  field_simp
  ring

lemma g8_comp_ge {n : ℕ} {z : Fin n → ℝ} {r : ℝ} (h : negInfNorm z ≤ r) (j : Fin n) :
    -r ≤ z j := by
  have h1 : ‖min (z j) 0‖ ≤ negInfNorm z := by
    unfold negInfNorm; exact norm_le_pi_norm (fun j => min (z j) 0) j
  rw [Real.norm_eq_abs] at h1
  have := neg_abs_le (min (z j) 0)
  have := min_le_left (z j) 0
  linarith

lemma g8_negInfNorm_le {n : ℕ} {z : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ j, -r ≤ z j) :
    negInfNorm z ≤ r := by
  unfold negInfNorm
  refine (pi_norm_le_iff_of_nonneg hr).2 (fun j => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_min (h j) (by linarith), (min_le_right _ _).trans hr⟩

lemma g8_Pq {n : ℕ} {x s dx ds : Fin n → ℝ} (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (j : Fin n) : PredCorr.Pq x s dx ds j = dx j * ds j := by
  unfold PredCorr.Pq PredCorr.scaledP PredCorr.scaledQ
  have h : Real.sqrt (s j / x j) * Real.sqrt (x j / s j) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg (hs j).le (hx j).le)]
    have hx' := (hx j).ne'
    have hs' := (hs j).ne'
    rw [show s j / x j * (x j / s j) = 1 by field_simp, Real.sqrt_one]
  calc _ = (Real.sqrt (s j / x j) * Real.sqrt (x j / s j)) * (dx j * ds j) := by ring
    _ = _ := by rw [h, one_mul]

lemma g8_theta2 {n : ℕ} (β γ : ℝ) (x s dx ds : Fin n → ℝ)
    (hpos : 0 < β * γ * PredCorr.mu x s) :
    0 < theta2Minus β γ x s dx ds ∧ theta2Minus β γ x s dx ds ≤ 1 ∧
    theta2Minus β γ x s dx ds * negInfNorm (PredCorr.Pq x s dx ds) ≤
      β * γ * PredCorr.mu x s := by
  have hN : 0 ≤ negInfNorm (PredCorr.Pq x s dx ds) := norm_nonneg _
  unfold theta2Minus
  split_ifs with h
  · rw [h]; exact ⟨one_pos, le_rfl, by linarith⟩
  · have hNp : 0 < negInfNorm (PredCorr.Pq x s dx ds) := lt_of_le_of_ne hN (Ne.symm h)
    refine ⟨lt_min one_pos (div_pos hpos hNp), min_le_left _ _, ?_⟩
    calc min 1 (β * γ * PredCorr.mu x s / negInfNorm (PredCorr.Pq x s dx ds)) *
          negInfNorm (PredCorr.Pq x s dx ds)
        ≤ (β * γ * PredCorr.mu x s / negInfNorm (PredCorr.Pq x s dx ds)) *
          negInfNorm (PredCorr.Pq x s dx ds) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hN
      _ = _ := div_mul_cancel₀ _ hNp.ne'

lemma g8_prod_ge {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {β γ : ℝ} {x s : Fin n → ℝ} (hN : InNinfMinus A b c β x s)
    {dx : Fin n → ℝ} {dy : Fin m → ℝ} {ds : Fin n → ℝ}
    (hd : IsNewtonDirection A γ x s dx dy ds) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθN : θ * negInfNorm (PredCorr.Pq x s dx ds) ≤ β * γ * PredCorr.mu x s) (j : Fin n) :
    (1 - β) * ((1 - θ * (1 - γ)) * PredCorr.mu x s) ≤
      lineStep x dx θ j * lineStep s ds θ j := by
  rw [g8_prod hd θ j]
  obtain ⟨⟨hx, hs, -, -⟩, hc⟩ := hN
  have h1 : -(β * PredCorr.mu x s) ≤ x j * s j - PredCorr.mu x s := g8_comp_ge hc j
  have h2 : -negInfNorm (PredCorr.Pq x s dx ds) ≤ dx j * ds j := by
    rw [← g8_Pq hx hs j]; exact g8_comp_ge le_rfl j
  have h3 : θ ^ 2 * (dx j * ds j) ≥ -(θ * (β * γ * PredCorr.mu x s)) := by
    have : θ ^ 2 * (dx j * ds j) ≥ θ ^ 2 * (-negInfNorm (PredCorr.Pq x s dx ds)) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg θ)
    nlinarith [mul_le_mul_of_nonneg_left hθN hθ0]
  have h4 : (1 - θ) * (x j * s j - PredCorr.mu x s) ≥ (1 - θ) * (-(β * PredCorr.mu x s)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

lemma g8_pos_aux (a b da db T : ℝ) (ha : 0 < a) (hT : 0 ≤ T)
    (h : ∀ θ, 0 ≤ θ → θ ≤ T → 0 < (a + θ * da) * (b + θ * db)) : 0 < a + T * da := by
  by_contra hc
  push_neg at hc
  have hdx : da < 0 := by
    by_contra h'; push_neg at h'; nlinarith
  have hθ'0 : 0 ≤ a / (-da) := div_nonneg ha.le (by linarith)
  have hroot : a + a / (-da) * da = 0 := by
    rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hdx.ne]; ring
  have hθ'T : a / (-da) ≤ T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := h _ hθ'0 hθ'T
  rw [hroot, zero_mul] at this
  exact lt_irrefl _ this

lemma g8_pos_of_prod {n : ℕ} {x s dx ds : Fin n → ℝ} (j : Fin n) (hx : 0 < x j) (hs : 0 < s j)
    {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ θ, 0 ≤ θ → θ ≤ T → 0 < lineStep x dx θ j * lineStep s ds θ j) :
    0 < lineStep x dx T j ∧ 0 < lineStep s ds T j := by
  unfold lineStep at *
  refine ⟨g8_pos_aux _ _ _ _ T hx hT h, g8_pos_aux _ (x j) _ (dx j) T hs hT ?_⟩
  intro θ h0 h1; rw [mul_comm]; exact h θ h0 h1

lemma g8_feas {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {γ : ℝ} {x s : Fin n → ℝ} (hAx : A *ᵥ x = b) (hy : ∃ y : Fin m → ℝ, Aᵀ *ᵥ y + s = c)
    {dx : Fin n → ℝ} {dy : Fin m → ℝ} {ds : Fin n → ℝ}
    (hd : IsNewtonDirection A γ x s dx dy ds) (θ : ℝ) :
    A *ᵥ lineStep x dx θ = b ∧ ∃ y : Fin m → ℝ, Aᵀ *ᵥ y + lineStep s ds θ = c := by
  obtain ⟨_, h2, h3⟩ := hd
  obtain ⟨y, hy⟩ := hy
  have ex : lineStep x dx θ = x + θ • dx := by funext j; simp [lineStep]
  have es : lineStep s ds θ = s + θ • ds := by funext j; simp [lineStep]
  refine ⟨?_, y + θ • dy, ?_⟩
  · rw [ex, mulVec_add, mulVec_smul, h2, smul_zero, add_zero, hAx]
  · rw [es, mulVec_add, mulVec_smul]
    rw [show Aᵀ *ᵥ y + θ • (Aᵀ *ᵥ dy) + (s + θ • ds) =
        (Aᵀ *ᵥ y + s) + θ • (Aᵀ *ᵥ dy + ds) by rw [smul_add]; abel, hy, h3, smul_zero, add_zero]

lemma g8_mu_pos {n : ℕ} (hn : 1 ≤ n) {x s : Fin n → ℝ} (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) : 0 < PredCorr.mu x s := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold PredCorr.mu
  apply div_pos _ hnpos
  unfold dotProduct
  calc (0:ℝ) < x ⟨0, hn⟩ * s ⟨0, hn⟩ := mul_pos (hx _) (hs _)
    _ ≤ ∑ i, x i * s i :=
      Finset.single_le_sum (f := fun i => x i * s i)
        (fun i _ => (mul_pos (hx i) (hs i)).le) (Finset.mem_univ _)

lemma g8_mem {m n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {β γ : ℝ} (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hβ0 : 0 < β)
    {x s : Fin n → ℝ} (hN : InNinfMinus A b c β x s)
    {dx : Fin n → ℝ} {dy : Fin m → ℝ} {ds : Fin n → ℝ}
    (hd : IsNewtonDirection A γ x s dx dy ds) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθN : θ * negInfNorm (PredCorr.Pq x s dx ds) ≤ β * γ * PredCorr.mu x s) :
    InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) := by
  have hN' := hN
  obtain ⟨⟨hx, hs, hAx, hy⟩, hc⟩ := hN'
  have hμ := g8_mu_pos hn hx hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNn : 0 ≤ negInfNorm (PredCorr.Pq x s dx ds) := norm_nonneg _
  have hprodpos : ∀ θ', 0 ≤ θ' → θ' ≤ θ → ∀ j,
      0 < lineStep x dx θ' j * lineStep s ds θ' j := by
    intro θ' h0 h1 j
    have hb := g8_prod_ge hN hd h0 (h1.trans hθ1)
      ((mul_le_mul_of_nonneg_right h1 hNn).trans hθN) j
    have : 0 < 1 - θ' * (1 - γ) := by nlinarith
    have : 0 < (1 - β) * ((1 - θ' * (1 - γ)) * PredCorr.mu x s) := by
      apply mul_pos (by linarith); exact mul_pos this hμ
    linarith
  have hpos : ∀ j, 0 < lineStep x dx θ j ∧ 0 < lineStep s ds θ j := fun j =>
    g8_pos_of_prod j (hx j) (hs j) hθ0 (fun θ' h0 h1 => hprodpos θ' h0 h1 j)
  obtain ⟨hf1, hf2⟩ := g8_feas (c := c) hAx hy hd θ
  refine ⟨⟨fun j => (hpos j).1, fun j => (hpos j).2, hf1, hf2⟩, ?_⟩
  have hmu' : PredCorr.mu (lineStep x dx θ) (lineStep s ds θ) =
      (1 - θ * (1 - γ)) * PredCorr.mu x s := by
    unfold PredCorr.mu; rw [g8_dot hn hd θ]; ring
  have hc0 : 0 < 1 - θ * (1 - γ) := by nlinarith
  apply g8_negInfNorm_le
  · rw [hmu']; positivity
  · intro j
    unfold centralityResidual
    rw [hmu']
    have := g8_prod_ge hN hd hθ0 hθ1 hθN j
    linarith

lemma g8_psi_bound {m n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {x s : Fin n → ℝ} (hN : InNinfMinus A b c β x s)
    {dx : Fin n → ℝ} {dy : Fin m → ℝ} {ds : Fin n → ℝ}
    (hd : IsNewtonDirection A γ x s dx dy ds) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθN : θ * negInfNorm (PredCorr.Pq x s dx ds) ≤ β * γ * PredCorr.mu x s) :
    LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θ) (lineStep s ds θ) -
        LinearOptimization.interiorPointPotential (rho n β γ) x s ≤
      -(3 * (n : ℝ) ^ 2 * θ / (β * γ) - n) * Real.log (1 / (1 - β)) := by
  have hmem := g8_mem hn hβ1 hγ0 hγ1 hβ0 hN hd hθ0 hθ1 hθN
  obtain ⟨⟨hx', hs', -, -⟩, -⟩ := hmem
  have hN0 := hN
  obtain ⟨⟨hx, hs, -, -⟩, -⟩ := hN0
  have hμ := g8_mu_pos hn hx hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set μ := PredCorr.mu x s with hμdef
  have hS : x ⬝ᵥ s = n * μ := by rw [hμdef]; unfold PredCorr.mu; field_simp
  have hSpos : 0 < x ⬝ᵥ s := by rw [hS]; positivity
  set cθ := 1 - θ * (1 - γ) with hcθ
  have hc0 : 0 < cθ := by nlinarith
  have hdot : lineStep s ds θ ⬝ᵥ lineStep x dx θ = cθ * (x ⬝ᵥ s) := by
    rw [dotProduct_comm]; exact g8_dot hn hd θ
  have hsx : s ⬝ᵥ x = x ⬝ᵥ s := dotProduct_comm s x
  -- lower bound for the new log sum
  have hnew : ∑ j, Real.log (lineStep x dx θ j) + ∑ j, Real.log (lineStep s ds θ j) ≥
      n * (Real.log (1 - β) + Real.log cθ + Real.log μ) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j, Real.log (1 - β) + Real.log cθ + Real.log μ ≤
        Real.log (lineStep x dx θ j) + Real.log (lineStep s ds θ j) := by
      intro j
      rw [← Real.log_mul (hx' j).ne' (hs' j).ne', ← Real.log_mul (by linarith) hc0.ne',
        ← Real.log_mul (by positivity) hμ.ne']
      apply Real.log_le_log (by have : 0 < 1 - β := by linarith
                                positivity)
      have := g8_prod_ge hN hd hθ0 hθ1 hθN j
      rw [← hcθ] at this
      linarith
    calc (n : ℝ) * (Real.log (1 - β) + Real.log cθ + Real.log μ)
        = ∑ _j : Fin n, (Real.log (1 - β) + Real.log cθ + Real.log μ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => this j)
  -- upper bound for the old log sum
  have hold : ∑ j, Real.log (x j) + ∑ j, Real.log (s j) ≤ n * Real.log μ := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j, Real.log (x j) + Real.log (s j) ≤ Real.log μ + (x j * s j / μ - 1) := by
      intro j
      rw [← Real.log_mul (hx j).ne' (hs j).ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos (mul_pos (hx j) (hs j)) hμ)
      rw [Real.log_div (mul_pos (hx j) (hs j)).ne' hμ.ne'] at h1
      linarith
    calc ∑ j, (Real.log (x j) + Real.log (s j))
        ≤ ∑ j, (Real.log μ + (x j * s j / μ - 1)) := Finset.sum_le_sum (fun j _ => this j)
      _ = n * Real.log μ + ((∑ j, x j * s j) / μ - n) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]; simp
      _ = n * Real.log μ := by
          have : ∑ j, x j * s j = x ⬝ᵥ s := rfl
          rw [this, hS]; field_simp; ring
  have hlogc : Real.log cθ ≤ -(θ * (1 - γ)) := by
    have := Real.log_le_sub_one_of_pos hc0; rw [hcθ] at this; linarith
  have hL : Real.log (1 / (1 - β)) = -Real.log (1 - β) := by
    rw [one_div, Real.log_inv]
  have hLpos : 0 < Real.log (1 / (1 - β)) := by
    apply Real.log_pos; rw [lt_div_iff₀ (by linarith)]; linarith
  have hρn : 0 ≤ rho n β γ - n := by
    unfold rho
    have : 0 < 3 / (β * γ * (1 - γ)) := by
      apply div_pos (by norm_num); apply mul_pos (mul_pos hβ0 hγ0); linarith
    have := mul_pos this hLpos
    nlinarith [sq_nonneg (n : ℝ)]
  have hkey : (rho n β γ - n) * (θ * (1 - γ)) =
      3 * (n : ℝ) ^ 2 * θ / (β * γ) * Real.log (1 / (1 - β)) := by
    unfold rho
    have : (1 - γ) ≠ 0 := by linarith
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_left hlogc hρn
  unfold LinearOptimization.interiorPointPotential
  rw [hdot, hsx, Real.log_mul hc0.ne' hSpos.ne']
  have : -(3 * (n : ℝ) ^ 2 * θ / (β * γ) - n) * Real.log (1 / (1 - β)) =
      -((rho n β γ - n) * (θ * (1 - γ))) + n * Real.log (1 / (1 - β)) := by
    rw [hkey]; ring
  rw [this, hL]
  nlinarith

theorem eq16_core {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (x s : Fin n → ℝ) (hN : InNinfMinus A b c β x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θbar : ℝ)
    (hθmin : ∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θ) (lineStep s ds θ)) :
    LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) -
        LinearOptimization.interiorPointPotential (rho n β γ) x s ≤
      -(3 * (n : ℝ) ^ 2 * theta2Minus β γ x s dx ds / (β * γ) - n) *
        Real.log (1 / (1 - β)) := by
  have hμ := g8_mu_pos hn hN.1.1 hN.1.2.1
  obtain ⟨h0, h1, h2⟩ := g8_theta2 β γ x s dx ds (by positivity)
  have hmem := g8_mem hn hβ1 hγ0 hγ1 hβ0 hN hd h0.le h1 h2
  have := hθmin _ hmem
  have hb := g8_psi_bound hn hβ0 hβ1 hγ0 hγ1 hN hd h0.le h1 h2
  linarith

end AdaptiveStepIPM.Potential

open AdaptiveStepIPM.Potential


theorem solution {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : InNinfMinus A b c β x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θbar : ℝ)
    (hθN : InNinfMinus A b c β (lineStep x dx θbar) (lineStep s ds θbar))
    (hθmin : ∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θ) (lineStep s ds θ)) :
    LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) -
        LinearOptimization.interiorPointPotential (rho n β γ) x s ≤
      -(3 * (n : ℝ) ^ 2 * theta2Minus β γ x s dx ds / (β * γ) - n) *
        Real.log (1 / (1 - β)) := by
  exact eq16_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 x s hN dx dy ds hd θbar hθmin
