-- Prove2me | solution 1 for AdaptiveStepIPM.Potential.potential_decrease_per_iteration
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:11:27.858993+00:00
-- url     : https://prove2.me/submissions/b2421ce4-d597-4a65-8034-1081ff8177af

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

lemma g8_N_bound {m n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {β γ : ℝ} (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγβ : γ ≤ 2 * (1 - β)) {x s : Fin n → ℝ} (hN : InNinfMinus A b c β x s)
    {dx : Fin n → ℝ} {dy : Fin m → ℝ} {ds : Fin n → ℝ}
    (hd : IsNewtonDirection A γ x s dx dy ds) :
    negInfNorm (PredCorr.Pq x s dx ds) ≤ n * PredCorr.mu x s / 4 := by
  obtain ⟨⟨hx, hs, -, -⟩, hc⟩ := hN
  have hμ := g8_mu_pos hn hx hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set μ := PredCorr.mu x s with hμdef
  have hS : ∑ k, x k * s k = n * μ := by
    have : ∑ k, x k * s k = x ⬝ᵥ s := rfl
    rw [this, hμdef]; unfold PredCorr.mu; field_simp
  have hw : ∀ k, (1 - β) * μ ≤ x k * s k := by
    intro k; have := g8_comp_ge hc k; unfold centralityResidual at this; linarith
  -- T_k and U_k
  have hT : ∀ k, (s k * dx k - x k * ds k) ^ 2 / (4 * (x k * s k)) =
      (γ * μ - x k * s k) ^ 2 / (4 * (x k * s k)) - dx k * ds k := by
    intro k
    rw [← hd.1 k]
    have := (hx k).ne'
    have := (hs k).ne'
    field_simp
    ring
  have hTnn : ∀ k, 0 ≤ (γ * μ - x k * s k) ^ 2 / (4 * (x k * s k)) - dx k * ds k := by
    intro k; rw [← hT k]; have := mul_pos (hx k) (hs k); positivity
  have hU : ∀ k, (γ * μ - x k * s k) ^ 2 / (4 * (x k * s k)) ≤ x k * s k / 4 := by
    intro k
    have hwk := mul_pos (hx k) (hs k)
    rw [div_le_iff₀ (by positivity)]
    have h1 : γ * μ ≤ 2 * (x k * s k) := by nlinarith [hw k]
    nlinarith [mul_nonneg (mul_pos hγ0 hμ).le (by linarith : (0:ℝ) ≤ 2 * (x k * s k) - γ * μ)]
  have h0 := g8_dot_zero hd
  apply g8_negInfNorm_le (by positivity)
  intro j
  rw [g8_Pq hx hs j]
  have hU0 : 0 ≤ (γ * μ - x j * s j) ^ 2 / (4 * (x j * s j)) := by
    have := mul_pos (hx j) (hs j); positivity
  have hsingle : (γ * μ - x j * s j) ^ 2 / (4 * (x j * s j)) - dx j * ds j ≤
      ∑ k, ((γ * μ - x k * s k) ^ 2 / (4 * (x k * s k)) - dx k * ds k) :=
    Finset.single_le_sum (f := fun k => (γ * μ - x k * s k) ^ 2 / (4 * (x k * s k)) - dx k * ds k)
      (fun k _ => hTnn k) (Finset.mem_univ j)
  rw [Finset.sum_sub_distrib, h0, sub_zero] at hsingle
  have hsum : ∑ k, (γ * μ - x k * s k) ^ 2 / (4 * (x k * s k)) ≤ ∑ k, x k * s k / 4 :=
    Finset.sum_le_sum (fun k _ => hU k)
  rw [← Finset.sum_div, hS] at hsum
  linarith

lemma g8_theta_lb {m n : ℕ} (hn2 : 2 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγβ : γ ≤ 2 * (1 - β)) {x s : Fin n → ℝ} (hN : InNinfMinus A b c β x s)
    {dx : Fin n → ℝ} {dy : Fin m → ℝ} {ds : Fin n → ℝ}
    (hd : IsNewtonDirection A γ x s dx dy ds) :
    4 * β * γ / n ≤ theta2Minus β γ x s dx ds := by
  have hn : 1 ≤ n := by omega
  have hNb := g8_N_bound hn hβ1 hγ0 hγβ hN hd
  have hμ := g8_mu_pos hn hN.1.1 hN.1.2.1
  have hnpos : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hβγ : β * γ ≤ 1 / 2 := by nlinarith [sq_nonneg (2 * β - 1)]
  have h1 : 4 * β * γ / n ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hNn : 0 ≤ negInfNorm (PredCorr.Pq x s dx ds) := norm_nonneg _
  unfold theta2Minus
  split_ifs with h
  · exact h1
  · have hNp : 0 < negInfNorm (PredCorr.Pq x s dx ds) := lt_of_le_of_ne hNn (Ne.symm h)
    refine le_min h1 ?_
    rw [div_le_div_iff₀ (by linarith) hNp]
    have := mul_le_mul_of_nonneg_left hNb (by positivity : (0:ℝ) ≤ 4 * β * γ)
    nlinarith

lemma g8_n1_false {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ)
    (c : Fin 1 → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (x s : Fin 1 → ℝ) (hN : InNinfMinus A b c β x s)
    (dx : Fin 1 → ℝ) (dy : Fin m → ℝ) (ds : Fin 1 → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θbar : ℝ)
    (hθN : InNinfMinus A b c β (lineStep x dx θbar) (lineStep s ds θbar))
    (hθmin : ∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential (rho 1 β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential (rho 1 β γ)
          (lineStep x dx θ) (lineStep s ds θ)) : False := by
  obtain ⟨⟨hx, hs, hAx, hy⟩, -⟩ := hN
  have h0 : dx 0 * ds 0 = 0 := by
    have := g8_dot_zero hd; simpa using this
  have hmu : PredCorr.mu x s = x 0 * s 0 := by
    unfold PredCorr.mu; simp [dotProduct]
  have hP : 0 < x 0 * s 0 := mul_pos (hx 0) (hs 0)
  have hprod : ∀ θ, lineStep x dx θ 0 * lineStep s ds θ 0 = (1 - θ * (1 - γ)) * (x 0 * s 0) := by
    intro θ; rw [g8_prod hd θ 0, h0, hmu]; ring
  have hcbar : 0 < 1 - θbar * (1 - γ) := by
    have h := mul_pos (hθN.1.1 0) (hθN.1.2.1 0)
    rw [hprod] at h
    by_contra hc; push_neg at hc
    nlinarith
  set cb := 1 - θbar * (1 - γ) with hcb
  set c' := min cb 1 / 2 with hc'
  have hc'pos : 0 < c' := by rw [hc']; have := lt_min hcbar one_pos; linarith
  have hc'1 : c' ≤ 1 / 2 := by rw [hc']; have := min_le_right cb 1; linarith
  have hc'cb : c' < cb := by rw [hc']; have := min_le_left cb 1; linarith
  have hγ1' : 0 < 1 - γ := by linarith
  set θ' := (1 - c') / (1 - γ) with hθ'
  have hθ'c : 1 - θ' * (1 - γ) = c' := by
    rw [hθ']; field_simp; ring
  have hθ'0 : 0 ≤ θ' := by rw [hθ']; apply div_nonneg (by linarith) hγ1'.le
  -- membership at θ'
  have hpos := g8_pos_of_prod (dx := dx) (ds := ds) 0 (hx 0) (hs 0) hθ'0 (by
    intro θ h0' h1'
    rw [hprod]
    have : c' ≤ 1 - θ * (1 - γ) := by
      rw [← hθ'c]; nlinarith
    have := mul_pos (lt_of_lt_of_le hc'pos this) hP
    linarith)
  have hfin : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim j 0
  obtain ⟨hf1, hf2⟩ := g8_feas (c := c) hAx hy hd θ'
  have hmem : InNinfMinus A b c β (lineStep x dx θ') (lineStep s ds θ') := by
    refine ⟨⟨fun j => by rw [hfin j]; exact hpos.1, fun j => by rw [hfin j]; exact hpos.2,
      hf1, hf2⟩, ?_⟩
    apply g8_negInfNorm_le
    · have : 0 < PredCorr.mu (lineStep x dx θ') (lineStep s ds θ') :=
        g8_mu_pos le_rfl (fun j => by rw [hfin j]; exact hpos.1)
          (fun j => by rw [hfin j]; exact hpos.2)
      positivity
    · intro j
      rw [hfin j]
      unfold centralityResidual PredCorr.mu
      simp [dotProduct]
      exact mul_nonneg hβ0.le (mul_pos hpos.1 hpos.2).le
  have hle := hθmin θ' hmem
  -- potential for n = 1
  have hψ : ∀ θ, 0 < lineStep x dx θ 0 → 0 < lineStep s ds θ 0 →
      LinearOptimization.interiorPointPotential (rho 1 β γ) (lineStep x dx θ) (lineStep s ds θ)
        = (rho 1 β γ - 1) * (Real.log (1 - θ * (1 - γ)) + Real.log (x 0 * s 0)) := by
    intro θ h1 h2
    have hc : 0 < 1 - θ * (1 - γ) := by
      have := mul_pos h1 h2; rw [hprod] at this
      by_contra hc; push_neg at hc; nlinarith
    unfold LinearOptimization.interiorPointPotential
    simp only [dotProduct, Fin.sum_univ_one]
    rw [mul_comm (lineStep s ds θ 0), hprod, Real.log_mul hc.ne' hP.ne']
    have := hprod θ
    rw [← Real.log_mul hc.ne' hP.ne', ← this, Real.log_mul h1.ne' h2.ne']
    ring
  rw [hψ θbar (hθN.1.1 0) (hθN.1.2.1 0), hψ θ' hpos.1 hpos.2, ← hcb, hθ'c] at hle
  have hρ : 0 < rho 1 β γ - 1 := by
    unfold rho
    have hLpos : 0 < Real.log (1 / (1 - β)) := by
      apply Real.log_pos; rw [lt_div_iff₀ (by linarith)]; linarith
    have : 0 < 3 / (β * γ * (1 - γ)) := by
      apply div_pos (by norm_num); apply mul_pos (mul_pos hβ0 hγ0); linarith
    have := mul_pos this hLpos
    push_cast; nlinarith
  have hlog : Real.log c' < Real.log cb := Real.log_lt_log hc'pos hc'cb
  nlinarith

theorem pd_core {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
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
      -(11 * (n : ℝ) * Real.log (1 / (1 - β))) := by
  rcases Nat.lt_or_ge n 2 with h | h2
  · have h1 : n = 1 := by omega
    subst h1
    exact (g8_n1_false A b c β γ hβ0 hβ1 hγ0 hγ1 x s hN dx dy ds hd θbar hθN hθmin).elim
  have hb := eq16_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 x s hN dx dy ds hd θbar hθmin
  have hθ := g8_theta_lb h2 hβ0 hβ1 hγ0 hγβ hN hd
  set θ := theta2Minus β γ x s dx ds
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < Real.log (1 / (1 - β)) := by
    apply Real.log_pos; rw [lt_div_iff₀ (by linarith)]; linarith
  have hβγ : 0 < β * γ := mul_pos hβ0 hγ0
  have hθn : 4 * β * γ ≤ θ * n := by rwa [div_le_iff₀ hnpos] at hθ
  have h12 : 12 * (n : ℝ) ≤ 3 * (n : ℝ) ^ 2 * θ / (β * γ) := by
    rw [le_div_iff₀ hβγ]; nlinarith
  have := mul_le_mul_of_nonneg_right h12 hLpos.le
  nlinarith

end AdaptiveStepIPM.Potential

open AdaptiveStepIPM.Potential


theorem solution {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
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
      -(11 * (n : ℝ) * Real.log (1 / (1 - β))) := by
  exact pd_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ x s hN dx dy ds hd θbar hθN hθmin
