-- Prove2me | solution 1 for AdaptiveStepIPM.WideNbhd.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:24:49.808025+00:00
-- url     : https://prove2.me/submissions/07775974-c974-4258-8ecf-1005d883502c

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

open Matrix

namespace AdaptiveStepIPM.WideNbhd

lemma wn_le_normInf {n : ℕ} (z : Fin n → ℝ) (j : Fin n) : |z j| ≤ normInf z :=
  le_ciSup (f := fun j => |z j|) (Set.finite_range _).bddAbove j

lemma wn_normInf_nonneg {n : ℕ} (z : Fin n → ℝ) : 0 ≤ normInf z :=
  Real.iSup_nonneg (fun j => abs_nonneg (z j))

lemma wn_normInf_le {n : ℕ} (hn : 1 ≤ n) (z : Fin n → ℝ) (C : ℝ) (h : ∀ j, |z j| ≤ C) :
    normInf z ≤ C := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ciSup_le h

lemma wn_abs_min_le (a : ℝ) : |min a 0| ≤ |a| := by
  rcases le_total a 0 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]; simp

lemma wn_abs_min_le' {d C : ℝ} (h : -C ≤ d) (hC : 0 ≤ C) : |min d 0| ≤ C := by
  rcases le_total d 0 with h' | h'
  · rw [min_eq_left h', abs_of_nonpos h']; linarith
  · rw [min_eq_right h']; simpa using hC

lemma wn_ge_of_normInfNeg {n : ℕ} (z : Fin n → ℝ) (C : ℝ) (h : normInfNeg z ≤ C) (j : Fin n) :
    -C ≤ z j := by
  have h1 := le_trans (wn_le_normInf (fun j => min (z j) 0) j) h
  have h2 : -|min (z j) 0| ≤ min (z j) 0 := neg_abs_le _
  have h3 : min (z j) 0 ≤ z j := min_le_left _ _
  linarith

lemma wn_mu_pos {n : ℕ} (hn : 1 ≤ n) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    0 < AdaptiveStepIPM.PredCorr.mu x s := by
  unfold AdaptiveStepIPM.PredCorr.mu
  apply div_pos
  · unfold dotProduct
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun j _ => mul_pos (hx j) (hs j)) Finset.univ_nonempty
  · exact_mod_cast hn

lemma wn_sum_w {n : ℕ} (hn : 1 ≤ n) (x s : Fin n → ℝ) :
    ∑ j, x j * s j = n * AdaptiveStepIPM.PredCorr.mu x s := by
  unfold AdaptiveStepIPM.PredCorr.mu
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ this]; rfl

lemma wn_Pq {n : ℕ} (x s dx ds : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) (j : Fin n) :
    AdaptiveStepIPM.PredCorr.Pq x s dx ds j = dx j * ds j := by
  unfold AdaptiveStepIPM.PredCorr.Pq AdaptiveStepIPM.PredCorr.scaledP AdaptiveStepIPM.PredCorr.scaledQ
  have hx' := hx j; have hs' := hs j
  have : Real.sqrt (s j / x j) * Real.sqrt (x j / s j) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg hs'.le hx'.le)]
    rw [show s j / x j * (x j / s j) = 1 by field_simp]
    simp
  calc Real.sqrt (s j / x j) * dx j * (Real.sqrt (x j / s j) * ds j)
      = (Real.sqrt (s j / x j) * Real.sqrt (x j / s j)) * (dx j * ds j) := by ring
    _ = dx j * ds j := by rw [this, one_mul]

lemma wn_orth {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    ∑ j, dx j * ds j = 0 := by
  have hds : ds = -(Aᵀ *ᵥ dy) := by
    have := hd.2.2; rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have : dx ⬝ᵥ ds = 0 := by
    rw [hds, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, hd.2.1, zero_dotProduct, neg_zero]
  exact this

lemma wn_rsq {n : ℕ} (γ : ℝ) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) (j : Fin n) :
    rvec γ x s j ^ 2 = (γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) ^ 2 / (x j * s j) := by
  unfold rvec
  rw [div_pow, Real.sq_sqrt (mul_pos (hx j) (hs j)).le]

lemma wn_norm2sq {n : ℕ} (z : Fin n → ℝ) : norm2 z ^ 2 = ∑ j, z j ^ 2 := by
  unfold norm2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (z j)))]

/-- the key two-sided bound `|Pq_j| ≤ ‖r‖²/4`. -/
lemma wn_absPq_le {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds)
    (j : Fin n) : |dx j * ds j| ≤ norm2 (rvec γ x s) ^ 2 / 4 := by
  have key : ∀ k, 4 * (dx k * ds k) ≤ rvec γ x s k ^ 2 := by
    intro k
    rw [wn_rsq γ x s hx hs k, ← hd.1 k, le_div_iff₀ (mul_pos (hx k) (hs k))]
    nlinarith [sq_nonneg (s k * dx k - x k * ds k)]
  have hsum : norm2 (rvec γ x s) ^ 2 = ∑ k, (rvec γ x s k ^ 2 - 4 * (dx k * ds k)) := by
    rw [wn_norm2sq, Finset.sum_sub_distrib, ← Finset.mul_sum, wn_orth A x s γ dx dy ds hd]
    ring
  have h1 : rvec γ x s j ^ 2 ≤ norm2 (rvec γ x s) ^ 2 := by
    rw [wn_norm2sq]
    exact Finset.single_le_sum (f := fun k => rvec γ x s k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : rvec γ x s j ^ 2 - 4 * (dx j * ds j) ≤ norm2 (rvec γ x s) ^ 2 := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun k => rvec γ x s k ^ 2 - 4 * (dx k * ds k))
      (fun k _ => by linarith [key k]) (Finset.mem_univ j)
  have h3 := key j
  have h4 := sq_nonneg (rvec γ x s j)
  rw [abs_le]; constructor <;> linarith

lemma wn_norm2_le {n : ℕ} (hn : 1 ≤ n) (γ β : ℝ) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) (hγ0 : 0 < γ) (hγβ : γ ≤ 2 * (1 - β))
    (hw : ∀ j, -(β * AdaptiveStepIPM.PredCorr.mu x s) ≤ x j * s j - AdaptiveStepIPM.PredCorr.mu x s) :
    norm2 (rvec γ x s) ^ 2 ≤ n * AdaptiveStepIPM.PredCorr.mu x s := by
  have hμ := wn_mu_pos hn x s hx hs
  rw [wn_norm2sq, ← wn_sum_w hn]
  apply Finset.sum_le_sum
  intro k _
  rw [wn_rsq γ x s hx hs k, div_le_iff₀ (mul_pos (hx k) (hs k))]
  have hk := hw k
  have hw0 := mul_pos (hx k) (hs k)
  have : γ * AdaptiveStepIPM.PredCorr.mu x s ≤ 2 * (x k * s k) := by nlinarith
  nlinarith [mul_nonneg (le_of_lt (mul_pos hγ0 hμ)) (sub_nonneg.2 this)]

lemma wn_stepBound_props {β γ μ ν t : ℝ} (hν : 0 ≤ ν) (hc : 0 ≤ β * γ * μ)
    (ht : t ∈ Set.Icc (0 : ℝ) (stepBound β γ μ ν)) : t ≤ 1 ∧ t * ν ≤ β * γ * μ := by
  unfold stepBound at ht
  split_ifs at ht with h
  · subst h; exact ⟨ht.2, by simpa using hc⟩
  · have hν' : 0 < ν := lt_of_le_of_ne hν (Ne.symm h)
    refine ⟨le_trans ht.2 (min_le_left _ _), ?_⟩
    have := le_trans ht.2 (min_le_right _ _)
    rw [le_div_iff₀ hν'] at this
    exact this

lemma wn_stepBound_nonneg (β γ μ ν : ℝ) (hc : 0 ≤ β * γ * μ) (hν : 0 ≤ ν) :
    0 ≤ stepBound β γ μ ν := by
  unfold stepBound
  split_ifs
  · norm_num
  · exact le_min zero_le_one (div_nonneg hc hν)

lemma wn_stepBound_anti {β γ μ ν₁ ν₂ : ℝ} (hc : 0 ≤ β * γ * μ) (h0 : 0 ≤ ν₁) (h12 : ν₁ ≤ ν₂) :
    stepBound β γ μ ν₂ ≤ stepBound β γ μ ν₁ := by
  unfold stepBound
  by_cases h1 : ν₁ = 0
  · rw [if_pos h1]; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · have h1' : 0 < ν₁ := lt_of_le_of_ne h0 (Ne.symm h1)
    have h2 : ν₂ ≠ 0 := by intro h; linarith
    rw [if_neg h1, if_neg h2]
    exact min_le_min le_rfl (div_le_div_of_nonneg_left hc h1' h12)

lemma wn_bg_le (β γ : ℝ) (hβ0 : 0 < β) (hγβ : γ ≤ 2 * (1 - β)) : β * γ ≤ 1 / 2 := by
  nlinarith [sq_nonneg (2 * β - 1)]

theorem theta2_lower_bound_core {n m : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : (x, s) ∈ NinfMinus A b c β)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ∧
      normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 ∧
      norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s / 4 ∧
      stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤
        stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ∧
      4 * β * γ / n ≤ stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨⟨hx, hs, _, _⟩, hneg⟩ := hN
  simp only at hx hs hneg
  have hμ := wn_mu_pos hn1 x s hx hs
  set μ := AdaptiveStepIPM.PredCorr.mu x s with hμdef
  set P := AdaptiveStepIPM.PredCorr.Pq x s dx ds with hP
  have hA : normInfNeg P ≤ normInf P := by
    unfold normInfNeg
    exact wn_normInf_le hn1 _ _ (fun j => le_trans (wn_abs_min_le (P j)) (wn_le_normInf P j))
  have hB : normInf P ≤ norm2 (rvec γ x s) ^ 2 / 4 := by
    apply wn_normInf_le hn1
    intro j
    rw [hP, wn_Pq x s dx ds hx hs j]
    exact wn_absPq_le A x s γ hx hs dx dy ds hd j
  have hC : norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * μ / 4 := by
    have := wn_norm2_le hn1 γ β x s hx hs hγ0 hγβ (wn_ge_of_normInfNeg _ _ hneg)
    linarith
  have hc : 0 ≤ β * γ * μ := by positivity
  have hnegnn : 0 ≤ normInfNeg P := wn_normInf_nonneg _
  refine ⟨hA, hB, hC, wn_stepBound_anti hc hnegnn hA, ?_⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hle1 : 4 * β * γ / n ≤ 1 := by
    rw [div_le_one (by linarith)]
    have := wn_bg_le β γ hβ0 hγβ
    linarith
  unfold stepBound
  split_ifs with h
  · exact hle1
  · have hν : 0 < normInf P := lt_of_le_of_ne (wn_normInf_nonneg _) (Ne.symm h)
    refine le_min hle1 ?_
    have hle : normInf P ≤ n * μ / 4 := le_trans hB hC
    calc 4 * β * γ / n = β * γ * μ / (n * μ / 4) := by field_simp
      _ ≤ β * γ * μ / normInf P := div_le_div_of_nonneg_left hc hν hle

lemma wn_pos_of_prod_left {a b da db θ : ℝ} (ha : 0 < a) (hθ : 0 ≤ θ)
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

lemma wn_pos_of_prod {a b da db θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ)
    (h : ∀ t, 0 ≤ t → t ≤ θ → 0 < (a + t * da) * (b + t * db)) :
    0 < a + θ * da ∧ 0 < b + θ * db :=
  ⟨wn_pos_of_prod_left ha hθ h,
    wn_pos_of_prod_left hb hθ (fun t h0 h1 => by rw [mul_comm]; exact h t h0 h1)⟩

lemma wn_prod_step {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds)
    (t : ℝ) (j : Fin n) :
    (x j + t * dx j) * (s j + t * ds j) =
      x j * s j + t * (γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) + t ^ 2 * (dx j * ds j) := by
  rw [← hd.1 j]; ring

lemma wn_mu_step {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds)
    (t : ℝ) :
    AdaptiveStepIPM.PredCorr.mu (x + t • dx) (s + t • ds) =
      (1 - t + t * γ) * AdaptiveStepIPM.PredCorr.mu x s := by
  have h1 : (x + t • dx) ⬝ᵥ (s + t • ds) = ∑ j, (x j * s j +
      t * (γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) + t ^ 2 * (dx j * ds j)) := by
    unfold dotProduct
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← wn_prod_step A x s γ dx dy ds hd t j]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [show AdaptiveStepIPM.PredCorr.mu (x + t • dx) (s + t • ds) =
    ((x + t • dx) ⬝ᵥ (s + t • ds)) / n from rfl, h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, wn_orth A x s γ dx dy ds hd, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, wn_sum_w hn]
  field_simp
  ring

lemma wn_dev_eq {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds)
    (t : ℝ) (j : Fin n) :
    (x + t • dx) j * (s + t • ds) j - AdaptiveStepIPM.PredCorr.mu (x + t • dx) (s + t • ds) =
      (1 - t) * (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) + t ^ 2 * (dx j * ds j) := by
  rw [wn_mu_step hn A x s γ dx dy ds hd t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [wn_prod_step A x s γ dx dy ds hd t j]
  ring

lemma wn_step_feasible {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ1 : β < 1) (x s : Fin n → ℝ)
    (hF : (x, s) ∈ strictlyFeasible A b c)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hmu : ∀ t, 0 ≤ t → t ≤ θ → 0 < 1 - t + t * γ)
    (hlow : ∀ t, 0 ≤ t → t ≤ θ → ∀ j, -(β * ((1 - t + t * γ) * AdaptiveStepIPM.PredCorr.mu x s)) ≤
      (1 - t) * (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) + t ^ 2 * (dx j * ds j)) :
    (x + θ • dx, s + θ • ds) ∈ strictlyFeasible A b c := by
  obtain ⟨hx, hs, hAx, y, hy⟩ := hF
  simp only at hx hs hAx hy
  have hμ := wn_mu_pos hn x s hx hs
  have hprod : ∀ t, 0 ≤ t → t ≤ θ → ∀ j, 0 < (x j + t * dx j) * (s j + t * ds j) := by
    intro t h0 h1 j
    have e := wn_dev_eq hn A x s γ dx dy ds hd t j
    rw [wn_mu_step hn A x s γ dx dy ds hd t] at e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    have hl := hlow t h0 h1 j
    have hm := mul_pos (hmu t h0 h1) hμ
    have : 0 < (1 - β) * ((1 - t + t * γ) * AdaptiveStepIPM.PredCorr.mu x s) :=
      mul_pos (by linarith) hm
    nlinarith
  refine ⟨?_, ?_, ?_, y + θ • dy, ?_⟩
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (wn_pos_of_prod (hx j) (hs j) hθ0 (fun t h0 h1 => hprod t h0 h1 j)).1
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (wn_pos_of_prod (hx j) (hs j) hθ0 (fun t h0 h1 => hprod t h0 h1 j)).2
  · show A *ᵥ (x + θ • dx) = b
    rw [mulVec_add, mulVec_smul, hd.2.1, smul_zero, add_zero]; exact hAx
  · show Aᵀ *ᵥ (y + θ • dy) + (s + θ • ds) = c
    rw [mulVec_add, mulVec_smul]
    have e : Aᵀ *ᵥ y + θ • Aᵀ *ᵥ dy + (s + θ • ds) = (Aᵀ *ᵥ y + s) + θ • (Aᵀ *ᵥ dy + ds) := by
      rw [smul_add]; abel
    rw [e, hy, hd.2.2, smul_zero, add_zero]

lemma wn_dev_bound {β γ μ ν t d0 P : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htν : t * ν ≤ β * γ * μ)
    (h1 : |d0| ≤ β * μ) (h2 : |P| ≤ ν) :
    |(1 - t) * d0 + t ^ 2 * P| ≤ β * ((1 - t + t * γ) * μ) := by
  rw [abs_le] at h1 h2 ⊢
  have a1 : (1 - t) * d0 ≤ (1 - t) * (β * μ) := mul_le_mul_of_nonneg_left h1.2 (by linarith)
  have a2 : (1 - t) * (-(β * μ)) ≤ (1 - t) * d0 := mul_le_mul_of_nonneg_left h1.1 (by linarith)
  have a3 : t ^ 2 * P ≤ t ^ 2 * ν := mul_le_mul_of_nonneg_left h2.2 (sq_nonneg t)
  have a4 : t ^ 2 * (-ν) ≤ t ^ 2 * P := mul_le_mul_of_nonneg_left h2.1 (sq_nonneg t)
  have a5 : t * (t * ν) ≤ t * (β * γ * μ) := mul_le_mul_of_nonneg_left htν ht0
  constructor <;> nlinarith

lemma wn_dev_lower {β γ μ ν t d0 P : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htν : t * ν ≤ β * γ * μ)
    (h1 : -(β * μ) ≤ d0) (h2 : -ν ≤ P) :
    -(β * ((1 - t + t * γ) * μ)) ≤ (1 - t) * d0 + t ^ 2 * P := by
  have a2 : (1 - t) * (-(β * μ)) ≤ (1 - t) * d0 := mul_le_mul_of_nonneg_left h1 (by linarith)
  have a4 : t ^ 2 * (-ν) ≤ t ^ 2 * P := mul_le_mul_of_nonneg_left h2 (sq_nonneg t)
  have a5 : t * (t * ν) ≤ t * (β * γ * μ) := mul_le_mul_of_nonneg_left htν ht0
  nlinarith

lemma wn_mu_fac_pos {γ t : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < 1 - t + t * γ := by
  nlinarith [mul_le_mul_of_nonneg_right ht1 (by linarith : (0 : ℝ) ≤ 1 - γ)]

theorem lemma_5_core {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (x s : Fin n → ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsDirection A x s γ dx dy ds) :
    ((x, s) ∈ Ninf A b c β →
        (∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
            (x + θ • dx, s + θ • ds) ∈ Ninf A b c β) ∧
        ∀ θbar, IsGreatest (admissibleSteps (Ninf A b c β) x s dx ds) θbar →
          stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤ θbar) ∧
      ((x, s) ∈ NinfMinus A b c β →
        (∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
            (x + θ • dx, s + θ • ds) ∈ NinfMinus A b c β) ∧
        ∀ θbar, IsGreatest (admissibleSteps (NinfMinus A b c β) x s dx ds) θbar →
          stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤ θbar) := by
  constructor
  · intro hN
    obtain ⟨hF, hnorm⟩ := hN
    have hF0 := hF
    obtain ⟨hx, hs, -, -⟩ := hF0
    simp only at hx hs hnorm
    have hμ := wn_mu_pos hn x s hx hs
    have hc : 0 ≤ β * γ * AdaptiveStepIPM.PredCorr.mu x s := by positivity
    have hνnn := wn_normInf_nonneg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)
    have hdev0 : ∀ j, |x j * s j - AdaptiveStepIPM.PredCorr.mu x s| ≤ β * AdaptiveStepIPM.PredCorr.mu x s :=
      fun j => le_trans (wn_le_normInf (fun j => x j * s j - AdaptiveStepIPM.PredCorr.mu x s) j) hnorm
    have hP : ∀ j, |dx j * ds j| ≤ normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) := by
      intro j; rw [← wn_Pq x s dx ds hx hs j]; exact wn_le_normInf _ j
    have hall : ∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s)
        (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds))), (x + θ • dx, s + θ • ds) ∈ Ninf A b c β := by
      intro θ hθ
      obtain ⟨hθ1, hθν⟩ := wn_stepBound_props hνnn hc hθ
      have hdev : ∀ t, 0 ≤ t → t ≤ θ → ∀ j,
          |(1 - t) * (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) + t ^ 2 * (dx j * ds j)| ≤
            β * ((1 - t + t * γ) * AdaptiveStepIPM.PredCorr.mu x s) := by
        intro t ht0 htθ j
        exact wn_dev_bound ht0 (by linarith)
          (le_trans (mul_le_mul_of_nonneg_right htθ hνnn) hθν) (hdev0 j) (hP j)
      have hF' := wn_step_feasible hn A b c β γ hβ1 x s hF dx dy ds hd θ hθ.1
        (fun t h0 h1 => wn_mu_fac_pos hγ0 hγ1 h0 (by linarith))
        (fun t h0 h1 j => (abs_le.1 (hdev t h0 h1 j)).1)
      refine ⟨hF', ?_⟩
      show normInf (fun j => (x + θ • dx) j * (s + θ • ds) j -
        AdaptiveStepIPM.PredCorr.mu (x + θ • dx) (s + θ • ds)) ≤
          β * AdaptiveStepIPM.PredCorr.mu (x + θ • dx) (s + θ • ds)
      apply wn_normInf_le hn
      intro j
      rw [wn_dev_eq hn A x s γ dx dy ds hd θ j, wn_mu_step hn A x s γ dx dy ds hd θ]
      exact hdev θ hθ.1 le_rfl j
    refine ⟨hall, fun θbar hG => hG.2 ⟨wn_stepBound_nonneg _ _ _ _ hc hνnn, hall⟩⟩
  · intro hN
    obtain ⟨hF, hnorm⟩ := hN
    have hF0 := hF
    obtain ⟨hx, hs, -, -⟩ := hF0
    simp only at hx hs hnorm
    have hμ := wn_mu_pos hn x s hx hs
    have hc : 0 ≤ β * γ * AdaptiveStepIPM.PredCorr.mu x s := by positivity
    have hνnn := wn_normInf_nonneg (fun j => min (AdaptiveStepIPM.PredCorr.Pq x s dx ds j) 0)
    have hdev0 := wn_ge_of_normInfNeg _ _ hnorm
    have hP : ∀ j, -normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ dx j * ds j := by
      intro j; rw [← wn_Pq x s dx ds hx hs j]; exact wn_ge_of_normInfNeg _ _ le_rfl j
    have hall : ∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s)
        (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
          (x + θ • dx, s + θ • ds) ∈ NinfMinus A b c β := by
      intro θ hθ
      obtain ⟨hθ1, hθν⟩ := wn_stepBound_props hνnn hc hθ
      have hdev : ∀ t, 0 ≤ t → t ≤ θ → ∀ j,
          -(β * ((1 - t + t * γ) * AdaptiveStepIPM.PredCorr.mu x s)) ≤
            (1 - t) * (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) + t ^ 2 * (dx j * ds j) := by
        intro t ht0 htθ j
        exact wn_dev_lower ht0 (by linarith)
          (le_trans (mul_le_mul_of_nonneg_right htθ hνnn) hθν) (hdev0 j) (hP j)
      have hF' := wn_step_feasible hn A b c β γ hβ1 x s hF dx dy ds hd θ hθ.1
        (fun t h0 h1 => wn_mu_fac_pos hγ0 hγ1 h0 (by linarith)) hdev
      refine ⟨hF', ?_⟩
      show normInf (fun j => min ((x + θ • dx) j * (s + θ • ds) j -
        AdaptiveStepIPM.PredCorr.mu (x + θ • dx) (s + θ • ds)) 0) ≤
          β * AdaptiveStepIPM.PredCorr.mu (x + θ • dx) (s + θ • ds)
      apply wn_normInf_le hn
      intro j
      rw [wn_dev_eq hn A x s γ dx dy ds hd θ j, wn_mu_step hn A x s γ dx dy ds hd θ]
      have hm := wn_mu_fac_pos hγ0 hγ1 hθ.1 hθ1
      exact wn_abs_min_le' (hdev θ hθ.1 le_rfl j) (by positivity)
    refine ⟨hall, fun θbar hG => hG.2 ⟨wn_stepBound_nonneg _ _ _ _ hc hνnn, hall⟩⟩

lemma wn_Ninf_sub {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) (h : p ∈ Ninf A b c β) :
    p ∈ NinfMinus A b c β := by
  refine ⟨h.1, le_trans ?_ h.2⟩
  unfold normInfNeg
  exact wn_normInf_le hn _ _ (fun j => le_trans (wn_abs_min_le _)
    (wn_le_normInf (fun j => p.1 j * p.2 j - AdaptiveStepIPM.PredCorr.mu p.1 p.2) j))

lemma wn_four_lt (β γ : ℝ) (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ ≤ 2 * (1 - β)) :
    4 * β * γ * (1 - γ) < 1 := by
  have hg : 0 ≤ γ * (1 - γ) := mul_nonneg hγ0.le (by linarith)
  have h1 : β * (γ * (1 - γ)) ≤ (1 - γ / 2) * (γ * (1 - γ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hg
  have h2 : γ * (1 - γ) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * γ - 1)]
  have h3 : (1 - γ / 2) * (γ * (1 - γ)) ≤ (1 - γ / 2) * (1 / 4) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

lemma wn_sum_one {n : ℕ} (hn : n = 1) (f : Fin n → ℝ) (j : Fin n) : ∑ k, f k = f j := by
  refine Finset.sum_eq_single j (fun k _ hk => absurd (Fin.ext (by omega)) hk) (by simp)

theorem eq_15_core {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (x s x' s' : Fin n → ℝ)
    (hstep : Alg2Step A N γ x s x' s') :
    AdaptiveStepIPM.PredCorr.mu x' s' ≤ (1 - 4 * β * γ * (1 - γ) / n) * AdaptiveStepIPM.PredCorr.mu x s := by
  obtain ⟨dx, dy, ds, θbar, hd, hG, rfl, rfl⟩ := hstep
  have hθ0 : 0 ≤ θbar := hG.1.1
  have hmem : (x, s) ∈ N := by
    have := hG.1.2 0 ⟨le_rfl, hθ0⟩
    simpa using this
  have hmemM : (x, s) ∈ NinfMinus A b c β := by
    rcases hN with rfl | rfl
    · exact wn_Ninf_sub hn A b c β _ hmem
    · exact hmem
  have hF := hmemM.1
  obtain ⟨hx, hs, -, -⟩ := hF
  simp only at hx hs
  have hμ := wn_mu_pos hn x s hx hs
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have key : 4 * β * γ / n ≤ θbar := by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- n = 1
      have hn1 : n = 1 := by omega
      have hnR1 : (n : ℝ) = 1 := by rw [hn1]; norm_num
      rw [hnR1, div_one]
      by_contra hlt
      push_neg at hlt
      have h4 := wn_four_lt β γ hβ0 hγ0 hγ1 hγβ
      have hdev0 : ∀ j, x j * s j - AdaptiveStepIPM.PredCorr.mu x s = 0 := by
        intro j
        have := wn_sum_w hn x s
        rw [wn_sum_one hn1 _ j, hnR1, one_mul] at this
        linarith
      have hP0 : ∀ j, dx j * ds j = 0 := by
        intro j
        have := wn_orth A x s γ dx dy ds hd
        rwa [wn_sum_one hn1 _ j] at this
      have hmu : ∀ t, 0 ≤ t → t ≤ 4 * β * γ → 0 < 1 - t + t * γ := by
        intro t h0 h1
        have : t * (1 - γ) ≤ 4 * β * γ * (1 - γ) := mul_le_mul_of_nonneg_right h1 (by linarith)
        nlinarith
      have hadm : (4 * β * γ) ∈ admissibleSteps N x s dx ds := by
        refine ⟨by positivity, fun θ hθ => ?_⟩
        have hF' := wn_step_feasible hn A b c β γ hβ1 x s hmemM.1 dx dy ds hd θ hθ.1
          (fun t h0 h1 => hmu t h0 (le_trans h1 hθ.2))
          (fun t h0 h1 j => by
            rw [hdev0 j, hP0 j]
            have := mul_pos (hmu t h0 (le_trans h1 hθ.2)) hμ
            have : 0 ≤ β * ((1 - t + t * γ) * AdaptiveStepIPM.PredCorr.mu x s) := by positivity
            linarith)
        have hin : (x + θ • dx, s + θ • ds) ∈ Ninf A b c β := by
          refine ⟨hF', ?_⟩
          show normInf (fun j => (x + θ • dx) j * (s + θ • ds) j -
            AdaptiveStepIPM.PredCorr.mu (x + θ • dx) (s + θ • ds)) ≤
              β * AdaptiveStepIPM.PredCorr.mu (x + θ • dx) (s + θ • ds)
          apply wn_normInf_le hn
          intro j
          rw [wn_dev_eq hn A x s γ dx dy ds hd θ j, wn_mu_step hn A x s γ dx dy ds hd θ,
            hdev0 j, hP0 j]
          have := mul_pos (hmu θ hθ.1 hθ.2) hμ
          simp only [mul_zero, add_zero, abs_zero]
          positivity
        rcases hN with rfl | rfl
        · exact hin
        · exact wn_Ninf_sub hn A b c β _ hin
      have := hG.2 hadm
      linarith
    · rcases hN with rfl | rfl
      · have h5 := ((lemma_5_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 x s dx dy ds hd).1 hmem).2 θbar hG
        have h2' := (theta2_lower_bound_core h2 A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ x s hmemM dx dy ds hd).2.2.2.2
        linarith
      · have h5 := ((lemma_5_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 x s dx dy ds hd).2 hmem).2 θbar hG
        have h2' := theta2_lower_bound_core h2 A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ x s hmemM dx dy ds hd
        linarith [h2'.2.2.2.1, h2'.2.2.2.2]
  rw [wn_mu_step hn A x s γ dx dy ds hd θbar]
  have e : 4 * β * γ * (1 - γ) / n = 4 * β * γ / n * (1 - γ) := by ring
  rw [e]
  have : 4 * β * γ / n * (1 - γ) ≤ θbar * (1 - γ) := mul_le_mul_of_nonneg_right key (by linarith)
  apply mul_le_mul_of_nonneg_right _ hμ.le
  linarith

end AdaptiveStepIPM.WideNbhd

open AdaptiveStepIPM.WideNbhd


theorem solution {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (x s x' s' : Fin n → ℝ)
    (hstep : Alg2Step A N γ x s x' s') :
    AdaptiveStepIPM.PredCorr.mu x' s' ≤ (1 - 4 * β * γ * (1 - γ) / n) * AdaptiveStepIPM.PredCorr.mu x s := by
  exact eq_15_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ N hN x s x' s' hstep
