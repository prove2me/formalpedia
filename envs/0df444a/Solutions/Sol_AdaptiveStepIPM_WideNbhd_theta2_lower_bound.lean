-- Prove2me | solution 1 for AdaptiveStepIPM.WideNbhd.theta2_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:20:13.701839+00:00
-- url     : https://prove2.me/submissions/ac210dbe-6d8b-4551-b20d-1a6007d26a44

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

end AdaptiveStepIPM.WideNbhd

open AdaptiveStepIPM.WideNbhd


theorem solution {n m : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : (x, s) ∈ NinfMinus A b c β)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ∧
      normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 ∧
      norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s / 4 ∧
      stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤
        stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ∧
      4 * β * γ / n ≤ stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) := by
  exact theta2_lower_bound_core hn A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ x s hN dx dy ds hd
