-- Prove2me | solution 2 for AdaptiveStepIPM.WideNbhd.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:10.110269+00:00
-- url     : https://prove2.me/submissions/aa05bd4d-0cb1-4359-8459-f702812e185f

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2
import Theorems.Thm_AdaptiveStepIPM_WideNbhd_eq_15

set_option autoImplicit false
open AdaptiveStepIPM.WideNbhd
open Matrix

-- carved from submission 75c8ec96-7de8-4d4e-bf24-7704bcf3738f, lines 502-572

theorem solution {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (t : ℝ) (x s : ℕ → Fin n → ℝ)
    (h0 : (x 0, s 0) ∈ N) (h0t : x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t)
    (hrun : ∀ k, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k → Alg2Step A N γ (x k) (s k) (x (k + 1)) (s (k + 1))) :
    ∃ k ≤ ⌈Real.log 2 * n * t / (2 * β * γ * (1 - γ))⌉₊, x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by
  set K := ⌈Real.log 2 * n * t / (2 * β * γ * (1 - γ))⌉₊ with hK
  by_contra hcon
  push_neg at hcon
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set δ := 4 * β * γ * (1 - γ) / n with hδ
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ 4 * β * γ * (1 - γ) := by
      have : 0 < 1 - γ := by linarith
      positivity
    positivity
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
  have hD : ∀ k, x k ⬝ᵥ s k = n * AdaptiveStepIPM.PredCorr.mu (x k) (s k) := by
    intro k; unfold AdaptiveStepIPM.PredCorr.mu; field_simp
  have hstep : ∀ k, k < K → x (k + 1) ⬝ᵥ s (k + 1) ≤ Real.exp (-δ) * (x k ⬝ᵥ s k) := by
    intro k hk
    have hgt := hcon k hk.le
    have h := AdaptiveStepIPM.WideNbhd.eq_15 hn A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ N hN _ _ _ _ (hrun k hgt)
    have h1 : x (k + 1) ⬝ᵥ s (k + 1) ≤ (1 - δ) * (x k ⬝ᵥ s k) := by
      rw [hD (k + 1), hD k]
      have := mul_le_mul_of_nonneg_left h hnpos.le
      linarith
    have h2 : (1 - δ) * (x k ⬝ᵥ s k) ≤ Real.exp (-δ) * (x k ⬝ᵥ s k) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-δ)]) (by linarith)
    linarith
  have hexp : ∀ k, k ≤ K → x k ⬝ᵥ s k ≤ Real.exp (-δ * k) * (x 0 ⬝ᵥ s 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := hstep k (by omega)
      have h2 := ih (by omega)
      have h3 : Real.exp (-δ) * (x k ⬝ᵥ s k) ≤
          Real.exp (-δ) * (Real.exp (-δ * k) * (x 0 ⬝ᵥ s 0)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      have e : Real.exp (-δ) * (Real.exp (-δ * k) * (x 0 ⬝ᵥ s 0)) =
          Real.exp (-δ * ((k + 1 : ℕ) : ℝ)) * (x 0 ⬝ᵥ s 0) := by
        rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
      linarith
  have hKv : Real.log 2 * n * t / (2 * β * γ * (1 - γ)) ≤ (K : ℝ) := Nat.le_ceil _
  have hδK : 2 * (Real.log 2 * t) ≤ δ * K := by
    have := mul_le_mul_of_nonneg_left hKv hδ0
    have e : δ * (Real.log 2 * n * t / (2 * β * γ * (1 - γ))) = 2 * (Real.log 2 * t) := by
      rw [hδ]
      have : 1 - γ ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hfin := hexp K le_rfl
  have hlt := hcon K le_rfl
  have hb : Real.exp (-δ * K) * (x 0 ⬝ᵥ s 0) ≤ Real.exp (-δ * K) * (2 : ℝ) ^ t :=
    mul_le_mul_of_nonneg_left h0t (Real.exp_pos _).le
  have hc : Real.exp (-δ * K) * (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (-t) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, Real.exp_le_exp]
    linarith
  linarith
