-- Prove2me | solution 1 for ArtinPrimitiveRoots.small_prime_sparse_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T20:27:25.612706+00:00
-- url     : https://prove2.me/submissions/61d216ba-48fe-4810-9013-14175d538847

import Mathlib
import Definitions.Def_ArtinMarkedSquare
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_mean_value
import Theorems.Thm_ArtinPrimitiveRoots_log_phase_progression

section
/-!
# L102M: shared basic definitions and lemmas

`arcCutoff` facts, `ψ_λ = psiL`, `n^{iτ}` helpers, and the Cauchy weight `ω_a`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

lemma natCpow_I_mul (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (I * t) = Complex.exp (I * t * Real.log n) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  have h : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [h]; congr 1; ring

lemma norm_natCpow_I_mul (n : ℕ) (hn : 0 < n) (t : ℝ) : ‖(n : ℂ) ^ (I * t)‖ = 1 := by
  rw [natCpow_I_mul n hn t, show I * (t : ℂ) * ((Real.log n : ℝ) : ℂ) =
    ((t * Real.log n : ℝ) : ℂ) * I by rw [Complex.ofReal_mul]; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_natCpow_I_mul (n : ℕ) (hn : 0 < n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (I * t) := by
  have : (fun t : ℝ => (n : ℂ) ^ (I * t)) = fun t : ℝ => Complex.exp (I * t * Real.log n) := by
    funext t; exact natCpow_I_mul n hn t
  rw [this]; fun_prop

lemma natCpow_I_mul_conj (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (I * t)) = (n : ℂ) ^ (I * (-t : ℝ)) := by
  rw [natCpow_I_mul n hn, natCpow_I_mul n hn, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast; ring

lemma natCpow_I_mul_add (n : ℕ) (hn : 0 < n) (s t : ℝ) :
    (n : ℂ) ^ (I * s) * (n : ℂ) ^ (I * t) = (n : ℂ) ^ (I * (s + t : ℝ)) := by
  rw [natCpow_I_mul n hn, natCpow_I_mul n hn, natCpow_I_mul n hn, ← Complex.exp_add]
  congr 1; push_cast; ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: Gram duality for Dirichlet polynomials at finitely many points

`∑_r |∑_n c_n n^{i t_r}|² ≤ B ∑_n |c_n|²` whenever every Gram row sum
`∑_s |∑_n n^{i(t_r - t_s)}|` is at most `B`.
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset

noncomputable section

/-- **Gram duality.** -/
theorem gram_duality {ι : Type*} (R : Finset ι) (t : ι → ℝ) (F : Finset ℕ)
    (hF : ∀ n ∈ F, 0 < n) (c : ℕ → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ r ∈ R, ∑ s ∈ R, ‖∑ n ∈ F, (n : ℂ) ^ (I * (t r - t s : ℝ))‖ ≤ B) :
    ∑ r ∈ R, ‖∑ n ∈ F, c n * (n : ℂ) ^ (I * t r)‖ ^ 2 ≤ B * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  set y : ι → ℂ := fun r => ∑ n ∈ F, c n * (n : ℂ) ^ (I * t r) with hy
  set z : ℕ → ℂ := fun n => ∑ r ∈ R, y r * (n : ℂ) ^ (I * (-t r : ℝ)) with hz
  set S := ∑ r ∈ R, ‖y r‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  -- S = ∑_n c_n conj(z_n)
  have h1 : (S : ℂ) = ∑ n ∈ F, c n * (starRingEnd ℂ) (z n) := by
    rw [hS]; push_cast
    simp_rw [← Complex.mul_conj']
    rw [hz]; simp only [map_sum, map_mul]
    rw [Finset.sum_congr rfl fun n hn => (Finset.mul_sum _ _ _)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hy]; simp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCpow_I_mul_conj n (hF n hn), neg_neg]
    simp only [map_sum, map_mul]
    ring
  -- ∑ |z_n|² ≤ B S
  have h2 : ∑ n ∈ F, ‖z n‖ ^ 2 ≤ B * S := by
    have e : ((∑ n ∈ F, ‖z n‖ ^ 2 : ℝ) : ℂ) = ∑ r ∈ R, ∑ s ∈ R, y r * (starRingEnd ℂ) (y s) *
        ∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ)) := by
      rw [Complex.ofReal_sum]
      simp_rw [Complex.ofReal_pow, ← Complex.mul_conj']
      rw [hz]; simp only [map_sum, map_mul]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [natCpow_I_mul_conj n (hF n hn), neg_neg]
      have := natCpow_I_mul_add n (hF n hn) (-t r) (t s)
      rw [show (t s - t r : ℝ) = -t r + t s by ring, ← this]
      ring
    have hle : ∑ n ∈ F, ‖z n‖ ^ 2 ≤ ∑ r ∈ R, ∑ s ∈ R, ‖y r‖ * ‖y s‖ *
        ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖ := by
      have h0 : 0 ≤ ∑ n ∈ F, ‖z n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      calc ∑ n ∈ F, ‖z n‖ ^ 2 = ‖((∑ n ∈ F, ‖z n‖ ^ 2 : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg h0]
        _ ≤ _ := by
            rw [e]
            refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
            refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
            rw [norm_mul, norm_mul, Complex.norm_conj]
    -- symmetrize
    have hsym : ∀ r s, ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖ =
        ‖∑ n ∈ F, (n : ℂ) ^ (I * (t r - t s : ℝ))‖ := by
      intro r s
      rw [← Complex.norm_conj, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [natCpow_I_mul_conj n (hF n hn)]
      congr 2; push_cast; ring
    calc ∑ n ∈ F, ‖z n‖ ^ 2
        ≤ ∑ r ∈ R, ∑ s ∈ R, ‖y r‖ * ‖y s‖ * ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖ := hle
      _ ≤ ∑ r ∈ R, ∑ s ∈ R, (‖y r‖ ^ 2 + ‖y s‖ ^ 2) / 2 *
            ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖ := by
          refine sum_le_sum fun r _ => sum_le_sum fun s _ => ?_
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          nlinarith [sq_nonneg (‖y r‖ - ‖y s‖)]
      _ = ∑ r ∈ R, ‖y r‖ ^ 2 * ∑ s ∈ R, ‖∑ n ∈ F, (n : ℂ) ^ (I * (t r - t s : ℝ))‖ := by
          have e1 : ∑ r ∈ R, ∑ s ∈ R, (‖y r‖ ^ 2 + ‖y s‖ ^ 2) / 2 *
              ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖ =
              (∑ r ∈ R, ∑ s ∈ R, ‖y r‖ ^ 2 *
                ‖∑ n ∈ F, (n : ℂ) ^ (I * (t r - t s : ℝ))‖) / 2 +
              (∑ r ∈ R, ∑ s ∈ R, ‖y s‖ ^ 2 *
                ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖) / 2 := by
            rw [sum_div, sum_div, ← sum_add_distrib]
            refine sum_congr rfl fun r _ => ?_
            rw [sum_div, sum_div, ← sum_add_distrib]
            refine sum_congr rfl fun s _ => ?_
            rw [hsym r s]; ring
          rw [e1, Finset.sum_comm (s := R) (t := R) (f := fun r s => ‖y s‖ ^ 2 *
            ‖∑ n ∈ F, (n : ℂ) ^ (I * (t s - t r : ℝ))‖)]
          simp_rw [mul_sum]
          ring
      _ ≤ ∑ r ∈ R, ‖y r‖ ^ 2 * B := by
          refine sum_le_sum fun r hr => ?_
          gcongr
          exact hB r hr
      _ = B * S := by rw [hS, mul_sum]; refine sum_congr rfl fun r _ => ?_; ring
  -- conclude
  have h3 : S ≤ ∑ n ∈ F, ‖c n‖ * ‖z n‖ := by
    have : S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hS0]
    rw [this, h1]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_conj]
  have h4 : (∑ n ∈ F, ‖c n‖ * ‖z n‖) ^ 2 ≤ (∑ n ∈ F, ‖c n‖ ^ 2) * ∑ n ∈ F, ‖z n‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq _ _ _
  have hc0 : 0 ≤ ∑ n ∈ F, ‖c n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h5 : S ^ 2 ≤ (∑ n ∈ F, ‖c n‖ ^ 2) * (B * S) := by
    calc S ^ 2 ≤ (∑ n ∈ F, ‖c n‖ * ‖z n‖) ^ 2 := by gcongr
      _ ≤ _ := h4
      _ ≤ _ := by gcongr
  rcases hS0.lt_or_eq with hpos | hzero
  · have : S * S ≤ (B * ∑ n ∈ F, ‖c n‖ ^ 2) * S := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    exact mul_nonneg hB0 hc0

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the elementary bound for `∑ n^{iΔ}`

`‖∑_{N₁ ≤ n ≤ N₂} n^{iΔ}‖ ≤ 2 N₂/|Δ| + 1 + |Δ| (N₂ - N₁)/N₁` ([21] (5.7), (5.13)).
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory intervalIntegral

noncomputable section

lemma norm_cexp_I_sub_le (a b : ℝ) :
    ‖Complex.exp (I * a) - Complex.exp (I * b)‖ ≤ |a - b| := by
  have h : Complex.exp (I * a) - Complex.exp (I * b) =
      Complex.exp (I * b) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [h, norm_mul, show I * (b : ℂ) = (b : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

lemma realCpow_I_mul (y : ℝ) (hy : 0 < y) (Δ : ℝ) :
    (y : ℂ) ^ (I * Δ) = Complex.exp (I * ((Δ * Real.log y : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]
  congr 1; push_cast; ring

lemma norm_realCpow_sub_le (n y Δ : ℝ) (hn : 0 < n) (hny : n ≤ y) (hy : y ≤ n + 1) :
    ‖(y : ℂ) ^ (I * Δ) - (n : ℂ) ^ (I * Δ)‖ ≤ |Δ| / n := by
  have hy0 : 0 < y := lt_of_lt_of_le hn hny
  rw [realCpow_I_mul y hy0, realCpow_I_mul n hn]
  refine (norm_cexp_I_sub_le _ _).trans ?_
  rw [← mul_sub, abs_mul, ← Real.log_div hy0.ne' hn.ne']
  have h1 : 0 ≤ Real.log (y / n) := Real.log_nonneg (by rw [le_div_iff₀ hn]; linarith)
  have h2 : Real.log (y / n) ≤ y / n - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hn)
  have h3 : y / n - 1 ≤ 1 / n := by
    rw [div_sub_one hn.ne', div_le_div_iff_of_pos_right hn]; linarith
  rw [abs_of_nonneg h1]
  calc |Δ| * Real.log (y / n) ≤ |Δ| * (1 / n) := by gcongr; linarith
    _ = |Δ| / n := by ring

lemma continuous_realCpow_I_mul (Δ : ℝ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ (I * Δ)) (Set.Ioi 0) := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_ofReal_cpow_const y (I * Δ) (Or.inr (ne_of_gt hy))

lemma intervalIntegrable_realCpow (Δ a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (I * Δ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_realCpow_I_mul Δ).mono
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  exact lt_of_lt_of_le ha hy.1

lemma norm_integral_realCpow_le (Δ : ℝ) (hΔ : Δ ≠ 0) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ y in a..b, (y : ℂ) ^ (I * Δ)‖ ≤ 2 * b / |Δ| := by
  have hr : -1 < (I * (Δ : ℂ)).re := by simp
  rw [integral_cpow (Or.inl hr)]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hne : I * (Δ : ℂ) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hn1 : ‖I * (Δ : ℂ) + 1‖ ≥ |Δ| := by
    have : (I * (Δ : ℂ) + 1) = ⟨1, Δ⟩ := by apply Complex.ext <;> simp
    rw [this, Complex.norm_eq_sqrt_sq_add_sq]
    simp only
    rw [ge_iff_le, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hpow : ∀ c : ℝ, 0 < c → ‖(c : ℂ) ^ (I * (Δ : ℂ) + 1)‖ = c := by
    intro c hc
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hc]
    simp
  rw [norm_div]
  have hΔ' : 0 < |Δ| := abs_pos.mpr hΔ
  rw [div_le_div_iff₀ (lt_of_lt_of_le hΔ' hn1) hΔ']
  calc ‖(b : ℂ) ^ (I * (Δ : ℂ) + 1) - (a : ℂ) ^ (I * (Δ : ℂ) + 1)‖ * |Δ|
      ≤ (b + a) * |Δ| := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [hpow b hb, hpow a ha]
    _ ≤ (2 * b) * ‖I * (Δ : ℂ) + 1‖ := by
        have : b + a ≤ 2 * b := by linarith
        calc (b + a) * |Δ| ≤ (2 * b) * |Δ| := by gcongr
          _ ≤ _ := by gcongr

/-- **The elementary exponential-sum bound.** -/
theorem norm_sum_natCpow_le (N₁ N₂ : ℕ) (h1 : 1 ≤ N₁) (h12 : N₁ ≤ N₂) (Δ : ℝ) (hΔ : Δ ≠ 0) :
    ‖∑ n ∈ Icc N₁ N₂, (n : ℂ) ^ (I * Δ)‖ ≤
      2 * N₂ / |Δ| + 1 + |Δ| * (N₂ - N₁) / N₁ := by
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ (I * Δ) with hf
  have hN1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast h1
  have hN12 : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast h12
  set M := N₂ - N₁ with hM
  have hN₂ : N₂ = N₁ + M := by omega
  -- split off the last term
  have hsplit : ∑ n ∈ Icc N₁ N₂, (n : ℂ) ^ (I * Δ) =
      ∑ i ∈ range M, f ((N₁ + i : ℕ) : ℝ) + f (N₂ : ℝ) := by
    have e1 : Icc N₁ N₂ = insert N₂ (Ico N₁ N₂) := by
      ext n; simp only [mem_Icc, mem_insert, mem_Ico]; omega
    rw [e1, sum_insert (by simp), add_comm]
    congr 1
    · rw [Finset.sum_Ico_eq_sum_range]
      refine sum_congr (by rw [hM]) fun i _ => ?_
      simp [hf]
  have hint : ∫ y in (N₁ : ℝ)..(N₂ : ℝ), f y =
      ∑ i ∈ range M, ∫ y in ((N₁ + i : ℕ) : ℝ)..((N₁ + i + 1 : ℕ) : ℝ), f y := by
    have hint' : ∀ k < M, IntervalIntegrable f volume ((fun i => ((N₁ + i : ℕ) : ℝ)) k)
        ((fun i => ((N₁ + i : ℕ) : ℝ)) (k + 1)) := by
      intro k _
      apply intervalIntegrable_realCpow
      · have : (1 : ℝ) ≤ ((N₁ + k : ℕ) : ℝ) := by
          push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
        simp only; linarith
      · simp only; push_cast; linarith
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
      (a := fun i => ((N₁ + i : ℕ) : ℝ)) (n := M) hint'
    simp only [add_zero, ← hN₂, ← add_assoc] at h
    exact h.symm
  have hlocal : ∀ i ∈ range M, ‖f ((N₁ + i : ℕ) : ℝ) -
      ∫ y in ((N₁ + i : ℕ) : ℝ)..((N₁ + i + 1 : ℕ) : ℝ), f y‖ ≤ |Δ| / N₁ := by
    intro i _
    set n : ℝ := ((N₁ + i : ℕ) : ℝ) with hn
    have hn1 : (N₁ : ℝ) ≤ n := by rw [hn]; push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    have hn0 : 0 < n := by linarith
    have hn' : ((N₁ + i + 1 : ℕ) : ℝ) = n + 1 := by rw [hn]; push_cast; ring
    rw [hn']
    have hc : f n = ∫ y in n..(n + 1), f n := by simp
    rw [hc, ← intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_realCpow Δ n (n + 1) hn0 (by linarith))]
    have hb : ∀ y ∈ Set.uIoc n (n + 1), ‖f n - f y‖ ≤ |Δ| / n := by
      intro y hy
      rw [Set.uIoc_of_le (by linarith)] at hy
      rw [norm_sub_rev]
      exact norm_realCpow_sub_le n y Δ hn0 hy.1.le hy.2
    calc ‖∫ y in n..(n + 1), (f n - f y)‖ ≤ |Δ| / n * |n + 1 - n| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = |Δ| / n := by rw [show n + 1 - n = 1 by ring, abs_one, mul_one]
      _ ≤ |Δ| / N₁ := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hn1
  have hfN : ‖f (N₂ : ℝ)‖ = 1 := by
    rw [hf]; simp only
    rw [realCpow_I_mul _ (by linarith), mul_comm, Complex.norm_exp_ofReal_mul_I]
  calc ‖∑ n ∈ Icc N₁ N₂, (n : ℂ) ^ (I * Δ)‖
      = ‖(∫ y in (N₁ : ℝ)..(N₂ : ℝ), f y) + f (N₂ : ℝ) + ∑ i ∈ range M,
          (f ((N₁ + i : ℕ) : ℝ) - ∫ y in ((N₁ + i : ℕ) : ℝ)..((N₁ + i + 1 : ℕ) : ℝ), f y)‖ := by
        rw [hsplit, hint, sum_sub_distrib]; ring_nf
    _ ≤ ‖∫ y in (N₁ : ℝ)..(N₂ : ℝ), f y‖ + ‖f (N₂ : ℝ)‖ + ∑ i ∈ range M,
          ‖f ((N₁ + i : ℕ) : ℝ) - ∫ y in ((N₁ + i : ℕ) : ℝ)..((N₁ + i + 1 : ℕ) : ℝ), f y‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        · exact norm_add_le _ _
        · exact norm_sum_le _ _
    _ ≤ 2 * N₂ / |Δ| + 1 + ∑ i ∈ range M, |Δ| / N₁ := by
        gcongr with i hi
        · exact norm_integral_realCpow_le Δ hΔ _ _ (by linarith) hN12
        · rw [hfN]
        · exact hlocal i hi
    _ = 2 * N₂ / |Δ| + 1 + |Δ| * (N₂ - N₁) / N₁ := by
        rw [sum_const, card_range, nsmul_eq_mul, hM, Nat.cast_sub h12]
        ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the prime polynomial `P_𝒮` and the integer window `[H, 2H]`
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset

noncomputable section

/-- The normalized prime polynomial `P_𝒮(τ) = P⁻¹ ∑_{p ∈ 𝒮} p^{iτ}`. -/
def Pf (𝒮 : Finset ℕ) (P τ : ℝ) : ℂ := ((P : ℂ))⁻¹ * ∑ p ∈ 𝒮, (p : ℂ) ^ (I * τ)

/-- The integers in `[Hn, 2Hn]`. -/
def Fset (Hn : ℝ) : Finset ℕ := (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n => Hn ≤ n)

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: [21] Lemma 5.3, second assertion (sparse sup-mean of `N_β`) — the core estimate

For integer labels `k ∈ 𝒦 ⊆ [-D, D]` and points `t_k ∈ [k, k+1]`,
`∑_{k ∈ 𝒦} |∑_{Hn ≤ n ≤ 2Hn} c_n n^{i t_k}|² ≤ 3 B (Hn + 1) M²`, where `B` bounds every Gram
row sum; the row sums are bounded through the elementary bound for small `|Δ|` and a supplied
bound `E` for large `|Δ|` (in the application, `log_phase_progression`).
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset

noncomputable section

/-- The Gram entry `∑_{Hn ≤ n ≤ 2Hn} n^{iΔ}`. -/
def Gsum (Hn Δ : ℝ) : ℂ := ∑ n ∈ Fset Hn, (n : ℂ) ^ (I * Δ)

lemma Fset_eq_Icc (Hn : ℝ) (hHn : 0 ≤ Hn) : Fset Hn = Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊ := by
  ext n
  simp only [Fset, mem_filter, mem_range, mem_Icc, Nat.ceil_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

lemma mem_Fset {Hn : ℝ} (hHn : 0 ≤ Hn) {n : ℕ} (hn : n ∈ Fset Hn) : Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn := by
  simp only [Fset, mem_filter, mem_range] at hn
  refine ⟨hn.2, ?_⟩
  have : n ≤ ⌊2 * Hn⌋₊ := by omega
  exact (Nat.le_floor_iff (by positivity)).mp this

lemma card_Fset_le (Hn : ℝ) (hHn : 1 ≤ Hn) : ((Fset Hn).card : ℝ) ≤ Hn + 1 := by
  rw [Fset_eq_Icc Hn (by linarith), Nat.card_Icc]
  have h1 : (⌈Hn⌉₊ : ℝ) ≥ Hn := Nat.le_ceil _
  have h2 : (⌊2 * Hn⌋₊ : ℝ) ≤ 2 * Hn := Nat.floor_le (by linarith)
  rcases le_or_gt ⌈Hn⌉₊ (⌊2 * Hn⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith

lemma Fset_pos (Hn : ℝ) (hHn : 0 < Hn) : ∀ n ∈ Fset Hn, 0 < n := by
  intro n hn
  have := (mem_Fset hHn.le hn).1
  have : (0 : ℝ) < n := lt_of_lt_of_le hHn this
  exact_mod_cast this

lemma norm_Gsum_zero (Hn : ℝ) (hHn : 1 ≤ Hn) : ‖Gsum Hn 0‖ ≤ Hn + 1 := by
  unfold Gsum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n ∈ Fset Hn, ‖(n : ℂ) ^ (I * ((0 : ℝ) : ℂ))‖ = 1 := by
    intro n hn; exact norm_natCpow_I_mul n (Fset_pos Hn (by linarith) n hn) 0
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
  exact card_Fset_le Hn hHn

lemma norm_Gsum_small (Hn Δ : ℝ) (hHn : 1 ≤ Hn) (hΔ : Δ ≠ 0) :
    ‖Gsum Hn Δ‖ ≤ 4 * Hn / |Δ| + 1 + |Δ| := by
  unfold Gsum
  rw [Fset_eq_Icc Hn (by linarith)]
  have h1 : (⌈Hn⌉₊ : ℝ) ≥ Hn := Nat.le_ceil _
  have h2 : (⌊2 * Hn⌋₊ : ℝ) ≤ 2 * Hn := Nat.floor_le (by linarith)
  have hΔ' : 0 < |Δ| := abs_pos.mpr hΔ
  rcases le_or_gt ⌈Hn⌉₊ ⌊2 * Hn⌋₊ with h | h
  · have hc1 : 1 ≤ ⌈Hn⌉₊ := by
      have : (1 : ℝ) ≤ ⌈Hn⌉₊ := le_trans hHn h1
      exact_mod_cast this
    refine (norm_sum_natCpow_le _ _ hc1 h Δ hΔ).trans ?_
    have hN1 : (0 : ℝ) < ⌈Hn⌉₊ := by linarith
    have e1 : 2 * (⌊2 * Hn⌋₊ : ℝ) / |Δ| ≤ 4 * Hn / |Δ| := by
      apply div_le_div_of_nonneg_right _ hΔ'.le; linarith
    have e2 : |Δ| * ((⌊2 * Hn⌋₊ : ℝ) - ⌈Hn⌉₊) / ⌈Hn⌉₊ ≤ |Δ| := by
      rw [div_le_iff₀ hN1]
      have : (⌊2 * Hn⌋₊ : ℝ) - ⌈Hn⌉₊ ≤ ⌈Hn⌉₊ := by linarith
      nlinarith
    linarith
  · rw [Finset.Icc_eq_empty (by omega), sum_empty, norm_zero]
    positivity

/-- Integer harmonic sum: for `r, s ∈ [-D, D]`, `∑_{s ≠ r} 1/|r - s| ≤ 2(1 + log(2D))`. -/
lemma sum_inv_abs_int_sub_le (𝒦 : Finset ℤ) (D : ℕ) (hD : ∀ k ∈ 𝒦, |k| ≤ D) (r : ℤ)
    (hr : |r| ≤ D) :
    ∑ s ∈ 𝒦.erase r, 1 / |((r - s : ℤ) : ℝ)| ≤ 2 * (1 + Real.log (2 * D)) := by
  have hH : ∑ d ∈ Icc 1 (2 * D), (1 / (d : ℝ)) ≤ 1 + Real.log (2 * D) := by
    have h := harmonic_le_one_add_log (2 * D)
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  have hsplit : ∑ s ∈ 𝒦.erase r, 1 / |((r - s : ℤ) : ℝ)| =
      ∑ s ∈ (𝒦.erase r).filter (· < r), 1 / |((r - s : ℤ) : ℝ)| +
      ∑ s ∈ (𝒦.erase r).filter (fun s => ¬ s < r), 1 / |((r - s : ℤ) : ℝ)| :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hA : ∑ s ∈ (𝒦.erase r).filter (· < r), 1 / |((r - s : ℤ) : ℝ)| ≤
      ∑ d ∈ Icc 1 (2 * D), (1 / (d : ℝ)) := by
    have himg : ∑ s ∈ (𝒦.erase r).filter (· < r), 1 / |((r - s : ℤ) : ℝ)| =
        ∑ d ∈ ((𝒦.erase r).filter (· < r)).image (fun s => (r - s).toNat), 1 / (d : ℝ) := by
      rw [sum_image]
      · apply sum_congr rfl
        intro s hs
        simp only [mem_filter, mem_erase] at hs
        have hpos : 0 < r - s := by omega
        rw [abs_of_pos (by exact_mod_cast hpos)]
        congr 1
        have : ((r - s).toNat : ℤ) = r - s := Int.toNat_of_nonneg hpos.le
        exact_mod_cast this.symm
      · intro a ha b hb hab
        simp only [coe_filter, mem_erase, Set.mem_ofPred_eq] at ha hb
        simp only at hab
        omega
    rw [himg]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [mem_image, mem_filter, mem_erase] at hd
      obtain ⟨s, ⟨⟨_, hs⟩, hsr⟩, rfl⟩ := hd
      have h1 := hD s hs
      rw [mem_Icc]
      constructor
      · omega
      · rw [abs_le] at h1 hr; omega
    · intro d _ _; positivity
  have hB : ∑ s ∈ (𝒦.erase r).filter (fun s => ¬ s < r), 1 / |((r - s : ℤ) : ℝ)| ≤
      ∑ d ∈ Icc 1 (2 * D), (1 / (d : ℝ)) := by
    have himg : ∑ s ∈ (𝒦.erase r).filter (fun s => ¬ s < r), 1 / |((r - s : ℤ) : ℝ)| =
        ∑ d ∈ ((𝒦.erase r).filter (fun s => ¬ s < r)).image (fun s => (s - r).toNat),
          1 / (d : ℝ) := by
      rw [sum_image]
      · apply sum_congr rfl
        intro s hs
        simp only [mem_filter, mem_erase, not_lt] at hs
        have hpos : 0 < s - r := by omega
        rw [abs_of_neg (by exact_mod_cast (by omega : r - s < 0))]
        congr 1
        have : ((s - r).toNat : ℤ) = s - r := Int.toNat_of_nonneg hpos.le
        push_cast
        have e : ((s - r).toNat : ℝ) = ((s - r : ℤ) : ℝ) := by exact_mod_cast this
        rw [e]; push_cast; ring
      · intro a ha b hb hab
        simp only [coe_filter, mem_erase, Set.mem_ofPred_eq, not_lt] at ha hb
        simp only at hab
        omega
    rw [himg]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [mem_image, mem_filter, mem_erase, not_lt] at hd
      obtain ⟨s, ⟨⟨hsr, hs⟩, hle⟩, rfl⟩ := hd
      have h1 := hD s hs
      rw [mem_Icc]
      constructor
      · omega
      · rw [abs_le] at h1 hr; omega
    · intro d _ _; positivity
  rw [hsplit]; linarith

/-- **Row-sum bound** for 3-separated integer labels. -/
lemma row_bound (Hn T E : ℝ) (hHn : 1 ≤ Hn) (hT : 0 ≤ T) (hE : 0 ≤ E) (𝒦 : Finset ℤ) (D : ℕ)
    (hD : ∀ k ∈ 𝒦, |k| ≤ D) (t : ℤ → ℝ) (ht : ∀ k ∈ 𝒦, (k : ℝ) ≤ t k ∧ t k ≤ k + 1)
    (hsep : ∀ r ∈ 𝒦, ∀ s ∈ 𝒦, r ≠ s → 3 ≤ |r - s|)
    (hlarge : ∀ Δ : ℝ, T ≤ |Δ| → |Δ| ≤ 2 * D + 2 → ‖Gsum Hn Δ‖ ≤ E) (r : ℤ) (hr : r ∈ 𝒦) :
    ∑ s ∈ 𝒦, ‖Gsum Hn (t r - t s)‖ ≤
      (Hn + 1) + 12 * Hn * (1 + Real.log (2 * D)) + 𝒦.card * (1 + T + E) := by
  rw [← add_sum_erase 𝒦 _ hr, sub_self]
  have hdiag := norm_Gsum_zero Hn hHn
  have hoff : ∀ s ∈ 𝒦.erase r, ‖Gsum Hn (t r - t s)‖ ≤
      6 * Hn * (1 / |((r - s : ℤ) : ℝ)|) + (1 + T + E) := by
    intro s hs
    have hsr : s ≠ r := ne_of_mem_erase hs
    have hs' : s ∈ 𝒦 := mem_of_mem_erase hs
    have h3 : (3 : ℝ) ≤ |((r - s : ℤ) : ℝ)| := by
      have := hsep r hr s hs' (Ne.symm hsr)
      rw [← Int.cast_abs]; exact_mod_cast this
    have htr := ht r hr
    have hts := ht s hs'
    have hΔlow : |((r - s : ℤ) : ℝ)| - 1 ≤ |t r - t s| := by
      push_cast
      have := abs_sub_abs_le_abs_sub ((r : ℝ) - s) (t r - t s - ((r : ℝ) - s))
      rw [abs_sub_comm] at this
      have hb : |t r - t s - ((r : ℝ) - s)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [htr.1, htr.2, hts.1, hts.2]
      have e : (r : ℝ) - s + (t r - t s - ((r : ℝ) - s)) = t r - t s := by ring
      calc |(r : ℝ) - s| - 1 ≤ |(r : ℝ) - s| - |t r - t s - ((r : ℝ) - s)| := by linarith
        _ ≤ |(r : ℝ) - s + (t r - t s - ((r : ℝ) - s))| := abs_sub_abs_le_abs_add _ _
        _ = |t r - t s| := by rw [e]
    have hΔpos : 0 < |t r - t s| := by linarith
    have hΔne : t r - t s ≠ 0 := abs_pos.mp hΔpos
    have hΔ23 : (2 / 3) * |((r - s : ℤ) : ℝ)| ≤ |t r - t s| := by linarith
    rcases lt_or_ge |t r - t s| T with hsm | hlg
    · refine (norm_Gsum_small Hn _ hHn hΔne).trans ?_
      have hq : 4 * Hn / |t r - t s| ≤ 6 * Hn * (1 / |((r - s : ℤ) : ℝ)|) := by
        rw [div_le_iff₀ hΔpos]
        have hpos3 : 0 < |((r - s : ℤ) : ℝ)| := by linarith
        calc 4 * Hn = 6 * Hn * (1 / |((r - s : ℤ) : ℝ)|) * ((2 / 3) * |((r - s : ℤ) : ℝ)|) := by
              field_simp; ring
          _ ≤ 6 * Hn * (1 / |((r - s : ℤ) : ℝ)|) * |t r - t s| := by gcongr
      linarith
    · have hup : |t r - t s| ≤ 2 * D + 2 := by
        have h1 := hD r hr
        have h2 := hD s hs'
        rw [abs_le] at h1 h2 ⊢
        have h1' : -(D : ℝ) ≤ r ∧ (r : ℝ) ≤ D := ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
        have h2' : -(D : ℝ) ≤ s ∧ (s : ℝ) ≤ D := ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
        constructor <;> linarith [htr.1, htr.2, hts.1, hts.2]
      refine (hlarge _ hlg hup).trans ?_
      have : 0 ≤ 6 * Hn * (1 / |((r - s : ℤ) : ℝ)|) := by positivity
      linarith
  have hrD : |r| ≤ D := hD r hr
  have hharm := sum_inv_abs_int_sub_le 𝒦 D hD r hrD
  calc ‖Gsum Hn 0‖ + ∑ s ∈ 𝒦.erase r, ‖Gsum Hn (t r - t s)‖
      ≤ (Hn + 1) + ∑ s ∈ 𝒦.erase r, (6 * Hn * (1 / |((r - s : ℤ) : ℝ)|) + (1 + T + E)) :=
        add_le_add hdiag (sum_le_sum hoff)
    _ = (Hn + 1) + (6 * Hn * ∑ s ∈ 𝒦.erase r, (1 / |((r - s : ℤ) : ℝ)|) +
          (𝒦.erase r).card * (1 + T + E)) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ (Hn + 1) + (6 * Hn * (2 * (1 + Real.log (2 * D))) + 𝒦.card * (1 + T + E)) := by
        gcongr
        exact erase_subset r 𝒦
    _ = (Hn + 1) + 12 * Hn * (1 + Real.log (2 * D)) + 𝒦.card * (1 + T + E) := by ring

/-- **Sparse sup-mean, core form** ([21] Lemma 5.3, second assertion). -/
theorem sparse_gram_core (Hn T E M : ℝ) (hHn : 1 ≤ Hn) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (𝒦 : Finset ℤ) (D : ℕ) (hD : ∀ k ∈ 𝒦, |k| ≤ D) (t : ℤ → ℝ)
    (ht : ∀ k ∈ 𝒦, (k : ℝ) ≤ t k ∧ t k ≤ k + 1)
    (hlarge : ∀ Δ : ℝ, T ≤ |Δ| → |Δ| ≤ 2 * D + 2 → ‖Gsum Hn Δ‖ ≤ E)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M) :
    ∑ k ∈ 𝒦, ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * t k)‖ ^ 2 ≤
      3 * ((Hn + 1) + 12 * Hn * (1 + Real.log (2 * D)) + 𝒦.card * (1 + T + E)) *
        ((Hn + 1) * M ^ 2) := by
  set B := (Hn + 1) + 12 * Hn * (1 + Real.log (2 * D)) + 𝒦.card * (1 + T + E) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have hlog : 0 ≤ 1 + Real.log (2 * D) := by
      rcases Nat.eq_zero_or_pos D with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ 2 * D := by
          have : (1 : ℝ) ≤ D := by exact_mod_cast h
          linarith
        linarith [Real.log_nonneg this]
    positivity
  have hcsum : ∑ n ∈ Fset Hn, ‖c n‖ ^ 2 ≤ (Hn + 1) * M ^ 2 := by
    have hM : 0 ≤ M := le_trans (norm_nonneg _) (hc 0)
    calc ∑ n ∈ Fset Hn, ‖c n‖ ^ 2 ≤ ∑ n ∈ Fset Hn, M ^ 2 :=
          sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hc n) 2
      _ = (Fset Hn).card * M ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (Hn + 1) * M ^ 2 := by gcongr; exact card_Fset_le Hn hHn
  -- split by residue mod 3
  have hfib := Finset.sum_fiberwise 𝒦 (fun k : ℤ => (k : ZMod 3))
    (fun k => ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * t k)‖ ^ 2)
  rw [← hfib]
  have hclass : ∀ j : ZMod 3, ∑ k ∈ 𝒦.filter (fun k : ℤ => (k : ZMod 3) = j),
      ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * t k)‖ ^ 2 ≤ B * ((Hn + 1) * M ^ 2) := by
    intro j
    set 𝒦j := 𝒦.filter (fun k : ℤ => (k : ZMod 3) = j) with h𝒦j
    have hsub : 𝒦j ⊆ 𝒦 := filter_subset _ _
    have hsep : ∀ r ∈ 𝒦j, ∀ s ∈ 𝒦j, r ≠ s → 3 ≤ |r - s| := by
      intro r hr s hs hrs
      rw [h𝒦j, mem_filter] at hr hs
      have hmod : ((r : ℤ) : ZMod 3) = ((s : ℤ) : ZMod 3) := hr.2.trans hs.2.symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hmod
      obtain ⟨q, hq⟩ := hmod
      have hq0 : q ≠ 0 := by
        rintro rfl; apply hrs; omega
      rw [show r - s = -(s - r) by ring, abs_neg, hq, abs_mul]
      have : 1 ≤ |q| := Int.one_le_abs hq0
      norm_num; linarith
    have hrow : ∀ r ∈ 𝒦j, ∑ s ∈ 𝒦j, ‖∑ n ∈ Fset Hn, (n : ℂ) ^ (I * (t r - t s : ℝ))‖ ≤ B := by
      intro r hr
      have := row_bound Hn T E hHn hT hE 𝒦j D (fun k hk => hD k (hsub hk)) t
        (fun k hk => ht k (hsub hk)) hsep hlarge r hr
      refine this.trans ?_
      rw [hB]
      gcongr
    refine (gram_duality 𝒦j t (Fset Hn) (Fset_pos Hn (by linarith)) c B hB0 hrow).trans ?_
    gcongr
  calc ∑ j : ZMod 3, ∑ k ∈ 𝒦.filter (fun k : ℤ => (k : ZMod 3) = j),
        ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * t k)‖ ^ 2
      ≤ ∑ j : ZMod 3, B * ((Hn + 1) * M ^ 2) := sum_le_sum fun j _ => hclass j
    _ = 3 * B * ((Hn + 1) * M ^ 2) := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; push_cast; ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the mean value theorems, taken from the cut `dirichlet_mean_value`
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory

theorem mvt (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ)
    (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * t)‖ ^ 2 ≤
      (T₂ - T₁ + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 :=
  (dirichlet_mean_value s N hs c).1 T₁ T₂ hT

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: [21] Lemma 5.3, first assertion (large values of a short prime polynomial are
sparse) — the core estimate

For a set `𝒮` of primes in `[P, 2P]` and `P_𝒮(τ) = P⁻¹ ∑_{p ∈ 𝒮} p^{iτ}`, if the points `τ_k`
(`k ∈ 𝒦`) are `2`-separated in `[-(Z-1), Z-1]` and `|P_𝒮(τ_k)| > η₀`, then
`#𝒦 · 2δ' (η₀/2)^{2j} ≤ P^{-2j} (2Z + 4N(1 + log N)) j^j (2P)^j` with `δ' = η₀/(4 log 2P)`
and any `j` with `N = ⌊(2P)^j⌋`. The proof uses the moment `P_𝒮^j`, the mean value theorem, the
count `#{t' : ∏ t' = ∏ t} ≤ j^j` for prime tuples, and the Lipschitz bound `|P_𝒮'| ≤ 2 log 2P`.
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory

noncomputable section

lemma card_primes_le (P : ℝ) (hP : 1 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P) : (𝒮.card : ℝ) ≤ 2 * P := by
  have hsub : 𝒮 ⊆ Icc ⌈P⌉₊ ⌊2 * P⌋₊ := by
    intro p hp
    obtain ⟨h1, h2⟩ := h𝒮 p hp
    rw [mem_Icc]
    exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  have h1 : (⌈P⌉₊ : ℝ) ≥ P := Nat.le_ceil _
  have h2 : (⌊2 * P⌋₊ : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
  have : ((⌊2 * P⌋₊ + 1 - ⌈P⌉₊ : ℕ) : ℝ) ≤ P + 1 := by
    rcases le_or_gt ⌈P⌉₊ (⌊2 * P⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith
  calc (𝒮.card : ℝ) ≤ ((⌊2 * P⌋₊ + 1 - ⌈P⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ P + 1 := this
    _ ≤ 2 * P := by linarith

lemma pos_of_mem (P : ℝ) (hP : 1 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P) : ∀ p ∈ 𝒮, 0 < p := by
  intro p hp
  have : (0 : ℝ) < p := by linarith [(h𝒮 p hp).1]
  exact_mod_cast this

lemma norm_Pf_le (P : ℝ) (hP : 1 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P) (τ : ℝ) : ‖Pf 𝒮 P τ‖ ≤ 2 := by
  unfold Pf
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h := norm_sum_le 𝒮 fun p => (p : ℂ) ^ (I * (τ : ℂ))
  have e : ∀ p ∈ 𝒮, ‖(p : ℂ) ^ (I * (τ : ℂ))‖ = 1 := fun p hp =>
    norm_natCpow_I_mul p (pos_of_mem P hP 𝒮 h𝒮 p hp) τ
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul, mul_one] at h
  have hc := card_primes_le P hP 𝒮 h𝒮
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith

lemma norm_Pf_sub_le (P : ℝ) (hP : 1 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P) (τ τ' : ℝ) :
    ‖Pf 𝒮 P τ - Pf 𝒮 P τ'‖ ≤ 2 * Real.log (2 * P) * |τ - τ'| := by
  unfold Pf
  rw [← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  have hterm : ∀ p ∈ 𝒮, ‖(p : ℂ) ^ (I * (τ : ℂ)) - (p : ℂ) ^ (I * (τ' : ℂ))‖ ≤
      Real.log (2 * P) * |τ - τ'| := by
    intro p hp
    have hp0 := pos_of_mem P hP 𝒮 h𝒮 p hp
    rw [natCpow_I_mul p hp0, natCpow_I_mul p hp0]
    rw [show I * (τ : ℂ) * ((Real.log p : ℝ) : ℂ) = I * ((τ * Real.log p : ℝ) : ℂ) by
      push_cast; ring, show I * (τ' : ℂ) * ((Real.log p : ℝ) : ℂ) =
      I * ((τ' * Real.log p : ℝ) : ℂ) by push_cast; ring]
    refine (norm_cexp_I_sub_le _ _).trans ?_
    rw [← sub_mul, abs_mul, mul_comm]
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp0)
    rw [abs_of_nonneg hlp]
    gcongr
    exact (h𝒮 p hp).2
  have hc := card_primes_le P hP 𝒮 h𝒮
  calc P⁻¹ * ‖∑ p ∈ 𝒮, ((p : ℂ) ^ (I * (τ : ℂ)) - (p : ℂ) ^ (I * (τ' : ℂ)))‖
      ≤ P⁻¹ * ∑ p ∈ 𝒮, Real.log (2 * P) * |τ - τ'| := by
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = P⁻¹ * 𝒮.card * (Real.log (2 * P) * |τ - τ'|) := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ P⁻¹ * (2 * P) * (Real.log (2 * P) * |τ - τ'|) := by
        have : 0 ≤ Real.log (2 * P) * |τ - τ'| :=
          mul_nonneg (Real.log_nonneg (by linarith)) (abs_nonneg _)
        gcongr
    _ = 2 * Real.log (2 * P) * |τ - τ'| := by field_simp

/-- Prime tuples with the same product: at most `j^j` of them. -/
lemma card_prod_fiber_le (𝒮 : Finset ℕ) (h𝒮 : ∀ p ∈ 𝒮, p.Prime) (j : ℕ) (t : Fin j → ℕ)
    (ht : ∀ l, t l ∈ 𝒮) :
    ((Fintype.piFinset fun _ : Fin j => 𝒮).filter
      (fun t' => ∏ l, t' l = ∏ l, t l)).card ≤ j ^ j := by
  classical
  have hT : ∀ l, (t l).Prime := fun l => h𝒮 _ (ht l)
  have hsub : (Fintype.piFinset fun _ : Fin j => 𝒮).filter (fun t' => ∏ l, t' l = ∏ l, t l) ⊆
      (Finset.univ : Finset (Fin j → Fin j)).image (fun σ => t ∘ σ) := by
    intro t' ht'
    rw [mem_filter, Fintype.mem_piFinset] at ht'
    obtain ⟨hmem, hprod⟩ := ht'
    have hex : ∀ l, ∃ m, t' l = t m := by
      intro l
      have hp : (t' l).Prime := h𝒮 _ (hmem l)
      have hdvd : t' l ∣ ∏ m, t m := by
        rw [← hprod]; exact Finset.dvd_prod_of_mem _ (mem_univ l)
      obtain ⟨m, _, hm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
      exact ⟨m, (Nat.prime_dvd_prime_iff_eq hp (hT m)).mp hm⟩
    choose σ hσ using hex
    rw [mem_image]
    exact ⟨σ, mem_univ _, funext fun l => (hσ l).symm⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

lemma natCpow_I_mul_prod {j : ℕ} (t : Fin j → ℕ) (ht : ∀ l, 0 < t l) (τ : ℝ) :
    ((∏ l, t l : ℕ) : ℂ) ^ (I * τ) = ∏ l, ((t l : ℕ) : ℂ) ^ (I * τ) := by
  have hpos : 0 < ∏ l, t l := Finset.prod_pos fun l _ => ht l
  rw [natCpow_I_mul _ hpos]
  simp_rw [natCpow_I_mul _ (ht _)]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Real.log_prod (fun l _ => by have := ht l; positivity)]
  push_cast
  rw [Finset.mul_sum]

/-- The moment expansion: `(∑_{p ∈ 𝒮} p^{iτ})^j = ∑_n c_n n^{iτ}` with `c_n` the number of
`j`-tuples of `𝒮` with product `n`. -/
lemma sum_pow_eq (𝒮 : Finset ℕ) (h𝒮 : ∀ p ∈ 𝒮, 0 < p) (j : ℕ) (τ : ℝ) :
    (∑ p ∈ 𝒮, (p : ℂ) ^ (I * τ)) ^ j =
      ∑ n ∈ (Fintype.piFinset fun _ : Fin j => 𝒮).image (fun t : Fin j → ℕ => ∏ l, t l),
        (((Fintype.piFinset fun _ : Fin j => 𝒮).filter
          (fun t : Fin j → ℕ => ∏ l, t l = n)).card : ℂ) * ((n : ℕ) : ℂ) ^ (I * τ) := by
  rw [Finset.sum_pow']
  have h1 : ∀ t ∈ (Fintype.piFinset fun _ : Fin j => 𝒮), ∏ i, ((t i : ℕ) : ℂ) ^ (I * τ) =
      ((∏ l, t l : ℕ) : ℂ) ^ (I * τ) := by
    intro t ht
    rw [Fintype.mem_piFinset] at ht
    exact (natCpow_I_mul_prod t (fun l => h𝒮 _ (ht l)) τ).symm
  rw [Finset.sum_congr rfl h1]
  have h2 := Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset fun _ : Fin j => 𝒮)
    (t := (Fintype.piFinset fun _ : Fin j => 𝒮).image (fun t => ∏ l, t l))
    (g := fun t => ∏ l, t l) (f := fun t => ((∏ l, t l : ℕ) : ℂ) ^ (I * τ))
    (fun t ht => mem_image_of_mem _ ht)
  rw [← h2]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_congr rfl (fun t ht => show ((∏ l, t l : ℕ) : ℂ) ^ (I * τ) = ((n : ℕ) : ℂ) ^ (I * τ)
    by rw [(mem_filter.mp ht).2]), sum_const, nsmul_eq_mul]

/-- The moment coefficient bound `∑_n c_n² ≤ j^j #𝒮^j`. -/
lemma sum_fiber_sq_le (𝒮 : Finset ℕ) (h𝒮 : ∀ p ∈ 𝒮, p.Prime) (j : ℕ) :
    ∑ n ∈ (Fintype.piFinset fun _ : Fin j => 𝒮).image (fun t => ∏ l, t l),
      ‖(((Fintype.piFinset fun _ : Fin j => 𝒮).filter (fun t => ∏ l, t l = n)).card : ℂ)‖ ^ 2 ≤
      (j : ℝ) ^ j * (𝒮.card : ℝ) ^ j := by
  set T := Fintype.piFinset fun _ : Fin j => 𝒮 with hT
  have e : ∀ n ∈ T.image (fun t => ∏ l, t l),
      ‖((T.filter (fun t => ∏ l, t l = n)).card : ℂ)‖ ^ 2 =
      ∑ t ∈ T.filter (fun t => ∏ l, t l = n),
        ((T.filter (fun t' => ∏ l, t' l = ∏ l, t l)).card : ℝ) := by
    intro n _
    rw [Complex.norm_natCast, sq]
    rw [Finset.sum_congr rfl (fun t ht => by rw [(mem_filter.mp ht).2]), sum_const, nsmul_eq_mul]
  have h2 := Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image (fun t => ∏ l, t l))
    (g := fun t => ∏ l, t l)
    (f := fun t => ((T.filter (fun t' => ∏ l, t' l = ∏ l, t l)).card : ℝ))
    (fun t ht => mem_image_of_mem _ ht)
  rw [Finset.sum_congr rfl e, h2]
  calc ∑ t ∈ T, ((T.filter (fun t' => ∏ l, t' l = ∏ l, t l)).card : ℝ)
      ≤ ∑ t ∈ T, (j : ℝ) ^ j := by
        refine sum_le_sum fun t ht => ?_
        rw [hT, Fintype.mem_piFinset] at ht
        exact_mod_cast card_prod_fiber_le 𝒮 h𝒮 j t ht
    _ = (j : ℝ) ^ j * (𝒮.card : ℝ) ^ j := by
        rw [sum_const, nsmul_eq_mul, hT, Fintype.card_piFinset]
        simp [Finset.prod_const, mul_comm]

/-- The moment mean value: `∫_{-Z}^{Z} |P_𝒮|^{2j} ≤ P^{-2j} (2Z + 4N(1+log N)) j^j #𝒮^j`. -/
lemma moment_mean (P : ℝ) (hP : 1 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) (j : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∫ τ in (-Z)..Z, ‖Pf 𝒮 P τ‖ ^ (2 * j) ≤
      (P ^ j)⁻¹ ^ 2 * ((2 * Z + 4 * ⌊(2 * P) ^ j⌋₊ * (1 + Real.log ⌊(2 * P) ^ j⌋₊)) *
        ((j : ℝ) ^ j * (𝒮.card : ℝ) ^ j)) := by
  have h𝒮' : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P := fun p hp => (h𝒮 p hp).2
  have hpos := pos_of_mem P hP 𝒮 h𝒮'
  set T := Fintype.piFinset fun _ : Fin j => 𝒮 with hT
  set s := T.image (fun t => ∏ l, t l) with hs
  set c : ℕ → ℂ := fun n => ((T.filter (fun t => ∏ l, t l = n)).card : ℂ) with hc
  set N := ⌊(2 * P) ^ j⌋₊ with hN
  have hsN : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    rw [hs, mem_image] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    rw [hT, Fintype.mem_piFinset] at ht
    constructor
    · exact Finset.prod_pos fun l _ => hpos _ (ht l)
    · apply Nat.le_floor
      push_cast
      calc ∏ l, ((t l : ℕ) : ℝ) ≤ ∏ _l : Fin j, 2 * P :=
            Finset.prod_le_prod (fun l _ => by positivity) (fun l _ => (h𝒮' _ (ht l)).2)
        _ = (2 * P) ^ j := by simp
  have hpt : ∀ τ : ℝ, ‖Pf 𝒮 P τ‖ ^ (2 * j) = (P ^ j)⁻¹ ^ 2 * ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * τ)‖ ^ 2 := by
    intro τ
    have e := sum_pow_eq 𝒮 hpos j τ
    have e2 : Pf 𝒮 P τ ^ j = ((P : ℂ)⁻¹) ^ j * ∑ n ∈ s, c n * (n : ℂ) ^ (I * τ) := by
      unfold Pf; rw [mul_pow, e]
    rw [pow_mul', ← norm_pow, e2, norm_mul, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (by linarith), mul_pow, inv_pow]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  have hmvt := mvt s N hsN c (-Z) Z (by linarith)
  have hsq := sum_fiber_sq_le 𝒮 (fun p hp => (h𝒮 p hp).1) j
  have h0 : 0 ≤ (P ^ j)⁻¹ ^ 2 := by positivity
  calc (P ^ j)⁻¹ ^ 2 * ∫ τ in (-Z)..Z, ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * τ)‖ ^ 2
      ≤ (P ^ j)⁻¹ ^ 2 * ((Z - -Z + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2) := by gcongr
    _ ≤ (P ^ j)⁻¹ ^ 2 * ((2 * Z + 4 * N * (1 + Real.log N)) *
          ((j : ℝ) ^ j * (𝒮.card : ℝ) ^ j)) := by
        have hlog : 0 ≤ 1 + Real.log N := by
          rcases Nat.eq_zero_or_pos N with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ N := by exact_mod_cast h
            linarith [Real.log_nonneg this]
        have hA : 0 ≤ 2 * Z + 4 * N * (1 + Real.log N) := by positivity
        rw [show Z - -Z = 2 * Z by ring]
        gcongr

/-- **Large values of `P_𝒮` are sparse** (core form). -/
theorem large_values_core (P : ℝ) (hP : 2 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) (η₀ : ℝ) (hη : 0 < η₀) (j : ℕ)
    (Z : ℝ) (hZ : 1 ≤ Z) {ι : Type*} (𝒦 : Finset ι) (τ : ι → ℝ)
    (hτ : ∀ k ∈ 𝒦, |τ k| ≤ Z - 1 ∧ η₀ < ‖Pf 𝒮 P (τ k)‖)
    (hsep : ∀ k ∈ 𝒦, ∀ k' ∈ 𝒦, k ≠ k' → 2 ≤ |τ k - τ k'|) :
    (𝒦.card : ℝ) * (2 * (η₀ / (4 * Real.log (2 * P))) * (η₀ / 2) ^ (2 * j)) ≤
      (P ^ j)⁻¹ ^ 2 * ((2 * Z + 4 * ⌊(2 * P) ^ j⌋₊ * (1 + Real.log ⌊(2 * P) ^ j⌋₊)) *
        ((j : ℝ) ^ j * (𝒮.card : ℝ) ^ j)) := by
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have h𝒮' : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P := fun p hp => (h𝒮 p hp).2
  set lg := Real.log (2 * P) with hlg
  have hlg1 : 1 < lg := by
    rw [hlg, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set δ' := η₀ / (4 * lg) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  -- η₀ < 2 (when 𝒦 is nonempty), so δ' < 1/2
  set f : ℝ → ℝ := fun t => ‖Pf 𝒮 P t‖ ^ (2 * j) with hf
  have hfc : Continuous f := by
    rw [hf]; unfold Pf
    refine Continuous.pow (Continuous.norm (continuous_const.mul ?_)) _
    exact continuous_finsetSum _ fun p hp =>
      continuous_natCpow_I_mul p (pos_of_mem P hP1 𝒮 h𝒮' p hp)
  have hf0 : ∀ t, 0 ≤ f t := fun t => by rw [hf]; positivity
  rcases 𝒦.eq_empty_or_nonempty with h𝒦 | ⟨k₀, hk₀⟩
  · simp [h𝒦]; positivity
  have hη2 : η₀ < 2 := lt_of_lt_of_le (hτ k₀ hk₀).2 (norm_Pf_le P hP1 𝒮 h𝒮' _)
  have hδ'1 : δ' < 1 / 2 := by
    rw [hδ', div_lt_iff₀ (by positivity)]; nlinarith
  -- intervals
  set I : ι → Set ℝ := fun k => Set.Icc (τ k - δ') (τ k + δ') with hI
  have hlow : ∀ k ∈ 𝒦, 2 * δ' * (η₀ / 2) ^ (2 * j) ≤ ∫ t in I k, f t := by
    intro k hk
    have hbd : ∀ t ∈ I k, (η₀ / 2) ^ (2 * j) ≤ f t := by
      intro t ht
      rw [hI, Set.mem_Icc] at ht
      have hlip := norm_Pf_sub_le P hP1 𝒮 h𝒮' t (τ k)
      have habs : |t - τ k| ≤ δ' := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have h1 : η₀ / 2 ≤ ‖Pf 𝒮 P t‖ := by
        have h2 : ‖Pf 𝒮 P (τ k)‖ ≤ ‖Pf 𝒮 P t‖ + ‖Pf 𝒮 P t - Pf 𝒮 P (τ k)‖ := by
          have := norm_sub_norm_le (Pf 𝒮 P (τ k)) (Pf 𝒮 P t)
          rw [norm_sub_rev] at this; linarith
        have h3 : 2 * lg * |t - τ k| ≤ η₀ / 2 := by
          calc 2 * lg * |t - τ k| ≤ 2 * lg * δ' := by gcongr
            _ = η₀ / 2 := by rw [hδ']; field_simp; ring
        linarith [(hτ k hk).2]
      rw [hf]; exact pow_le_pow_left₀ (by positivity) h1 _
    have := setIntegral_ge_of_const_le_real (μ := volume) (s := I k) measurableSet_Icc
      (by rw [hI]; simp) hbd hfc.integrableOn_Icc
    rw [hI, Real.volume_real_Icc_of_le (by linarith)] at this
    calc 2 * δ' * (η₀ / 2) ^ (2 * j) = (η₀ / 2) ^ (2 * j) * (τ k + δ' - (τ k - δ')) := by ring
      _ ≤ _ := this
  have hdisj : Set.Pairwise (↑𝒦) (Function.onFun Disjoint I) := by
    intro k hk k' hk' hne
    rw [Function.onFun, hI]
    simp only
    rw [Set.disjoint_left]
    intro t ht ht'
    rw [Set.mem_Icc] at ht ht'
    rcases le_abs'.mp (hsep k hk k' hk' hne) with h | h <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hunion : (⋃ k ∈ 𝒦, I k) ⊆ Set.Icc (-Z) Z := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨k, hk, ht⟩ := ht
    rw [hI, Set.mem_Icc] at ht
    have := (hτ k hk).1
    rw [abs_le] at this
    constructor <;> linarith [ht.1, ht.2]
  have hsum : ∑ k ∈ 𝒦, ∫ t in I k, f t ≤ ∫ t in (-Z)..Z, f t := by
    rw [← integral_biUnion_finset 𝒦 (fun k _ => measurableSet_Icc) hdisj
      (fun k _ => hfc.integrableOn_Icc)]
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_mono_set hfc.integrableOn_Icc
    · exact Filter.Eventually.of_forall fun t => hf0 t
    · exact Filter.Eventually.of_forall hunion
  have hmom := moment_mean P hP1 𝒮 h𝒮 j Z (by linarith)
  calc (𝒦.card : ℝ) * (2 * δ' * (η₀ / 2) ^ (2 * j)) = ∑ k ∈ 𝒦, 2 * δ' * (η₀ / 2) ^ (2 * j) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ 𝒦, ∫ t in I k, f t := sum_le_sum hlow
    _ ≤ ∫ t in (-Z)..Z, f t := hsum
    _ ≤ _ := hmom

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the small-prime split of [21] (5.22) — core form

`∫_{-Z}^{Z} |P_𝒮|²|M|²|N|² ≤ η₀² ∫_{-Z}^{Z} |M|²|N|² + 4 ε_M² ∑_{k ∈ 𝒦} |N(t_k)|²`, where `𝒦` is the
set of integers `k` whose unit interval `[k, k+1]` meets `{|P_𝒮| > η₀}` and `t_k` maximizes `|N|`
on `[k, k+1]`. The witnesses `w_k ∈ [k, k+1]` with `|P_𝒮(w_k)| > η₀` are returned for counting.
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory

noncomputable section

theorem split_mean_core (P : ℝ) (hP : 1 ≤ P) (𝒮 : Finset ℕ)
    (h𝒮 : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P) (η₀ : ℝ) (hη : 0 ≤ η₀) (Z : ℝ) (hZ : 0 ≤ Z)
    (M N : ℝ → ℂ) (hMc : Continuous M) (hNc : Continuous N) (εM : ℝ)
    (hM : ∀ τ : ℝ, |τ| ≤ Z → ‖M τ‖ ≤ εM) :
    ∃ 𝒦 : Finset ℤ, ∃ w t : ℤ → ℝ,
      (∀ k ∈ 𝒦, |k| ≤ ⌈Z⌉₊ + 1 ∧ (k : ℝ) ≤ w k ∧ w k ≤ k + 1 ∧ η₀ < ‖Pf 𝒮 P (w k)‖ ∧
        (k : ℝ) ≤ t k ∧ t k ≤ k + 1) ∧
      ∫ τ in (-Z)..Z, ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 ≤
        η₀ ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) +
          4 * εM ^ 2 * ∑ k ∈ 𝒦, ‖N (t k)‖ ^ 2 := by
  classical
  have hPc : Continuous (Pf 𝒮 P) := by
    unfold Pf
    exact continuous_const.mul (continuous_finsetSum _ fun p hp =>
      continuous_natCpow_I_mul p (pos_of_mem P hP 𝒮 h𝒮 p hp))
  set B : ℕ := ⌈Z⌉₊ with hB
  set 𝒦 : Finset ℤ := (Finset.Icc (-(B : ℤ) - 1) (B : ℤ)).filter
    (fun k : ℤ => ∃ τ ∈ Set.Icc (k : ℝ) (k + 1), η₀ < ‖Pf 𝒮 P τ‖) with h𝒦
  have hex : ∀ k : ℤ, ∃ s ∈ Set.Icc (k : ℝ) (k + 1), IsMaxOn (fun τ => ‖N τ‖) (Set.Icc (k : ℝ) (k + 1)) s :=
    fun k => isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith))
      (hNc.norm.continuousOn)
  choose t ht htmax using hex
  set w : ℤ → ℝ := fun k => if h : ∃ τ ∈ Set.Icc (k : ℝ) (k + 1), η₀ < ‖Pf 𝒮 P τ‖ then
    Classical.choose h else 0 with hw
  refine ⟨𝒦, w, t, ?_, ?_⟩
  · intro k hk
    rw [h𝒦, mem_filter, mem_Icc] at hk
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    have hwk : w k = Classical.choose h3 := by rw [hw]; simp only; rw [dif_pos h3]
    obtain ⟨hmem, hgt⟩ := Classical.choose_spec h3
    refine ⟨?_, ?_, ?_, ?_, (ht k).1, (ht k).2⟩
    · rw [abs_le]; constructor <;> push_cast <;> omega
    · rw [hwk]; exact hmem.1
    · rw [hwk]; exact hmem.2
    · rw [hwk]; exact hgt
  -- pointwise bound
  set g : ℝ → ℝ := fun τ => η₀ ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) +
    ∑ k ∈ 𝒦, (Set.Icc (k : ℝ) (k + 1)).indicator (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ with hg
  have hpt : ∀ τ ∈ Set.uIcc (-Z) Z, ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 ≤ g τ := by
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hτ
    have hτabs : |τ| ≤ Z := abs_le.mpr ⟨hτ.1, hτ.2⟩
    have hnn : 0 ≤ ∑ k ∈ 𝒦, (Set.Icc (k : ℝ) (k + 1)).indicator
        (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ :=
      sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => by positivity) _
    rcases le_or_gt ‖Pf 𝒮 P τ‖ η₀ with hsm | hlg
    · rw [hg]
      have : ‖Pf 𝒮 P τ‖ ^ 2 ≤ η₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsm 2
      have h0 : 0 ≤ ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := by positivity
      nlinarith
    · set k₀ : ℤ := ⌊τ⌋ with hk₀
      have hk₀1 : (k₀ : ℝ) ≤ τ := Int.floor_le τ
      have hk₀2 : τ ≤ k₀ + 1 := (Int.lt_floor_add_one τ).le
      have hk₀mem : k₀ ∈ 𝒦 := by
        rw [h𝒦, mem_filter, mem_Icc]
        refine ⟨⟨?_, ?_⟩, ⟨τ, ⟨hk₀1, hk₀2⟩, hlg⟩⟩
        · have hBZ : Z ≤ (B : ℝ) := Nat.le_ceil Z
          have : (-(B : ℝ)) - 1 < k₀ := by linarith [Int.lt_floor_add_one τ]
          have : ((-(B : ℤ) - 1 : ℤ) : ℝ) < k₀ := by push_cast; linarith
          exact_mod_cast this.le
        · have hBZ : Z ≤ (B : ℝ) := Nat.le_ceil Z
          have : (k₀ : ℝ) ≤ B := by linarith
          exact_mod_cast this
      have hterm : (Set.Icc (k₀ : ℝ) (k₀ + 1)).indicator
          (fun _ => 4 * εM ^ 2 * ‖N (t k₀)‖ ^ 2) τ = 4 * εM ^ 2 * ‖N (t k₀)‖ ^ 2 :=
        Set.indicator_of_mem (show τ ∈ Set.Icc (k₀ : ℝ) (k₀ + 1) from ⟨hk₀1, hk₀2⟩) _
      have hsingle : 4 * εM ^ 2 * ‖N (t k₀)‖ ^ 2 ≤ ∑ k ∈ 𝒦, (Set.Icc (k : ℝ) (k + 1)).indicator
          (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ := by
        rw [← hterm]
        exact single_le_sum (f := fun k : ℤ => (Set.Icc (k : ℝ) (k + 1)).indicator
          (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ)
          (fun k _ => Set.indicator_nonneg (fun _ _ => by positivity) _) hk₀mem
      have hP2 : ‖Pf 𝒮 P τ‖ ^ 2 ≤ 4 := by
        have := norm_Pf_le P hP 𝒮 h𝒮 τ
        nlinarith [norm_nonneg (Pf 𝒮 P τ)]
      have hM2 : ‖M τ‖ ^ 2 ≤ εM ^ 2 := by
        have := hM τ hτabs
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      have hN2 : ‖N τ‖ ^ 2 ≤ ‖N (t k₀)‖ ^ 2 := by
        have := htmax k₀ (show τ ∈ Set.Icc (k₀ : ℝ) (k₀ + 1) from ⟨hk₀1, hk₀2⟩)
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      have hprod : ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 ≤ 4 * εM ^ 2 * ‖N (t k₀)‖ ^ 2 := by
        have h1 : 0 ≤ ‖M τ‖ ^ 2 := sq_nonneg _
        have h2 : 0 ≤ ‖N τ‖ ^ 2 := sq_nonneg _
        calc ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 ≤ 4 * εM ^ 2 * ‖N τ‖ ^ 2 := by
              gcongr
          _ ≤ 4 * εM ^ 2 * ‖N (t k₀)‖ ^ 2 := by gcongr
      rw [hg]
      have : 0 ≤ η₀ ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by positivity
      linarith
  -- integrate
  have hind : ∀ k : ℤ, Integrable ((Set.Icc (k : ℝ) (k + 1)).indicator
      (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2)) := by
    intro k
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp)
  have hMN : Continuous fun τ => ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := by fun_prop
  have hgint : IntervalIntegrable g volume (-Z) Z := by
    rw [hg]
    refine ((hMN.intervalIntegrable _ _).const_mul _).add ?_
    exact (integrable_finsetSum _ fun k _ => hind k).intervalIntegrable
  have hlhs : IntervalIntegrable (fun τ => ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) volume (-Z) Z :=
    (by fun_prop : Continuous fun τ => ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2).intervalIntegrable _ _
  calc ∫ τ in (-Z)..Z, ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2
      ≤ ∫ τ in (-Z)..Z, g τ :=
        intervalIntegral.integral_mono_on (by linarith) hlhs hgint
          (fun τ hτ => hpt τ (by rw [Set.uIcc_of_le (by linarith)]; exact hτ))
    _ = η₀ ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) +
          ∑ k ∈ 𝒦, ∫ τ in (-Z)..Z, (Set.Icc (k : ℝ) (k + 1)).indicator
            (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ := by
        rw [hg, intervalIntegral.integral_add ((hMN.intervalIntegrable _ _).const_mul _)
          ((integrable_finsetSum _ fun k _ => hind k).intervalIntegrable),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum (fun k _ => (hind k).intervalIntegrable)]
    _ ≤ η₀ ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) +
          ∑ k ∈ 𝒦, 4 * εM ^ 2 * ‖N (t k)‖ ^ 2 := by
        gcongr with k hk
        rw [intervalIntegral.integral_of_le (by linarith)]
        calc ∫ τ in Set.Ioc (-Z) Z, (Set.Icc (k : ℝ) (k + 1)).indicator
              (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ
            ≤ ∫ τ, (Set.Icc (k : ℝ) (k + 1)).indicator
              (fun _ => 4 * εM ^ 2 * ‖N (t k)‖ ^ 2) τ :=
              setIntegral_le_integral (hind k) (Filter.Eventually.of_forall fun τ =>
                Set.indicator_nonneg (fun _ _ => by positivity) _)
          _ = 4 * εM ^ 2 * ‖N (t k)‖ ^ 2 := by
              rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le
                (by linarith)]
              simp
    _ = η₀ ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) +
          4 * εM ^ 2 * ∑ k ∈ 𝒦, ‖N (t k)‖ ^ 2 := by rw [mul_sum]

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: asymptotic helper inequalities (in the variable `L = log x → ∞`)
-/

namespace ArtinPrimitiveRoots.L102M

open Real Filter Topology

lemma ev_const_mul_rpow_le (a b c : ℝ) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, c * L ^ a ≤ L ^ b := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (max c 0)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have e : L ^ b = L ^ (b - a) * L ^ a := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [e]
  have : 0 ≤ L ^ a := by positivity
  nlinarith [le_max_left c 0]

lemma log_le_rpow (ε : ℝ) (hε : 0 < ε) (L : ℝ) (hL : 0 ≤ L) :
    Real.log L ≤ L ^ ε / ε := Real.log_le_rpow_div hL hε

lemma ev_const_mul_rpow_log_le (a b c : ℝ) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, c * L ^ a * Real.log L ≤ L ^ b := by
  set ε := (b - a) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h := ev_const_mul_rpow_le (a + ε) b (|c| / ε) (by rw [hε]; linarith)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hle := log_le_rpow ε hε0 L hL0.le
  calc c * L ^ a * Real.log L ≤ |c| * L ^ a * Real.log L := by
        have : 0 ≤ L ^ a * Real.log L := by positivity
        nlinarith [le_abs_self c]
    _ ≤ |c| * L ^ a * (L ^ ε / ε) := by gcongr
    _ = |c| / ε * L ^ (a + ε) := by
        rw [Real.rpow_add hL0]; ring
    _ ≤ L ^ b := hL

lemma ev_const_le_rpow (c ε : ℝ) (hε : 0 < ε) : ∀ᶠ L : ℝ in atTop, c ≤ L ^ ε := by
  filter_upwards [ev_const_mul_rpow_le 0 ε c hε, eventually_gt_atTop (0 : ℝ)] with L hL hL0
  simpa using hL

lemma ev_logpow_le_rpow (r ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, Real.log L ^ r ≤ L ^ ε := by
  have h := isLittleO_log_rpow_rpow_atTop r hε
  have hb := h.bound one_pos
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL1.le) _),
    Real.norm_of_nonneg (by positivity)] at hL
  exact hL

/-- Transfer from `L` to `x` via `L = log x`. -/
lemma ev_log {p : ℝ → Prop} (h : ∀ᶠ L : ℝ in atTop, p L) : ∀ᶠ x : ℝ in atTop, p (Real.log x) :=
  Real.tendsto_log_atTop.eventually h

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the count of large values, explicit form

From `large_values_core` with `j = ⌊log Z'/log 2P⌋`: the number of 2-separated large values is
at most `4P log(2P) (6 + 4 log Z') 16^j j^j / η₀^{2j+1}`, which is `≤ exp(L^{0.95})` when
`L^{0.1} ≤ log P ≤ 3L^{0.2}`, `log Z' ≤ 4L` and `η₀ = L^{-As}`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Filter Topology

noncomputable section

lemma j_bounds (P Z' : ℝ) (hP : 2 ≤ P) (hZ' : 1 ≤ Z') :
    (2 * P) ^ ⌊Real.log Z' / Real.log (2 * P)⌋₊ ≤ Z' ∧
      Z' < (2 * P) ^ (⌊Real.log Z' / Real.log (2 * P)⌋₊ + 1) := by
  set j := ⌊Real.log Z' / Real.log (2 * P)⌋₊ with hj
  have h2P : 1 < 2 * P := by linarith
  have hlog : 0 < Real.log (2 * P) := Real.log_pos h2P
  have hZ0 : 0 < Z' := by linarith
  have hlz : 0 ≤ Real.log Z' := Real.log_nonneg hZ'
  have hq : 0 ≤ Real.log Z' / Real.log (2 * P) := div_nonneg hlz hlog.le
  constructor
  · have h1 : (j : ℝ) ≤ Real.log Z' / Real.log (2 * P) := Nat.floor_le hq
    have h2 : (j : ℝ) * Real.log (2 * P) ≤ Real.log Z' := by
      rwa [le_div_iff₀ hlog] at h1
    rw [← Real.exp_log hZ0, ← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    linarith
  · have h1 : Real.log Z' / Real.log (2 * P) < j + 1 := Nat.lt_floor_add_one _
    have h2 : Real.log Z' < ((j : ℝ) + 1) * Real.log (2 * P) := by
      rwa [div_lt_iff₀ hlog] at h1
    rw [← Real.exp_log hZ0, ← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_lt_exp.mpr
    push_cast; linarith

lemma count_core (P Z' η₀ : ℝ) (j : ℕ) (hP : 2 ≤ P) (hZ' : 1 ≤ Z')
    (hj1 : (2 * P) ^ j ≤ Z') (hj2 : Z' < (2 * P) ^ (j + 1)) (hη : 0 < η₀) (n𝒦 c𝒮 : ℝ)
    (hc0 : 0 ≤ c𝒮) (hc : c𝒮 ≤ 2 * P)
    (h : n𝒦 * (2 * (η₀ / (4 * Real.log (2 * P))) * (η₀ / 2) ^ (2 * j)) ≤
      (P ^ j)⁻¹ ^ 2 * ((2 * Z' + 4 * ⌊(2 * P) ^ j⌋₊ * (1 + Real.log ⌊(2 * P) ^ j⌋₊)) *
        ((j : ℝ) ^ j * c𝒮 ^ j))) :
    n𝒦 ≤ 4 * P * Real.log (2 * P) * (6 + 4 * Real.log Z') * 16 ^ j * (j : ℝ) ^ j /
      η₀ ^ (2 * j + 1) := by
  have hP0 : 0 < P := by linarith
  have h2P : 1 < 2 * P := by linarith
  have hlg : 0 < Real.log (2 * P) := Real.log_pos h2P
  have hZ0 : 0 < Z' := by linarith
  set N := ⌊(2 * P) ^ j⌋₊ with hN
  have hNle : (N : ℝ) ≤ Z' := (Nat.floor_le (by positivity)).trans hj1
  have hlogN : Real.log N ≤ Real.log Z' := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0]; simp; exact Real.log_nonneg hZ'
    · exact Real.log_le_log (by exact_mod_cast h0) hNle
  have hlogZ : 0 ≤ Real.log Z' := Real.log_nonneg hZ'
  have hlogN0 : 0 ≤ 1 + Real.log N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0]; simp
    · have : (1 : ℝ) ≤ N := by exact_mod_cast h0
      linarith [Real.log_nonneg this]
  -- numerator bound
  have hnum : (P ^ j)⁻¹ ^ 2 * ((2 * Z' + 4 * N * (1 + Real.log N)) * ((j : ℝ) ^ j * c𝒮 ^ j)) ≤
      2 * P * 4 ^ j * (6 + 4 * Real.log Z') * (j : ℝ) ^ j := by
    have hA : 2 * Z' + 4 * N * (1 + Real.log N) ≤ Z' * (6 + 4 * Real.log Z') := by
      have : (N : ℝ) * (1 + Real.log N) ≤ Z' * (1 + Real.log Z') := by
        gcongr
      nlinarith
    have hB : c𝒮 ^ j ≤ (2 * P) ^ j := pow_le_pow_left₀ hc0 hc j
    have hjj : 0 ≤ (j : ℝ) ^ j := by positivity
    have hPj : 0 < P ^ j := by positivity
    calc (P ^ j)⁻¹ ^ 2 * ((2 * Z' + 4 * N * (1 + Real.log N)) * ((j : ℝ) ^ j * c𝒮 ^ j))
        ≤ (P ^ j)⁻¹ ^ 2 * ((Z' * (6 + 4 * Real.log Z')) * ((j : ℝ) ^ j * (2 * P) ^ j)) := by
          gcongr
      _ = Z' * (2 ^ j / P ^ j) * (6 + 4 * Real.log Z') * (j : ℝ) ^ j := by
          rw [mul_pow]; field_simp
      _ ≤ (2 * P) ^ (j + 1) * (2 ^ j / P ^ j) * (6 + 4 * Real.log Z') * (j : ℝ) ^ j := by
          gcongr
      _ = 2 * P * 4 ^ j * (6 + 4 * Real.log Z') * (j : ℝ) ^ j := by
          rw [pow_succ, mul_pow, show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
          field_simp
  have hden : 0 < 2 * (η₀ / (4 * Real.log (2 * P))) * (η₀ / 2) ^ (2 * j) := by positivity
  have e : 2 * (η₀ / (4 * Real.log (2 * P))) * (η₀ / 2) ^ (2 * j) =
      η₀ ^ (2 * j + 1) / (2 * Real.log (2 * P) * 4 ^ j) := by
    rw [div_pow, pow_mul, pow_mul, pow_succ]
    field_simp
    ring
  have h' : n𝒦 * (2 * (η₀ / (4 * Real.log (2 * P))) * (η₀ / 2) ^ (2 * j)) ≤
      2 * P * 4 ^ j * (6 + 4 * Real.log Z') * (j : ℝ) ^ j := h.trans hnum
  rw [← le_div_iff₀ hden, e] at h'
  refine h'.trans (le_of_eq ?_)
  rw [show (16 : ℝ) ^ j = 4 ^ j * 4 ^ j by rw [← mul_pow]; norm_num]
  field_simp
  norm_num

/-- The asymptotic count bound. -/
lemma ev_count_le (As : ℝ) (hAs : 0 < As) :
    ∀ᶠ L : ℝ in atTop, ∀ P Z' : ℝ, ∀ j : ℕ, 2 ≤ P → L ^ (0.1 : ℝ) ≤ Real.log P →
      Real.log P ≤ 3 * L ^ (0.2 : ℝ) → 1 ≤ Z' → Real.log Z' ≤ 4 * L → (2 * P) ^ j ≤ Z' →
      4 * P * Real.log (2 * P) * (6 + 4 * Real.log Z') * 16 ^ j * (j : ℝ) ^ j /
        (L ^ (-As)) ^ (2 * j + 1) ≤ Real.exp (L ^ (0.95 : ℝ)) := by
  have e1 := ev_const_mul_rpow_le 0.2 0.95 (8 * 6) (by norm_num)
  have e2 := ev_const_mul_rpow_le 0.9 0.95 (8 * 18) (by norm_num)
  have e3 := ev_const_mul_rpow_log_le 0.9 0.95 (8 * 3.6) (by norm_num)
  have e4 := ev_const_mul_rpow_log_le 0.9 0.95 (8 * (8 * As)) (by norm_num)
  have e5 := ev_const_mul_rpow_log_le 0 0.95 (8 * (1 + As)) (by norm_num)
  have e6 := ev_const_le_rpow (8 * (Real.log 4 + 1 + Real.log 22)) 0.95 (by norm_num)
  filter_upwards [e1, e2, e3, e4, e5, e6, eventually_ge_atTop (2 : ℝ)] with L h1 h2 h3 h4 h5 h6 hL2
    P Z' j hP hP1 hP2 hZ1 hZ2 hj
  have hL0 : 0 < L := by linarith only [hL2]
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
  have hP0 : 0 < P := by linarith only [hP]
  have h2P : 1 < 2 * P := by linarith only [hP]
  have hlg : 0 < Real.log (2 * P) := Real.log_pos h2P
  have hL01 : 1 ≤ L ^ (0.1 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlogP : 0 < Real.log P := lt_of_lt_of_le one_pos (hL01.trans hP1)
  have hlogZ : 0 ≤ Real.log Z' := Real.log_nonneg hZ1
  have hZ0 : 0 < Z' := by linarith only [hZ1]
  -- j ≤ J = 4 L^{0.9}
  set J : ℝ := 4 * L ^ (0.9 : ℝ) with hJ
  have hjJ : (j : ℝ) ≤ J := by
    have h1' : (j : ℝ) * Real.log (2 * P) ≤ Real.log Z' := by
      have := Real.log_le_log (by positivity) hj
      rwa [Real.log_pow] at this
    have h2' : L ^ (0.1 : ℝ) ≤ Real.log (2 * P) :=
      hP1.trans (Real.log_le_log hP0 (by linarith only [hP]))
    have h3' : (j : ℝ) * L ^ (0.1 : ℝ) ≤ 4 * L := by
      have : (j : ℝ) * L ^ (0.1 : ℝ) ≤ (j : ℝ) * Real.log (2 * P) := by gcongr
      linarith only [this, h1', hZ2]
    have e : L = L ^ (0.1 : ℝ) * L ^ (0.9 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [hJ]
    have hpos : 0 < L ^ (0.1 : ℝ) := by positivity
    have e' : 4 * L ^ (0.9 : ℝ) * L ^ (0.1 : ℝ) = 4 * L := by
      rw [mul_assoc, ← Real.rpow_add hL0]; norm_num
    exact le_of_mul_le_mul_right (by linarith only [h3', e']) hpos
  have hJ1 : 1 ≤ J := by
    have : 1 ≤ L ^ (0.9 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    rw [hJ]; linarith only [this]
  -- positivity of the left side
  have hpos : 0 < 4 * P * Real.log (2 * P) * (6 + 4 * Real.log Z') * 16 ^ j * (j : ℝ) ^ j /
      (L ^ (-As)) ^ (2 * j + 1) := by
    have : 0 < (j : ℝ) ^ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h]; simp
      · exact pow_pos (by exact_mod_cast h) j
    positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  -- expand the logarithm
  have hlog : Real.log (4 * P * Real.log (2 * P) * (6 + 4 * Real.log Z') * 16 ^ j * (j : ℝ) ^ j /
      (L ^ (-As)) ^ (2 * j + 1)) = Real.log 4 + Real.log P + Real.log (Real.log (2 * P)) +
        Real.log (6 + 4 * Real.log Z') + j * Real.log 16 + j * Real.log j +
        (2 * j + 1) * (As * Real.log L) := by
    have hj0 : (j : ℝ) ^ j ≠ 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h]; simp
      · exact pow_ne_zero _ (by exact_mod_cast h.ne')
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hj0,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_rpow hL0]
    push_cast; ring
  rw [hlog]
  -- bound the pieces
  have b1 : Real.log (Real.log (2 * P)) ≤ 1 + 3 * L ^ (0.2 : ℝ) := by
    have := Real.log_le_sub_one_of_pos hlg
    have h22 : Real.log (2 * P) = Real.log 2 + Real.log P := Real.log_mul (by norm_num) hP0.ne'
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith only [this]
    linarith only [this, h22, hl2, hP2]
  have b2 : Real.log (6 + 4 * Real.log Z') ≤ Real.log 22 + Real.log L := by
    rw [← Real.log_mul (by norm_num) hL0.ne']
    exact Real.log_le_log (by positivity) (by linarith only [hZ2, hL1])
  have b3 : (j : ℝ) * Real.log 16 ≤ 3 * J := by
    have : Real.log 16 ≤ 3 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith only [this]
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    calc (j : ℝ) * Real.log 16 ≤ (j : ℝ) * 3 := mul_le_mul_of_nonneg_left this hj0
      _ ≤ J * 3 := mul_le_mul_of_nonneg_right hjJ (by norm_num)
      _ = 3 * J := by ring
  have b4 : (j : ℝ) * Real.log j ≤ J * Real.log J := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h]; simp; exact mul_nonneg (by linarith only [hJ1]) (Real.log_nonneg hJ1)
    · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast h
      have hlJ := Real.log_le_log (by linarith only [hj1]) hjJ
      have h0 : 0 ≤ Real.log j := Real.log_nonneg hj1
      calc (j : ℝ) * Real.log j ≤ J * Real.log j := mul_le_mul_of_nonneg_right hjJ h0
        _ ≤ J * Real.log J := mul_le_mul_of_nonneg_left hlJ (by linarith only [hJ1])
  have b5 : J * Real.log J ≤ 5.6 * L ^ (0.9 : ℝ) + 3.6 * L ^ (0.9 : ℝ) * Real.log L := by
    rw [hJ, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL0]
    have : Real.log 4 ≤ 1.4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith only [this]
    have h9 : 0 ≤ L ^ (0.9 : ℝ) := by positivity
    have e : 4 * L ^ (0.9 : ℝ) * (Real.log 4 + 0.9 * Real.log L) =
        4 * Real.log 4 * L ^ (0.9 : ℝ) + 3.6 * L ^ (0.9 : ℝ) * Real.log L := by ring
    rw [e]
    have : 4 * Real.log 4 * L ^ (0.9 : ℝ) ≤ 5.6 * L ^ (0.9 : ℝ) := by
      have := mul_le_mul_of_nonneg_right this h9
      linarith only [this]
    linarith only [this]
  have b6 : (2 * (j : ℝ) + 1) * (As * Real.log L) ≤
      8 * As * L ^ (0.9 : ℝ) * Real.log L + As * Real.log L := by
    have : (2 * (j : ℝ) + 1) ≤ 2 * J + 1 := by linarith only [hjJ]
    have h0 : 0 ≤ As * Real.log L := by positivity
    calc (2 * (j : ℝ) + 1) * (As * Real.log L) ≤ (2 * J + 1) * (As * Real.log L) := by gcongr
      _ = 8 * As * L ^ (0.9 : ℝ) * Real.log L + As * Real.log L := by rw [hJ]; ring
  have hL0' : L ^ (0 : ℝ) = 1 := Real.rpow_zero L
  rw [hL0'] at h5
  have hJe : 3 * J = 12 * L ^ (0.9 : ℝ) := by rw [hJ]; ring
  linarith only [h1, h2, h3, h4, h5, h6, hP2, b1, b2, b3, b4, b5, b6, hJe,
    Real.rpow_nonneg hL0.le (0.9 : ℝ)]

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: [21] Lemma 5.3 in the form used for (5.22)

For `x` large, `x^δ ≤ H_n ≤ x`, coefficients `|c_n| ≤ L^C`, a set `𝒮` of primes in `[P, 2P]`
with `L^{0.1} ≤ log P ≤ 3 L^{0.2}`, `0 ≤ Z ≤ x³`, and any continuous `M` with `|M| ≤ ε_M` on
`[-Z, Z]`:
`∫_{-Z}^{Z} |P_𝒮|² |M|² |N|² ≤ L^{-2A_s} ∫_{-Z}^{Z} |M|² |N|² + 4 ε_M² · 450 H_n² L^{2C+1}`,
`N(τ) = ∑_{H_n ≤ n ≤ 2H_n} c_n n^{iτ}`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Filter Topology Finset

noncomputable section

lemma ev_A3 (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ L : ℝ in atTop,
    3 * Real.exp (L ^ (0.95 : ℝ)) * (1 + Real.exp (L / (2 * Real.log L ^ 2))) ≤
      Real.exp (δ * L) / 2 := by
  have e1 := ev_const_mul_rpow_le 0.95 1 (3 / δ) (by norm_num)
  have e2 : ∀ᶠ L : ℝ in atTop, 3 / (2 * δ) ≤ Real.log L ^ 2 := by
    have := (Real.tendsto_log_atTop.eventually_ge_atTop (3 / (2 * δ) + 1))
    filter_upwards [this] with L hL
    have h1 : 1 ≤ Real.log L := by
      have : 0 < 3 / (2 * δ) := by positivity
      linarith
    nlinarith
  have e3 := (tendsto_id (α := ℝ)).eventually_ge_atTop (3 * Real.log 12 / δ)
  filter_upwards [e1, e2, e3, eventually_ge_atTop (2 : ℝ)] with L h1 h2 h3 hL2
  have hL0 : 0 < L := by linarith
  rw [Real.rpow_one] at h1
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  set u := L / (2 * Real.log L ^ 2) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ δ * L / 3 := by
    rw [hu, div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ δ * L / 3 := by positivity
    have e : δ * L / 3 * (2 * (3 / (2 * δ))) = L := by field_simp
    calc L = δ * L / 3 * (2 * (3 / (2 * δ))) := e.symm
      _ ≤ δ * L / 3 * (2 * Real.log L ^ 2) := by gcongr
  have hA : 1 + Real.exp u ≤ 2 * Real.exp u := by
    have := Real.one_le_exp hu0; linarith
  have hB : L ^ (0.95 : ℝ) ≤ δ * L / 3 := by
    have : 3 / δ * L ^ (0.95 : ℝ) ≤ L := h1
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at this
    linarith
  have hC' : Real.log 12 ≤ δ * L / 3 := by
    simp only [id] at h3
    rw [div_le_iff₀ hδ] at h3
    linarith
  calc 3 * Real.exp (L ^ (0.95 : ℝ)) * (1 + Real.exp u)
      ≤ 3 * Real.exp (L ^ (0.95 : ℝ)) * (2 * Real.exp u) := by gcongr
    _ = Real.exp (Real.log 12 + L ^ (0.95 : ℝ) + u) / 2 := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]; ring
    _ ≤ Real.exp (δ * L) / 2 := by
        gcongr; linarith

lemma ev_A4 (K₁ C₃ : ℝ) : ∀ᶠ L : ℝ in atTop,
    3 * Real.exp (L ^ (0.95 : ℝ)) * (max K₁ 0 * Real.exp (-(L / Real.log L ^ C₃))) ≤ 1 / 2 := by
  set c := Real.log (6 * (max K₁ 0 + 1)) with hc
  have e1 := ev_logpow_le_rpow C₃ 0.025 (by norm_num)
  have e2 := ev_const_mul_rpow_le 0.95 0.975 2 (by norm_num)
  have e3 := ev_const_le_rpow c 0.95 (by norm_num)
  filter_upwards [e1, e2, e3, eventually_ge_atTop (3 : ℝ)] with L h1 h2 h3 hL3
  have hL0 : 0 < L := by linarith
  have hlogL : 1 < Real.log L := by
    rw [Real.lt_log_iff_exp_lt hL0]
    have := Real.exp_one_lt_d9; linarith
  have hlp : 0 < Real.log L ^ C₃ := Real.rpow_pos_of_pos (by linarith) _
  -- L / (log L)^C₃ ≥ L^{0.975} ≥ c + L^{0.95}
  have hq : c + L ^ (0.95 : ℝ) ≤ L / Real.log L ^ C₃ := by
    rw [le_div_iff₀ hlp]
    have hLe : L = L ^ (0.025 : ℝ) * L ^ (0.975 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h4 : c + L ^ (0.95 : ℝ) ≤ L ^ (0.975 : ℝ) := by linarith
    have h5 : 0 ≤ c + L ^ (0.95 : ℝ) := by
      have : 0 ≤ c := Real.log_nonneg (by have := le_max_right K₁ 0; linarith)
      positivity
    calc (c + L ^ (0.95 : ℝ)) * Real.log L ^ C₃ ≤ L ^ (0.975 : ℝ) * L ^ (0.025 : ℝ) := by
          gcongr
      _ = L := by rw [← Real.rpow_add hL0]; norm_num
  have hK : 0 ≤ max K₁ 0 := le_max_right _ _
  calc 3 * Real.exp (L ^ (0.95 : ℝ)) * (max K₁ 0 * Real.exp (-(L / Real.log L ^ C₃)))
      ≤ 3 * Real.exp (L ^ (0.95 : ℝ)) * ((max K₁ 0 + 1) * Real.exp (-(c + L ^ (0.95 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith)) (by positivity)
          (by linarith)
    _ = 3 * (max K₁ 0 + 1) * Real.exp (-c) := by
        rw [neg_add, Real.exp_add]
        have : Real.exp (L ^ (0.95 : ℝ)) * Real.exp (-L ^ (0.95 : ℝ)) = 1 := by
          rw [← Real.exp_add]; simp
        calc 3 * Real.exp (L ^ (0.95 : ℝ)) * ((max K₁ 0 + 1) * (Real.exp (-c) *
              Real.exp (-L ^ (0.95 : ℝ)))) = 3 * (max K₁ 0 + 1) * Real.exp (-c) *
              (Real.exp (L ^ (0.95 : ℝ)) * Real.exp (-L ^ (0.95 : ℝ))) := by ring
          _ = _ := by rw [this, mul_one]
    _ = 1 / 2 := by
        rw [hc, Real.exp_neg, Real.exp_log (by positivity)]
        field_simp; ring

lemma ev_A5 (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ L : ℝ in atTop, L / Real.log L ^ 2 ≤ δ * L := by
  have := (Real.tendsto_log_atTop.eventually_ge_atTop (1 / δ + 1))
  filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have h1 : 1 ≤ Real.log L := by
    have : 0 < 1 / δ := by positivity
    linarith
  rw [div_le_iff₀ (by positivity)]
  have : 1 / δ ≤ Real.log L ^ 2 := by nlinarith
  have hδL : 0 ≤ δ * L := by positivity
  calc L = δ * L * (1 / δ) := by field_simp
    _ ≤ δ * L * Real.log L ^ 2 := by gcongr

open Classical in
/-- `Gsum` agrees with the sum in `log_phase_progression` for `q = 1`. -/
lemma Gsum_eq_lpp (Hn Δ : ℝ) (hHn : 0 ≤ Hn) (J : Set ℝ) (hJ : J = Set.Icc Hn (2 * Hn)) :
    Gsum Hn Δ = ∑ n ∈ (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n => n ≡ 0 [MOD 1]),
      (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * Δ) else 0) := by
  unfold Gsum Fset
  have h1 : (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n => n ≡ 0 [MOD 1]) =
      Finset.range (⌊2 * Hn⌋₊ + 1) := by
    ext n; simp [Nat.modEq_one]
  rw [h1, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_filter, mem_range, hJ, Set.mem_Icc]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨h, h', ?_⟩
    have : n ≤ ⌊2 * Hn⌋₊ := by omega
    exact (Nat.le_floor_iff (by positivity)).mp this
  · rintro ⟨h, h', _⟩; exact ⟨h, h'⟩

/-- **[21] Lemma 5.3, as used in (5.22).** -/
theorem lemma53 (δ C As : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hAs : 0 < As) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hn : ℝ, x ^ δ ≤ Hn → Hn ≤ x →
      ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ Real.log x ^ C) →
      ∀ P : ℝ, 2 ≤ P → Real.log x ^ (0.1 : ℝ) ≤ Real.log P →
      Real.log P ≤ 3 * Real.log x ^ (0.2 : ℝ) →
      ∀ 𝒮 : Finset ℕ, (∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Z : ℝ, 0 ≤ Z → Z ≤ x ^ 3 →
      ∀ M : ℝ → ℂ, Continuous M → ∀ εM : ℝ, (∀ τ : ℝ, |τ| ≤ Z → ‖M τ‖ ≤ εM) →
      ∫ τ in (-Z)..Z, ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 *
          ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ)‖ ^ 2 ≤
        (Real.log x ^ (-As)) ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 *
          ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ)‖ ^ 2) +
        4 * εM ^ 2 * (450 * Hn ^ 2 * Real.log x ^ (2 * C + 1)) := by
  obtain ⟨C₃, K₁, hC₃, hlpp⟩ := log_phase_progression
  obtain ⟨x₁, hx₁⟩ := hlpp 1 one_pos
  have hev : ∀ᶠ x : ℝ in atTop, x₁ ≤ x ∧ 3 ≤ x ∧
      (∀ P Z' : ℝ, ∀ j : ℕ, 2 ≤ P → Real.log x ^ (0.1 : ℝ) ≤ Real.log P →
        Real.log P ≤ 3 * Real.log x ^ (0.2 : ℝ) → 1 ≤ Z' → Real.log Z' ≤ 4 * Real.log x →
        (2 * P) ^ j ≤ Z' →
        4 * P * Real.log (2 * P) * (6 + 4 * Real.log Z') * 16 ^ j * (j : ℝ) ^ j /
          (Real.log x ^ (-As)) ^ (2 * j + 1) ≤ Real.exp (Real.log x ^ (0.95 : ℝ))) ∧
      3 * Real.exp (Real.log x ^ (0.95 : ℝ)) *
        (1 + Real.exp (Real.log x / (2 * Real.log (Real.log x) ^ 2))) ≤
          Real.exp (δ * Real.log x) / 2 ∧
      3 * Real.exp (Real.log x ^ (0.95 : ℝ)) * (max K₁ 0 *
        Real.exp (-(Real.log x / Real.log (Real.log x) ^ C₃))) ≤ 1 / 2 ∧
      Real.log x / Real.log (Real.log x) ^ 2 ≤ δ * Real.log x ∧ 1 ≤ Real.log x :=
    (eventually_ge_atTop x₁).and ((eventually_ge_atTop 3).and ((ev_log (ev_count_le As hAs)).and
      ((ev_log (ev_A3 δ hδ)).and ((ev_log (ev_A4 K₁ C₃)).and ((ev_log (ev_A5 δ hδ)).and
        (ev_log (eventually_ge_atTop 1)))))))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hev
  refine ⟨x₀, fun x hx Hn hHn1 hHn2 c hc P hP hP1 hP2 𝒮 h𝒮 Z hZ0 hZ M hMc εM hM => ?_⟩
  obtain ⟨hxx₁, hx3, hcount, hA3, hA4, hA5, hL1⟩ := hx₀ x hx
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith only [hx3]
  have hL0 : 0 < L := by linarith only [hL1]
  have hHnexp : Real.exp (δ * L) ≤ Hn := by
    have := hHn1
    rw [Real.rpow_def_of_pos hx0, mul_comm] at this
    exact this
  have hHn1' : 1 ≤ Hn := le_trans (Real.one_le_exp (by positivity)) hHnexp
  set η₀ := L ^ (-As) with hη₀
  have hη : 0 < η₀ := Real.rpow_pos_of_pos hL0 _
  set N : ℝ → ℂ := fun τ => ∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ) with hN
  have hNc : Continuous N := by
    rw [hN]
    exact continuous_finsetSum _ fun n hn => continuous_const.mul
      (continuous_natCpow_I_mul n (Fset_pos Hn (by linarith only [hHn1']) n hn))
  have h𝒮' : ∀ p ∈ 𝒮, P ≤ p ∧ (p : ℝ) ≤ 2 * P := fun p hp => (h𝒮 p hp).2
  obtain ⟨𝒦, w, t, h𝒦, hsplit⟩ := split_mean_core P (by linarith only [hP]) 𝒮 h𝒮' η₀ hη.le Z hZ0 M N hMc
    hNc εM hM
  have hZc : (⌈Z⌉₊ : ℝ) ≤ Z + 1 := (Nat.ceil_lt_add_one hZ0).le
  have hx3' : (27 : ℝ) ≤ x ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hx3 3; norm_num at this; linarith only [this]
  have hx4 : 3 * x ^ 3 ≤ x ^ 4 := by
    have e : x ^ 4 = x * x ^ 3 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hx3 (by positivity)
  -- the count of large values
  have hcard : (𝒦.card : ℝ) ≤ 3 * Real.exp (L ^ (0.95 : ℝ)) := by
    have hfib : (𝒦.card : ℝ) = ∑ r : ZMod 3, ((𝒦.filter (fun k : ℤ => (k : ZMod 3) = r)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_fiberwise 𝒦 (fun k : ℤ => (k : ZMod 3))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    rw [hfib]
    have hone : ∀ r : ZMod 3, ((𝒦.filter (fun k : ℤ => (k : ZMod 3) = r)).card : ℝ) ≤
        Real.exp (L ^ (0.95 : ℝ)) := by
      intro r
      set 𝒦r := 𝒦.filter (fun k : ℤ => (k : ZMod 3) = r) with h𝒦r
      have hsub : 𝒦r ⊆ 𝒦 := filter_subset _ _
      set jj := ⌊Real.log (Z + 4) / Real.log (2 * P)⌋₊ with hjj
      obtain ⟨hj1, hj2⟩ := j_bounds P (Z + 4) hP (by linarith only [hZ0])
      have hτ : ∀ k ∈ 𝒦r, |w k| ≤ Z + 4 - 1 ∧ η₀ < ‖Pf 𝒮 P (w k)‖ := by
        intro k hk
        obtain ⟨hk1, hk2, hk3, hk4, _, _⟩ := h𝒦 k (hsub hk)
        refine ⟨?_, hk4⟩
        rw [abs_le] at hk1 ⊢
        have a1 : (-(⌈Z⌉₊ : ℝ) - 1) ≤ k := by
          have := hk1.1; have : ((-(⌈Z⌉₊ + 1 : ℕ) : ℤ) : ℝ) ≤ k := by exact_mod_cast this
          push_cast at this; linarith only [this]
        have a2 : (k : ℝ) ≤ ⌈Z⌉₊ + 1 := by
          have := hk1.2; have : (k : ℝ) ≤ ((⌈Z⌉₊ + 1 : ℕ) : ℤ) := by exact_mod_cast this
          push_cast at this; linarith only [this]
        constructor <;> linarith only [a1, a2, hk2, hk3, hZc]
      have hsep : ∀ k ∈ 𝒦r, ∀ k' ∈ 𝒦r, k ≠ k' → 2 ≤ |w k - w k'| := by
        intro k hk k' hk' hne
        have h3 : 3 ≤ |k - k'| := by
          rw [h𝒦r, mem_filter] at hk hk'
          have hmod : ((k : ℤ) : ZMod 3) = ((k' : ℤ) : ZMod 3) := hk.2.trans hk'.2.symm
          rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hmod
          obtain ⟨q, hq⟩ := hmod
          have hq0 : q ≠ 0 := by rintro rfl; apply hne; omega
          rw [show k - k' = -(k' - k) by ring, abs_neg, hq, abs_mul]
          have : 1 ≤ |q| := Int.one_le_abs hq0
          norm_num; linarith only [this]
        obtain ⟨_, hw1, hw2, _, _, _⟩ := h𝒦 k (hsub hk)
        obtain ⟨_, hw1', hw2', _, _, _⟩ := h𝒦 k' (hsub hk')
        have h3' : (3 : ℝ) ≤ |(k : ℝ) - k'| := by
          rw [← Int.cast_sub, ← Int.cast_abs]; exact_mod_cast h3
        rcases le_abs'.mp h3' with h | h
        · rw [abs_sub_comm]; rw [le_abs']; right; linarith only [h, hw1, hw2, hw1', hw2']
        · rw [le_abs']; right; linarith only [h, hw1, hw2, hw1', hw2']
      have hlv := large_values_core P hP 𝒮 h𝒮 η₀ hη jj (Z + 4) (by linarith only [hZ0]) 𝒦r w hτ hsep
      have hc𝒮 := card_primes_le P (by linarith only [hP]) 𝒮 h𝒮'
      have hcc := count_core P (Z + 4) η₀ jj hP (by linarith only [hZ0]) hj1 hj2 hη (𝒦r.card) (𝒮.card)
        (Nat.cast_nonneg _) hc𝒮 hlv
      have hlogZ : Real.log (Z + 4) ≤ 4 * L := by
        have h4 : Z + 4 ≤ x ^ 4 := by linarith only [hZ, hx4, hx3']
        calc Real.log (Z + 4) ≤ Real.log (x ^ 4) := Real.log_le_log (by linarith only [hZ0]) h4
          _ = 4 * L := by rw [Real.log_pow]; push_cast; ring
      have hb := hcount P (Z + 4) jj hP hP1 hP2 (by linarith only [hZ0]) hlogZ hj1
      exact hcc.trans hb
    calc ∑ r : ZMod 3, ((𝒦.filter (fun k : ℤ => (k : ZMod 3) = r)).card : ℝ)
        ≤ ∑ _r : ZMod 3, Real.exp (L ^ (0.95 : ℝ)) := sum_le_sum fun r _ => hone r
      _ = 3 * Real.exp (L ^ (0.95 : ℝ)) := by
          rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; push_cast; ring
  -- the Gram estimate
  set T := Real.exp (L / (2 * Real.log L ^ 2)) with hT
  set E := max K₁ 0 * Hn * Real.exp (-(L / Real.log L ^ C₃)) with hE
  set D := ⌈Z⌉₊ + 1 with hD
  have hT0 : 0 ≤ T := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := by rw [hE]; have := le_max_right K₁ 0; positivity
  have hDk : ∀ k ∈ 𝒦, |k| ≤ D := fun k hk => by have := (h𝒦 k hk).1; push_cast; exact this
  have htk : ∀ k ∈ 𝒦, (k : ℝ) ≤ t k ∧ t k ≤ k + 1 := fun k hk =>
    ⟨(h𝒦 k hk).2.2.2.2.1, (h𝒦 k hk).2.2.2.2.2⟩
  have hDx : (2 * D + 2 : ℝ) ≤ 4 * x ^ 3 := by
    rw [hD]; push_cast; linarith only [hZc, hZ, hx3']
  have hlarge : ∀ Δ : ℝ, T ≤ |Δ| → |Δ| ≤ 2 * D + 2 → ‖Gsum Hn Δ‖ ≤ E := by
    intro Δ hΔ1 hΔ2
    rw [Gsum_eq_lpp Hn Δ (by linarith only [hHn1']) (Set.Icc Hn (2 * Hn)) rfl]
    have hNlow : Real.exp (L / Real.log L ^ 2) ≤ Hn :=
      le_trans (Real.exp_le_exp.mpr hA5) hHnexp
    have hNup : Hn ≤ 2 * x ^ 5 := by
      have : x ≤ x ^ 5 := by
        calc x = x ^ 1 := (pow_one x).symm
          _ ≤ x ^ 5 := pow_le_pow_right₀ (by linarith only [hx3]) (by norm_num)
      linarith only [hHn2, this, hx0]
    have hq : ((1 : ℕ) : ℝ) ≤ L ^ (1 : ℝ) := by rw [Real.rpow_one]; push_cast; exact hL1
    have := hx₁ x hxx₁ Hn hNlow hNup 1 one_pos hq Δ hΔ1 (hΔ2.trans hDx) 0 (Set.Icc Hn (2 * Hn))
      Set.ordConnected_Icc subset_rfl
    refine this.trans ?_
    rw [hE]
    push_cast
    rw [div_one]
    gcongr
    exact le_max_left _ _
  have hgram := sparse_gram_core Hn T E (L ^ C) hHn1' hT0 hE0 𝒦 D hDk t htk hlarge c hc
  have hKbig : (𝒦.card : ℝ) * (1 + T + E) ≤ Hn := by
    have hcE : (𝒦.card : ℝ) * E ≤ Hn / 2 := by
      calc (𝒦.card : ℝ) * E ≤ 3 * Real.exp (L ^ (0.95 : ℝ)) * E := by gcongr
        _ = Hn * (3 * Real.exp (L ^ (0.95 : ℝ)) * (max K₁ 0 *
              Real.exp (-(L / Real.log L ^ C₃)))) := by rw [hE]; ring
        _ ≤ Hn * (1 / 2) := by gcongr
        _ = Hn / 2 := by ring
    have hcT : (𝒦.card : ℝ) * (1 + T) ≤ Hn / 2 := by
      calc (𝒦.card : ℝ) * (1 + T) ≤ 3 * Real.exp (L ^ (0.95 : ℝ)) * (1 + T) := by gcongr
        _ ≤ Real.exp (δ * L) / 2 := hA3
        _ ≤ Hn / 2 := by linarith only [hHnexp]
    have e : (𝒦.card : ℝ) * (1 + T + E) = 𝒦.card * (1 + T) + 𝒦.card * E := by ring
    linarith only [hcE, hcT, e]
  have hlogD : Real.log (2 * D) ≤ 4 * L := by
    have h1 : (2 * D : ℝ) ≤ x ^ 4 := by rw [hD]; push_cast; linarith only [hZc, hZ, hx4, hx3']
    have h0 : (0 : ℝ) < 2 * D := by rw [hD]; positivity
    calc Real.log (2 * D) ≤ Real.log (x ^ 4) := Real.log_le_log h0 h1
      _ = 4 * L := by rw [Real.log_pow]; push_cast; ring
  have hLC : (L ^ C) ^ 2 = L ^ (2 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
  have hLC1 : L * L ^ (2 * C) = L ^ (2 * C + 1) := by
    rw [Real.rpow_add hL0, Real.rpow_one]; ring
  have hsum : ∑ k ∈ 𝒦, ‖N (t k)‖ ^ 2 ≤ 450 * Hn ^ 2 * L ^ (2 * C + 1) := by
    refine hgram.trans ?_
    have hLCpos : 0 ≤ L ^ (2 * C) := by positivity
    calc 3 * ((Hn + 1) + 12 * Hn * (1 + Real.log (2 * D)) + 𝒦.card * (1 + T + E)) *
          ((Hn + 1) * (L ^ C) ^ 2)
        ≤ 3 * ((Hn + Hn) + 12 * Hn * (1 + 4 * L) + Hn) * ((Hn + Hn) * L ^ (2 * C)) := by
          rw [hLC]
          gcongr
      _ = 3 * (15 * Hn + 48 * Hn * L) * (2 * Hn * L ^ (2 * C)) := by ring
      _ ≤ 3 * (63 * Hn * L) * (2 * Hn * L ^ (2 * C)) := by
          have h15 := mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ 15 * Hn by linarith only [hHn1'])
          gcongr; linarith only [h15]
      _ = 378 * Hn ^ 2 * (L * L ^ (2 * C)) := by ring
      _ ≤ 450 * Hn ^ 2 * L ^ (2 * C + 1) := by
          rw [hLC1]; gcongr; norm_num
  refine hsplit.trans ?_
  gcongr

end

end ArtinPrimitiveRoots.L102M
end

section
namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ C As : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hAs : 0 < As) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hn : ℝ, x ^ δ ≤ Hn → Hn ≤ x →
      ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ Real.log x ^ C) →
      ∀ P : ℝ, 2 ≤ P → Real.log x ^ (0.1 : ℝ) ≤ Real.log P →
      Real.log P ≤ 3 * Real.log x ^ (0.2 : ℝ) →
      ∀ 𝒮 : Finset ℕ, (∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Z : ℝ, 0 ≤ Z → Z ≤ x ^ 3 →
      ∀ M : ℝ → ℂ, Continuous M → ∀ εM : ℝ, (∀ τ : ℝ, |τ| ≤ Z → ‖M τ‖ ≤ εM) →
      ∫ τ in (-Z)..Z, ‖((P : ℂ))⁻¹ * ∑ p ∈ 𝒮, (p : ℂ) ^ (Complex.I * τ)‖ ^ 2 * ‖M τ‖ ^ 2 *
          ‖∑ n ∈ (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ => Hn ≤ (n : ℝ)),
            c n * (n : ℂ) ^ (Complex.I * τ)‖ ^ 2 ≤
        (Real.log x ^ (-As)) ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 *
          ‖∑ n ∈ (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ => Hn ≤ (n : ℝ)),
            c n * (n : ℂ) ^ (Complex.I * τ)‖ ^ 2) +
        4 * εM ^ 2 * (450 * Hn ^ 2 * Real.log x ^ (2 * C + 1)) := by
  exact L102M.lemma53 δ C As hδ hC hAs
end
