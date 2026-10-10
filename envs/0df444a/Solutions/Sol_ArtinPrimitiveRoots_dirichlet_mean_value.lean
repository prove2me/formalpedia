-- Prove2me | solution 1 for ArtinPrimitiveRoots.dirichlet_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T20:27:25.739115+00:00
-- url     : https://prove2.me/submissions/07624c1b-6948-41ee-bb45-d73007cef86b

import Mathlib
import Definitions.Def_ArtinMarkedSquare

section
/-!
# L102M: shared basic definitions and lemmas

`arcCutoff` facts, `ψ_λ = psiL`, `n^{iτ}` helpers, and the Cauchy weight `ω_a`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

lemma hasDerivAt_cexp_mul_ofReal (c : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (c * Complex.exp (c * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c y := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul c
  have := h1.cexp
  simpa [mul_comm] using this

lemma natCpow_I_mul (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (I * t) = Complex.exp (I * t * Real.log n) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  have h : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [h]; congr 1; ring

/-- The Cauchy weight `ω_a(τ) = (1 + (τ/a)²)⁻¹`. -/
def ωa (a τ : ℝ) : ℝ := (1 + (τ / a) ^ 2)⁻¹

lemma ωa_pos (a τ : ℝ) : 0 < ωa a τ := by unfold ωa; positivity

lemma ωa_continuous (a : ℝ) : Continuous (ωa a) := by
  unfold ωa
  exact Continuous.inv₀ (by fun_prop) (fun τ => by positivity)

lemma integrable_ωa (a : ℝ) (ha : 0 < a) : Integrable (ωa a) := by
  have h := (integrable_inv_one_add_sq).comp_mul_left' (inv_ne_zero ha.ne')
  have e : (fun τ => (1 + (a⁻¹ * τ) ^ 2)⁻¹) = ωa a := by
    funext τ; unfold ωa; rw [div_eq_inv_mul]
  simpa [e] using h

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the mean value theorem for Dirichlet polynomials (weak form)

`∫_{T₁}^{T₂} |∑_{n ∈ s} c_n n^{it}|² dt ≤ (T₂ - T₁ + 4N(1 + log N)) ∑ |c_n|²` for `s ⊆ [1, N]`.
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory intervalIntegral

lemma norm_integral_exp_I_mul_le (ℓ : ℝ) (hℓ : ℓ ≠ 0) (T₁ T₂ : ℝ) :
    ‖∫ t in T₁..T₂, Complex.exp (I * ℓ * t)‖ ≤ 2 / |ℓ| := by
  have hc : (I * ℓ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hℓ)
  rw [integral_exp_mul_complex hc, norm_div]
  have h1 : ‖Complex.exp (I * ℓ * T₂)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (I * ℓ * T₁)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hn : ‖(I * ℓ : ℂ)‖ = |ℓ| := by simp
  rw [hn]
  have hl : 0 < |ℓ| := abs_pos.mpr hℓ
  rw [div_le_div_iff_of_pos_right hl]
  calc ‖Complex.exp (I * ℓ * T₂) - Complex.exp (I * ℓ * T₁)‖
      ≤ ‖Complex.exp (I * ℓ * T₂)‖ + ‖Complex.exp (I * ℓ * T₁)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

lemma abs_log_sub_log_ge (n m N : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnN : n ≤ N) (hmN : m ≤ N) :
    |(n : ℝ) - m| / N ≤ |Real.log n - Real.log m| := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hN : (0 : ℝ) < N := by linarith
  -- WLOG m ≤ n
  have key : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → a ≤ N → b ≤ N → b ≤ a →
      (a - b) / N ≤ Real.log a - Real.log b := by
    intro a b ha hb haN hbN hba
    have hb0 : 0 < b := by linarith
    have ha0 : 0 < a := by linarith
    rw [← Real.log_div ha0.ne' hb0.ne']
    have h1 : 1 - b / a ≤ Real.log (a / b) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos ha0 hb0)
      rwa [inv_div] at this
    have h2 : (a - b) / N ≤ 1 - b / a := by
      rw [one_sub_div ha0.ne', div_le_div_iff₀ hN ha0]
      nlinarith
    linarith
  rcases le_total m n with h | h
  · have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg]
    · exact key n m hn' hm' hnN' hmN' hmn
    · exact sub_nonneg.mpr (Real.log_le_log (by linarith) hmn)
  · have hmn : (n : ℝ) ≤ m := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos]
    · have := key m n hm' hn' hmN' hnN' hmn
      have e : -((n : ℝ) - m) / N = (m - n) / N := by ring
      rw [e]; linarith
    · exact sub_nonpos.mpr (Real.log_le_log (by linarith) hmn)

/-- `∑_{1 ≤ m ≤ N, m ≠ n} 1/|n - m| ≤ 2 (1 + log N)`. -/
lemma sum_inv_abs_sub_le (n N : ℕ) (hnN : n ≤ N) :
    ∑ m ∈ (Icc 1 N).erase n, 1 / |(n : ℝ) - m| ≤ 2 * (1 + Real.log N) := by
  have hH : ∑ d ∈ Icc 1 N, (1 / (d : ℝ)) ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  have hsplit : ∑ m ∈ (Icc 1 N).erase n, 1 / |(n : ℝ) - m| =
      ∑ m ∈ ((Icc 1 N).erase n).filter (· < n), 1 / |(n : ℝ) - m| +
      ∑ m ∈ ((Icc 1 N).erase n).filter (fun m => ¬ m < n), 1 / |(n : ℝ) - m| :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hA : ∑ m ∈ ((Icc 1 N).erase n).filter (· < n), 1 / |(n : ℝ) - m| ≤
      ∑ d ∈ Icc 1 N, (1 / (d : ℝ)) := by
    have himg : ∑ m ∈ ((Icc 1 N).erase n).filter (· < n), 1 / |(n : ℝ) - m| =
        ∑ d ∈ (((Icc 1 N).erase n).filter (· < n)).image (fun m => n - m), 1 / (d : ℝ) := by
      rw [sum_image]
      · apply sum_congr rfl
        intro m hm
        simp only [mem_filter, mem_erase, mem_Icc] at hm
        rw [Nat.cast_sub hm.2.le, abs_of_pos (by
          have : (m : ℝ) < n := by exact_mod_cast hm.2
          linarith)]
      · intro a ha b hb hab
        simp only [coe_filter, mem_erase, mem_Icc, Set.mem_ofPred_eq] at ha hb
        simp only at hab
        omega
    rw [himg]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [mem_image, mem_filter, mem_erase, mem_Icc] at hd
      obtain ⟨m, ⟨⟨_, h1, h2⟩, h3⟩, rfl⟩ := hd
      simp only [mem_Icc]; omega
    · intro d _ _; positivity
  have hB : ∑ m ∈ ((Icc 1 N).erase n).filter (fun m => ¬ m < n), 1 / |(n : ℝ) - m| ≤
      ∑ d ∈ Icc 1 N, (1 / (d : ℝ)) := by
    have himg : ∑ m ∈ ((Icc 1 N).erase n).filter (fun m => ¬ m < n), 1 / |(n : ℝ) - m| =
        ∑ d ∈ (((Icc 1 N).erase n).filter (fun m => ¬ m < n)).image (fun m => m - n),
          1 / (d : ℝ) := by
      rw [sum_image]
      · apply sum_congr rfl
        intro m hm
        simp only [mem_filter, mem_erase, mem_Icc, not_lt] at hm
        have hlt : n < m := lt_of_le_of_ne hm.2 (Ne.symm hm.1.1)
        rw [Nat.cast_sub hlt.le, abs_of_neg (by
          have : (n : ℝ) < m := by exact_mod_cast hlt
          linarith)]
        congr 1; ring
      · intro a ha b hb hab
        simp only [coe_filter, mem_erase, mem_Icc, Set.mem_ofPred_eq, not_lt] at ha hb
        simp only at hab
        omega
    rw [himg]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [mem_image, mem_filter, mem_erase, mem_Icc, not_lt] at hd
      obtain ⟨m, ⟨⟨h0, h1, h2⟩, h3⟩, rfl⟩ := hd
      simp only [mem_Icc]; omega
    · intro d _ _; positivity
  rw [hsplit]; linarith

lemma sum_two_div_log_le (n N : ℕ) (s : Finset ℕ) (hs : ∀ m ∈ s, 1 ≤ m ∧ m ≤ N)
    (hn : n ∈ s) :
    ∑ m ∈ s.erase n, 2 / |Real.log n - Real.log m| ≤ 4 * N * (1 + Real.log N) := by
  obtain ⟨hn1, hnN⟩ := hs n hn
  have hN : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hn1.trans hnN
    linarith
  calc ∑ m ∈ s.erase n, 2 / |Real.log n - Real.log m|
      ≤ ∑ m ∈ s.erase n, 2 * N * (1 / |(n : ℝ) - m|) := by
        apply sum_le_sum
        intro m hm
        have hm' := mem_of_mem_erase hm
        have hne : m ≠ n := ne_of_mem_erase hm
        obtain ⟨hm1, hmN⟩ := hs m hm'
        have hpos : 0 < |(n : ℝ) - m| := by
          rw [abs_pos, sub_ne_zero]; exact_mod_cast hne.symm
        have hge := abs_log_sub_log_ge n m N hn1 hm1 hnN hmN
        have hpos' : 0 < |Real.log n - Real.log m| := lt_of_lt_of_le (by positivity) hge
        rw [div_le_iff₀ hpos']
        calc (2 : ℝ) = 2 * N * (1 / |(n : ℝ) - m|) * (|(n : ℝ) - m| / N) := by
              field_simp
          _ ≤ 2 * N * (1 / |(n : ℝ) - m|) * |Real.log n - Real.log m| := by
              gcongr
    _ ≤ ∑ m ∈ (Icc 1 N).erase n, 2 * N * (1 / |(n : ℝ) - m|) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [mem_erase] at hm ⊢
          refine ⟨hm.1, ?_⟩
          rw [mem_Icc]; exact hs m hm.2
        · intro m _ _; positivity
    _ = 2 * N * ∑ m ∈ (Icc 1 N).erase n, 1 / |(n : ℝ) - m| := by rw [mul_sum]
    _ ≤ 2 * N * (2 * (1 + Real.log N)) := by
        gcongr; exact sum_inv_abs_sub_le n N hnN
    _ = 4 * N * (1 + Real.log N) := by ring

/-- **Mean value theorem** (weak form): for `s ⊆ [1, N]` and `T₁ ≤ T₂`,
`∫_{T₁}^{T₂} ‖∑_{n ∈ s} c_n n^{it}‖² dt ≤ (T₂ - T₁ + 4N(1 + log N)) ∑_{n ∈ s} ‖c_n‖²`. -/
theorem mvt (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ)
    (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * t)‖ ^ 2 ≤
      (T₂ - T₁ + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  set D : ℝ → ℂ := fun t => ∑ n ∈ s, c n * (n : ℂ) ^ (I * t) with hD
  have hpos : ∀ n ∈ s, 0 < n := fun n hn => (hs n hn).1
  -- expand the square
  have hexp : ∀ t : ℝ, ((‖D t‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, c n * (starRingEnd ℂ) (c m) *
        Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', hD]
    simp only
    rw [map_sum, sum_mul_sum]
    apply sum_congr rfl; intro n hn
    apply sum_congr rfl; intro m hm
    rw [map_mul, natCpow_I_mul n (hpos n hn), natCpow_I_mul m (hpos m hm), ← Complex.exp_conj]
    have : (starRingEnd ℂ) (I * t * Real.log m) = -(I * t * Real.log m) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]; ring
    rw [this]
    have h2 : Complex.exp (I * t * Real.log n) * Complex.exp (-(I * t * Real.log m)) =
        Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
      rw [← Complex.exp_add]; congr 1; rw [Complex.ofReal_sub]; ring
    rw [← h2]; ring
  have hcont : ∀ n ∈ s, ∀ m ∈ s, Continuous fun t : ℝ =>
      c n * (starRingEnd ℂ) (c m) * Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
    intro n _ m _; fun_prop
  have hint : ((∫ t in T₁..T₂, ‖D t‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, c n * (starRingEnd ℂ) (c m) *
        ∫ t in T₁..T₂, Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl; intro n hn
      rw [intervalIntegral.integral_finsetSum]
      · apply sum_congr rfl; intro m hm
        rw [intervalIntegral.integral_const_mul]
      · intro m hm; exact ((hcont n hn m hm).intervalIntegrable _ _)
    · intro n hn
      exact (continuous_finsetSum _ fun m hm => hcont n hn m hm).intervalIntegrable _ _
  have hnonneg : 0 ≤ ∫ t in T₁..T₂, ‖D t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => by positivity)
  have hbound : ∀ n ∈ s, ∀ m ∈ s,
      ‖∫ t in T₁..T₂, Complex.exp (I * (Real.log n - Real.log m : ℝ) * t)‖ ≤
        if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m| := by
    intro n _ m _
    split_ifs with h
    · subst h
      simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
        intervalIntegral.integral_const, Complex.real_smul, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith)]
    · apply norm_integral_exp_I_mul_le
      intro h0
      apply h
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr (show (0 : ℝ) < n by
        exact_mod_cast hpos n ‹_›)) (Set.mem_Ioi.mpr (show (0 : ℝ) < m by
        exact_mod_cast hpos m ‹_›)) (by linarith)
      exact_mod_cast this
  calc ∫ t in T₁..T₂, ‖D t‖ ^ 2
      = ‖((∫ t in T₁..T₂, ‖D t‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ‖c n‖ * ‖c m‖ *
          (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|) := by
        rw [hint]
        refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
        exact hbound n hn m hm
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ((‖c n‖ ^ 2 + ‖c m‖ ^ 2) / 2 *
          (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|)) := by
        apply sum_le_sum; intro n _; apply sum_le_sum; intro m _
        have hw : 0 ≤ (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|) := by
          split_ifs
          · linarith
          · positivity
        gcongr
        nlinarith [sq_nonneg (‖c n‖ - ‖c m‖)]
    _ = ∑ n ∈ s, ‖c n‖ ^ 2 * ∑ m ∈ s,
          (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|) := by
        -- symmetrize
        have hsymm : ∀ n m : ℕ, (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|) =
            (if m = n then T₂ - T₁ else 2 / |Real.log m - Real.log n|) := by
          intro n m
          by_cases h : n = m
          · subst h; simp
          · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]
        have e1 : ∑ n ∈ s, ∑ m ∈ s, ((‖c n‖ ^ 2 + ‖c m‖ ^ 2) / 2 *
            (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|)) =
            (∑ n ∈ s, ∑ m ∈ s, ‖c n‖ ^ 2 *
              (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|)) / 2 +
            (∑ n ∈ s, ∑ m ∈ s, ‖c m‖ ^ 2 *
              (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|)) / 2 := by
          rw [sum_div, sum_div, ← sum_add_distrib]
          apply sum_congr rfl; intro n _
          rw [sum_div, sum_div, ← sum_add_distrib]
          apply sum_congr rfl; intro m _
          ring
        have e2 : (∑ n ∈ s, ∑ m ∈ s, ‖c m‖ ^ 2 *
              (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|)) =
            ∑ n ∈ s, ∑ m ∈ s, ‖c n‖ ^ 2 *
              (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|) := by
          rw [sum_comm]
          apply sum_congr rfl; intro n _
          apply sum_congr rfl; intro m _
          rw [hsymm]
        rw [e1, e2]
        simp_rw [mul_sum]
        ring
    _ ≤ ∑ n ∈ s, ‖c n‖ ^ 2 * (T₂ - T₁ + 4 * N * (1 + Real.log N)) := by
        apply sum_le_sum; intro n hn
        gcongr
        rw [← add_sum_erase s _ hn, if_pos rfl]
        gcongr
        calc ∑ m ∈ s.erase n, (if n = m then T₂ - T₁ else 2 / |Real.log n - Real.log m|)
            = ∑ m ∈ s.erase n, 2 / |Real.log n - Real.log m| := by
              apply sum_congr rfl; intro m hm
              rw [if_neg (Ne.symm (ne_of_mem_erase hm))]
          _ ≤ 4 * N * (1 + Real.log N) := sum_two_div_log_le n N s hs hn
    _ = (T₂ - T₁ + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
        rw [mul_sum]; apply sum_congr rfl; intro n _; ring

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the weighted mean value theorem

With `ω_a(τ) = (1 + (τ/a)²)⁻¹`:
`∫ ω_a(τ) |∑_{n ∈ s} c_n n^{iτ}|² dτ ≤ (π a + 2π N (1 + log N)) ∑ |c_n|²` for `s ⊆ [1, N]`.
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory Filter

noncomputable section

lemma integral_ωa (a : ℝ) (ha : 0 < a) : ∫ τ, ωa a τ = Real.pi * a := by
  have e : ωa a = fun τ => (fun x : ℝ => (1 + x ^ 2)⁻¹) (a⁻¹ * τ) := by
    funext τ; unfold ωa; rw [div_eq_inv_mul]
  rw [e, Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) a⁻¹,
    integral_univ_inv_one_add_sq, inv_inv, abs_of_pos ha, smul_eq_mul, mul_comm]

/-- `ω_a'(τ) = -(2τ/a²) ω_a(τ)²`. -/
def ωa' (a τ : ℝ) : ℝ := -(2 * τ / a ^ 2) * (ωa a τ) ^ 2

lemma hasDerivAt_ωa (a : ℝ) (ha : 0 < a) (τ : ℝ) : HasDerivAt (ωa a) (ωa' a τ) τ := by
  unfold ωa ωa'
  have ha' := ha.ne'
  have h1 : HasDerivAt (fun τ : ℝ => 1 + (τ / a) ^ 2) (2 * τ / a ^ 2) τ := by
    have := (((hasDerivAt_id τ).div_const a).pow 2).const_add 1
    refine this.congr_deriv ?_
    simp only [id]
    norm_num
    ring
  have hne : (1 + (τ / a) ^ 2) ≠ 0 := by positivity
  refine (h1.inv hne).congr_deriv ?_
  simp only [ωa]
  rw [inv_pow]
  ring

lemma abs_ωa'_le (a : ℝ) (ha : 0 < a) (τ : ℝ) : |ωa' a τ| ≤ a⁻¹ * ωa a τ := by
  unfold ωa'
  have hω := ωa_pos a τ
  have key : 2 * |τ / a| * ωa a τ ≤ 1 := by
    unfold ωa
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith [sq_nonneg (|τ / a| - 1), sq_abs (τ / a)]
  rw [abs_mul, abs_neg, abs_pow, abs_of_pos hω]
  have e : |2 * τ / a ^ 2| = a⁻¹ * (2 * |τ / a|) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : 0 < a ^ 2),
      abs_div, abs_of_pos ha]
    field_simp
  rw [e]
  calc a⁻¹ * (2 * |τ / a|) * ωa a τ ^ 2 = a⁻¹ * ωa a τ * (2 * |τ / a| * ωa a τ) := by ring
    _ ≤ a⁻¹ * ωa a τ * 1 := by gcongr
    _ = a⁻¹ * ωa a τ := mul_one _

lemma integrable_ωa' (a : ℝ) (ha : 0 < a) : Integrable (ωa' a) := by
  refine ((integrable_ωa a ha).const_mul a⁻¹).mono' ?_ (Eventually.of_forall fun τ => ?_)
  · unfold ωa'
    exact (Continuous.mul (by fun_prop) ((ωa_continuous a).pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_ωa'_le a ha τ

/-- `|∫ ω_a(τ) e^{iℓτ} dτ| ≤ π/|ℓ|` for `ℓ ≠ 0`. -/
lemma norm_integral_ωa_exp_le (a ℓ : ℝ) (ha : 0 < a) (hℓ : ℓ ≠ 0) :
    ‖∫ τ, (ωa a τ : ℂ) * Complex.exp (I * ℓ * τ)‖ ≤ Real.pi / |ℓ| := by
  have hc : (I * ℓ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hℓ)
  set u : ℝ → ℂ := fun τ => (ωa a τ : ℂ) with hu
  set u' : ℝ → ℂ := fun τ => (ωa' a τ : ℂ) with hu'
  set v : ℝ → ℂ := fun τ => Complex.exp (I * ℓ * τ) / (I * ℓ) with hv
  set v' : ℝ → ℂ := fun τ => Complex.exp (I * ℓ * τ) with hv'
  have hder_u : ∀ x, HasDerivAt u (u' x) x := fun x =>
    (hasDerivAt_ωa a ha x).ofReal_comp
  have hder_v : ∀ x, HasDerivAt v (v' x) x := by
    intro x
    have h : HasDerivAt (fun τ : ℝ => Complex.exp (I * ℓ * τ)) (I * ℓ * Complex.exp (I * ℓ * x)) x :=
      hasDerivAt_cexp_mul_ofReal (I * ℓ) x
    have := h.div_const (I * ℓ)
    refine this.congr_deriv ?_
    rw [hv']; exact mul_div_cancel_left₀ _ hc
  have hvb : ∀ τ, ‖v τ‖ = 1 / |ℓ| := by
    intro τ
    rw [hv]; simp only
    rw [norm_div, show I * (ℓ : ℂ) * (τ : ℂ) = ((ℓ * τ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    simp
  have hv'b : ∀ τ, ‖v' τ‖ = 1 := by
    intro τ
    rw [hv']; simp only
    rw [show I * (ℓ : ℂ) * (τ : ℂ) = ((ℓ * τ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hvc : Continuous v := by rw [hv]; fun_prop
  have hv'c : Continuous v' := by rw [hv']; fun_prop
  have hui : Integrable u := (integrable_ωa a ha).ofReal
  have hu'i : Integrable u' := (integrable_ωa' a ha).ofReal
  have h1 : Integrable (u * v') := hui.mul_bdd hv'c.aestronglyMeasurable
    (Eventually.of_forall fun τ => (hv'b τ).le)
  have h2 : Integrable (u' * v) := hu'i.mul_bdd hvc.aestronglyMeasurable
    (Eventually.of_forall fun τ => (hvb τ).le)
  have h3 : Integrable (u * v) := hui.mul_bdd hvc.aestronglyMeasurable
    (Eventually.of_forall fun τ => (hvb τ).le)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hder_u x)
    (fun x _ => hder_v x) h1 h2 h3
  have e : (fun τ : ℝ => (ωa a τ : ℂ) * Complex.exp (I * ℓ * τ)) = fun τ => u τ * v' τ := rfl
  rw [e, hibp, norm_neg]
  calc ‖∫ x, u' x * v x‖ ≤ ∫ x, ‖u' x * v x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, a⁻¹ * ωa a x * (1 / |ℓ|) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
        · exact ((integrable_ωa a ha).const_mul a⁻¹).mul_const _
        · refine Eventually.of_forall fun x => ?_
          dsimp only
          rw [norm_mul, hvb, hu']; simp only [Complex.norm_real, Real.norm_eq_abs]
          gcongr
          exact abs_ωa'_le a ha x
    _ = Real.pi / |ℓ| := by
        rw [integral_mul_const, integral_const_mul, integral_ωa a ha]
        field_simp

/-- **Weighted mean value theorem.** -/
theorem wmvt (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ)
    (a : ℝ) (ha : 0 < a) :
    ∫ τ, ωa a τ * ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * τ)‖ ^ 2 ≤
      (Real.pi * a + 2 * Real.pi * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  set D : ℝ → ℂ := fun t => ∑ n ∈ s, c n * (n : ℂ) ^ (I * t) with hD
  have hpos : ∀ n ∈ s, 0 < n := fun n hn => (hs n hn).1
  have hexp : ∀ t : ℝ, ((ωa a t * ‖D t‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, c n * (starRingEnd ℂ) (c m) *
        ((ωa a t : ℂ) * Complex.exp (I * (Real.log n - Real.log m : ℝ) * t)) := by
    intro t
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', hD]
    simp only
    rw [map_sum, sum_mul_sum, mul_sum]
    apply sum_congr rfl; intro n hn
    rw [mul_sum]
    apply sum_congr rfl; intro m hm
    rw [map_mul, natCpow_I_mul n (hpos n hn), natCpow_I_mul m (hpos m hm), ← Complex.exp_conj]
    have : (starRingEnd ℂ) (I * t * Real.log m) = -(I * t * Real.log m) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]; ring
    rw [this]
    have h2 : Complex.exp (I * t * Real.log n) * Complex.exp (-(I * t * Real.log m)) =
        Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
      rw [← Complex.exp_add]; congr 1; rw [Complex.ofReal_sub]; ring
    rw [← h2]; ring
  have hint : ∀ n m : ℕ, Integrable fun t : ℝ =>
      (ωa a t : ℂ) * Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
    intro n m
    refine (integrable_ωa a ha).ofReal.mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun t => ?_)
    rw [show I * ((Real.log n - Real.log m : ℝ) : ℂ) * (t : ℂ) =
      (((Real.log n - Real.log m) * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hI : ((∫ t, ωa a t * ‖D t‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, c n * (starRingEnd ℂ) (c m) *
        ∫ t, (ωa a t : ℂ) * Complex.exp (I * (Real.log n - Real.log m : ℝ) * t) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum]
    · apply sum_congr rfl; intro n _
      rw [integral_finsetSum]
      · apply sum_congr rfl; intro m _
        rw [integral_const_mul]
      · intro m _; exact (hint n m).const_mul _
    · intro n _
      exact integrable_finsetSum _ fun m _ => (hint n m).const_mul _
  have hnonneg : 0 ≤ ∫ t, ωa a t * ‖D t‖ ^ 2 :=
    integral_nonneg fun t => mul_nonneg (ωa_pos a t).le (sq_nonneg _)
  have hbound : ∀ n ∈ s, ∀ m ∈ s,
      ‖∫ t, (ωa a t : ℂ) * Complex.exp (I * (Real.log n - Real.log m : ℝ) * t)‖ ≤
        if n = m then Real.pi * a else Real.pi / |Real.log n - Real.log m| := by
    intro n hn m hm
    split_ifs with h
    · subst h
      simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, integral_ωa a ha,
        abs_of_pos (by positivity)]
    · apply norm_integral_ωa_exp_le a _ ha
      intro h0
      apply h
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr (show (0 : ℝ) < n by
        exact_mod_cast hpos n hn)) (Set.mem_Ioi.mpr (show (0 : ℝ) < m by
        exact_mod_cast hpos m hm)) (by linarith)
      exact_mod_cast this
  set W : ℕ → ℕ → ℝ := fun n m =>
    if n = m then Real.pi * a else Real.pi / |Real.log n - Real.log m| with hW
  have hW0 : ∀ n m, 0 ≤ W n m := by
    intro n m; rw [hW]; simp only; split_ifs
    · positivity
    · positivity
  have hsymm : ∀ n m, W n m = W m n := by
    intro n m; rw [hW]; simp only
    by_cases h : n = m
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]
  calc ∫ t, ωa a t * ‖D t‖ ^ 2
      = ‖((∫ t, ωa a t * ‖D t‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ‖c n‖ * ‖c m‖ * W n m := by
        rw [hI]
        refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
        exact hbound n hn m hm
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ((‖c n‖ ^ 2 + ‖c m‖ ^ 2) / 2 * W n m) := by
        apply sum_le_sum; intro n _; apply sum_le_sum; intro m _
        apply mul_le_mul_of_nonneg_right _ (hW0 n m)
        nlinarith [sq_nonneg (‖c n‖ - ‖c m‖)]
    _ = ∑ n ∈ s, ‖c n‖ ^ 2 * ∑ m ∈ s, W n m := by
        have e1 : ∑ n ∈ s, ∑ m ∈ s, ((‖c n‖ ^ 2 + ‖c m‖ ^ 2) / 2 * W n m) =
            (∑ n ∈ s, ∑ m ∈ s, ‖c n‖ ^ 2 * W n m) / 2 +
            (∑ n ∈ s, ∑ m ∈ s, ‖c m‖ ^ 2 * W n m) / 2 := by
          rw [sum_div, sum_div, ← sum_add_distrib]
          apply sum_congr rfl; intro n _
          rw [sum_div, sum_div, ← sum_add_distrib]
          apply sum_congr rfl; intro m _
          ring
        have e2 : (∑ n ∈ s, ∑ m ∈ s, ‖c m‖ ^ 2 * W n m) =
            ∑ n ∈ s, ∑ m ∈ s, ‖c n‖ ^ 2 * W n m := by
          rw [sum_comm]
          apply sum_congr rfl; intro n _
          apply sum_congr rfl; intro m _
          rw [hsymm]
        rw [e1, e2]
        simp_rw [mul_sum]
        ring
    _ ≤ ∑ n ∈ s, ‖c n‖ ^ 2 * (Real.pi * a + 2 * Real.pi * N * (1 + Real.log N)) := by
        apply sum_le_sum; intro n hn
        gcongr
        rw [← add_sum_erase s _ hn]
        have hd : W n n = Real.pi * a := by rw [hW]; simp
        rw [hd]
        gcongr
        calc ∑ m ∈ s.erase n, W n m
            = ∑ m ∈ s.erase n, Real.pi / 2 * (2 / |Real.log n - Real.log m|) := by
              apply sum_congr rfl; intro m hm
              rw [hW]; simp only
              rw [if_neg (Ne.symm (ne_of_mem_erase hm))]
              field_simp
          _ = Real.pi / 2 * ∑ m ∈ s.erase n, 2 / |Real.log n - Real.log m| := by
              rw [mul_sum]
          _ ≤ Real.pi / 2 * (4 * N * (1 + Real.log N)) := by
              gcongr
              exact sum_two_div_log_le n N s hs hn
          _ = 2 * Real.pi * N * (1 + Real.log N) := by ring
    _ = (Real.pi * a + 2 * Real.pi * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
        rw [mul_sum]; apply sum_congr rfl; intro n _; ring

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
theorem solution (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ) :
    (∀ T₁ T₂ : ℝ, T₁ ≤ T₂ →
      ∫ t in T₁..T₂, ‖∑ n ∈ s, c n * (n : ℂ) ^ (Complex.I * t)‖ ^ 2 ≤
        (T₂ - T₁ + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2) ∧
    (∀ a : ℝ, 0 < a →
      ∫ τ, (1 + (τ / a) ^ 2)⁻¹ * ‖∑ n ∈ s, c n * (n : ℂ) ^ (Complex.I * τ)‖ ^ 2 ≤
        (π * a + 2 * π * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2) := by
  exact ⟨fun T₁ T₂ h => L102M.mvt s N hs c T₁ T₂ h, fun a ha => L102M.wmvt s N hs c a ha⟩
end
