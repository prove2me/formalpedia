-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_factor_type_ii
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:41:24.602952+00:00
-- url     : https://prove2.me/submissions/957f678d-4ecd-427e-9613-44a70c2979c9

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_rough_factor_coefficient_bound
import Theorems.Thm_ArtinPrimitiveRoots_marked_type_ii_of_coefficient_bound
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product

namespace ArtinPrimitiveRoots.Prop103

open Real Filter Topology MeasureTheory

/-! ## A bound for the rough-number density on `[γ, 1]` -/

lemma roughDensityTerm_abs_le (γ w : ℝ) (hγ : 0 < γ) (hγw : γ ≤ w) (hw : w ≤ 1) (j : ℕ) :
    |roughDensityTerm γ w j| ≤ (1 / γ) ^ j / (j.factorial : ℝ) := by
  rcases j with _ | _ | j
  · simp [roughDensityTerm]
  · show |1 / w| ≤ (1 / γ) ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ)
    rw [abs_of_pos (by have := hγ.trans_le hγw; positivity)]
    simpa using one_div_le_one_div_of_le hγ hγw
  · show |(1 / ((j + 2).factorial : ℝ)) *
      ∫ t in {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ},
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹| ≤ (1 / γ) ^ (j + 2) / ((j + 2).factorial : ℝ)
    set s := {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} with hs
    have hsub : s ⊆ Set.Icc (0 : Fin (j + 1) → ℝ) 1 := by
      intro t ht
      refine ⟨fun i => le_trans hγ.le (ht.1 i), fun i => ?_⟩
      have h0 : ∀ i ∈ Finset.univ, 0 ≤ t i := fun i _ => le_trans hγ.le (ht.1 i)
      have := Finset.single_le_sum h0 (Finset.mem_univ i)
      simp only [Pi.one_apply]; linarith [ht.2]
    have hvol : volume s ≤ 1 := by
      calc volume s ≤ volume (Set.Icc (0 : Fin (j + 1) → ℝ) 1) := measure_mono hsub
        _ = 1 := by simp [Real.volume_Icc_pi]
    have hbound : ∀ t ∈ s, ‖(w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹‖ ≤ (1 / γ) ^ (j + 2) := by
      intro t ht
      have h1 : γ ≤ w - ∑ i, t i := by linarith [ht.2]
      rw [norm_mul, norm_prod, show j + 2 = (j + 1) + 1 by rfl, pow_succ']
      apply mul_le_mul
      · rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hγ.trans_le h1), ← one_div]
        exact one_div_le_one_div_of_le hγ h1
      · calc ∏ i, ‖(t i)⁻¹‖ ≤ ∏ _i : Fin (j + 1), 1 / γ := by
              apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
              intro i _
              rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hγ.trans_le (ht.1 i)), ← one_div]
              exact one_div_le_one_div_of_le hγ (ht.1 i)
          _ = (1 / γ) ^ (j + 1) := by simp
      · exact Finset.prod_nonneg fun i _ => norm_nonneg _
      · positivity
    have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (hvol.trans_lt ENNReal.one_lt_top) hbound
    have hreal : volume.real s ≤ 1 := by
      unfold Measure.real
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hvol)
    rw [Real.norm_eq_abs] at hint
    have hI : |∫ t in s, (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹| ≤ (1 / γ) ^ (j + 2) :=
      calc _ ≤ (1 / γ) ^ (j + 2) * volume.real s := hint
        _ ≤ (1 / γ) ^ (j + 2) * 1 := by gcongr
        _ = _ := mul_one _
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / ((j + 2).factorial : ℝ) * |∫ t in s, (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹|
        ≤ 1 / ((j + 2).factorial : ℝ) * (1 / γ) ^ (j + 2) := by gcongr
      _ = _ := by ring

lemma roughDensity_abs_le (γ w : ℝ) (hγ : 0 < γ) (hγw : γ ≤ w) (hw : w ≤ 1) :
    |roughDensity γ w| ≤ ∑' j : ℕ, (1 / γ) ^ j / (j.factorial : ℝ) := by
  have hg : Summable (fun j : ℕ => (1 / γ) ^ j / (j.factorial : ℝ)) :=
    Real.summable_pow_div_factorial _
  have hb := roughDensityTerm_abs_le γ w hγ hγw hw
  have hfn : Summable (fun j => ‖roughDensityTerm γ w j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => by simpa using hb j) hg
  unfold roughDensity
  rw [← Real.norm_eq_abs]
  calc ‖∑' j, roughDensityTerm γ w j‖ ≤ ∑' j, ‖roughDensityTerm γ w j‖ :=
        norm_tsum_le_tsum_norm hfn
    _ ≤ _ := Summable.tsum_le_tsum (fun j => by simpa using hb j) hfn hg

/-! ## The Mertens product at the sieve level -/

lemma mertensProduct_nonneg (y : ℝ) : 0 ≤ mertensProduct y := by
  unfold mertensProduct
  apply Finset.prod_nonneg
  intro p hp
  have : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt
  rw [sub_nonneg, div_le_one (by linarith)]; exact this.le

lemma tendsto_sieveLevel : Tendsto sieveLevel atTop atTop :=
  Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop)

lemma eventually_LV : ∃ c > 0, ∀ᶠ x in atTop, c ≤ log x * mertensProduct (sieveLevel x) := by
  set c0 := exp (-eulerMascheroniConstant)
  have hc0 : 0 < c0 := exp_pos _
  refine ⟨c0 / 2, by positivity, ?_⟩
  have h1 := mertens_product.eventually (eventually_gt_nhds (by linarith : c0 / 2 < c0))
  filter_upwards [tendsto_sieveLevel.eventually h1,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  have hlog : log (sieveLevel x) = log x ^ (0.24 : ℝ) := by unfold sieveLevel; exact Real.log_exp _
  simp only [hlog] at hx
  have h2 : log x ^ (0.24 : ℝ) ≤ log x := by
    calc log x ^ (0.24 : ℝ) ≤ log x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = log x := Real.rpow_one _
  have h3 := mertensProduct_nonneg (sieveLevel x)
  nlinarith

lemma eventually_proxy_bound (γ : ℝ) (hγ : 0 < γ) : ∃ Cα : ℝ, ∀ᶠ x in atTop, ∀ w : ℝ, γ ≤ w →
    w ≤ 1 → |roughDensity γ w / (log x * mertensProduct (sieveLevel x))| ≤ Cα := by
  obtain ⟨c, hc, hev⟩ := eventually_LV
  set R := ∑' j : ℕ, (1 / γ) ^ j / (j.factorial : ℝ)
  refine ⟨R / c, ?_⟩
  filter_upwards [hev] with x hx w hw1 hw2
  rw [abs_div, abs_of_pos (hc.trans_le hx)]
  have hR := roughDensity_abs_le γ w hγ hw1 hw2
  exact div_le_div₀ ((abs_nonneg _).trans hR) hR hc hx

/-! ## The coefficient `(10.13)` -/

open Classical in
/-- The coefficient `1_J(m) m^{iv} (R_γ(m) - B_γ(m))` of Proposition 10.3. -/
noncomputable def coefN (γ x : ℝ) (J : Set ℝ) (v : ℝ) (m : ℕ) : ℂ :=
  if (m : ℝ) ∈ J then
    (m : ℂ) ^ (Complex.I * v) *
      ((if IsRough (x ^ γ) m then 1 else 0) -
        ((roughDensity γ (log m / log x) /
            (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
          (if IsRough (sieveLevel x) m then 1 else 0))
  else 0

lemma isRough_mono {y y' : ℝ} {m : ℕ} (h : IsRough y m) (hy : y' ≤ y) : IsRough y' m :=
  ⟨h.1, fun p hp => lt_of_le_of_lt hy (h.2 p hp)⟩

lemma coefN_support {γ x : ℝ} {J : Set ℝ} {v : ℝ} {m : ℕ} (hW : sieveLevel x ≤ x ^ γ)
    (h : coefN γ x J v m ≠ 0) : (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m := by
  classical
  unfold coefN at h
  by_cases hJ : (m : ℝ) ∈ J
  · refine ⟨hJ, ?_⟩
    by_contra hRW
    have hR : ¬ IsRough (x ^ γ) m := fun hR => hRW (isRough_mono hR hW)
    rw [if_pos hJ, if_neg hR, if_neg hRW] at h
    simp at h
  · rw [if_neg hJ] at h; exact absurd rfl h

lemma norm_coefN_le {γ x Cα : ℝ} {J : Set ℝ} {v : ℝ} {m : ℕ} (hm : 0 < m)
    (hρ : |roughDensity γ (log m / log x) / (log x * mertensProduct (sieveLevel x))| ≤ Cα) :
    ‖coefN γ x J v m‖ ≤ 1 + Cα := by
  classical
  have hC : 0 ≤ Cα := (abs_nonneg _).trans hρ
  unfold coefN
  by_cases hJ : (m : ℝ) ∈ J
  · rw [if_pos hJ, norm_mul, Complex.norm_natCast_cpow_of_pos hm]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_zero, one_mul]
    have ha : ∀ P : Prop, [Decidable P] → ‖(if P then (1 : ℂ) else 0)‖ ≤ 1 := by
      intro P _; split_ifs <;> simp
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := ha (IsRough (sieveLevel x) m)
    have h2 := ha (IsRough (x ^ γ) m)
    have h3 := abs_nonneg (roughDensity γ (log m / log x) /
      (log x * mertensProduct (sieveLevel x)))
    have h4 := norm_nonneg (if IsRough (sieveLevel x) m then (1 : ℂ) else 0)
    calc _ ≤ 1 + Cα * 1 := by gcongr
      _ = 1 + Cα := by ring
  · rw [if_neg hJ]; simp; linarith

end ArtinPrimitiveRoots.Prop103

open ArtinPrimitiveRoots ArtinPrimitiveRoots.Prop103 Real Filter in
open Classical in
theorem solution (δ C Dstar q : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hq0 : 0 < q) (hq1 : q < 1) (γ wMinus wPlus : ℝ) (hγ : 0 < γ) (hγw : γ < wMinus) (hww : wMinus < wPlus)
    (hwPlus : wPlus < 1) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → x ^ δ ≤ Hn → c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      wMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ wPlus →
      ∀ F : ℕ → ℂ, (∀ h, 0 < h → ‖F h‖ ≤ 1) →
        (∀ h, 0 < h → ∀ p ∈ groupPrimes x a, F (p * h) = F h) →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      ∀ v : ℝ, |v| ≤ log x ^ C →
      ∀ β : ℕ → ℂ,
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ n, ‖β n‖ ≤ log x ^ C) →
      ‖∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          (if (m : ℝ) ∈ J then
            (m : ℂ) ^ (Complex.I * v) *
              ((if IsRough (x ^ γ) m then 1 else 0) -
                ((roughDensity γ (log m / log x) /
                    (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
                  (if IsRough (sieveLevel x) m then 1 else 0))
          else 0) *
          β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-Dstar) := by
  obtain ⟨Cα, hCα⟩ := eventually_proxy_bound γ hγ
  have hlogC := (tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop
  have hlog76 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.76)).comp Real.tendsto_log_atTop
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hCα.and ((eventually_gt_atTop 1).and
    ((Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * c₂))).and
      ((hlogC.eventually_ge_atTop (1 + Cα)).and (hlog76.eventually_ge_atTop (1 / γ))))))
  -- consequences of the threshold
  have hXfacts : ∀ x, X ≤ x → 1 < x ∧ 1 ≤ log x ∧ 2 * c₂ ≤ log x ∧ 1 + Cα ≤ log x ^ C ∧
      sieveLevel x ≤ x ^ γ := by
    intro x hx
    obtain ⟨-, h1, hL, hC', h76⟩ := hX x hx
    simp only [Function.comp] at hC' h76
    refine ⟨h1, le_of_max_le_left hL, le_of_max_le_right hL, hC', ?_⟩
    have hL0 : 0 < log x := Real.log_pos h1
    unfold sieveLevel
    rw [show x ^ γ = exp (log x * γ) from Real.rpow_def_of_pos (by linarith) γ, Real.exp_le_exp]
    have hsplit : log x = log x ^ (0.24 : ℝ) * log x ^ (0.76 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h24 : 0 ≤ log x ^ (0.24 : ℝ) := by positivity
    have : log x ^ (0.24 : ℝ) * 1 ≤ log x ^ (0.24 : ℝ) * (log x ^ (0.76 : ℝ) * γ) := by
      apply mul_le_mul_of_nonneg_left _ h24
      rw [div_le_iff₀ hγ] at h76; linarith
    calc log x ^ (0.24 : ℝ) = log x ^ (0.24 : ℝ) * 1 := (mul_one _).symm
      _ ≤ _ := this
      _ = log x ^ (0.24 : ℝ) * log x ^ (0.76 : ℝ) * γ := by ring
      _ = log x * γ := by rw [← hsplit]
  -- the set of tuples
  let P : ℝ → ℝ → ℝ → (ℕ → ℂ) → (ℕ → ℂ) → Prop := fun x Hm Hn α β =>
    X ≤ x ∧ x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
    wMinus ≤ log Hm / log x ∧ log (2 * Hm) / log x ≤ wPlus ∧
    (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧ ∃ v : ℝ, |v| ≤ log x ^ C ∧
      α = coefN γ x J v) ∧
    (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
    (∀ n, ‖β n‖ ≤ log x ^ C)
  let S : Set (ℝ × ℝ × ℝ × (ℕ → ℂ) × (ℕ → ℂ)) :=
    {p | P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2}
  have hS : ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S →
      x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
      (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
        ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) ∧
      (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
      (∀ m, ‖α m‖ ≤ log x ^ C) ∧ (∀ n, ‖β n‖ ≤ log x ^ C) := by
    rintro x Hm Hn α β ⟨hxX, h1, h2, h3, h4, hw1, hw2, ⟨J, hJ, hJs, v, hv, hαe⟩, hβ1, hβ2⟩
    dsimp only at hαe hxX h1 h2 h3 h4 hw1 hw2 hβ1 hβ2 hJ hJs hv; subst hαe
    obtain ⟨hx1, hL1, -, hCα', hW⟩ := hXfacts x hxX
    refine ⟨h1, h2, h3, h4, ⟨J, hJ, hJs, fun m hm => coefN_support hW hm⟩, hβ1, ?_, hβ2⟩
    intro m
    by_cases hmJ : (m : ℝ) ∈ J
    · have hHm : 0 < Hm := lt_of_lt_of_le (by positivity) h1
      have hmI := hJs hmJ
      have hm0 : 0 < m := by
        have : (0 : ℝ) < m := lt_of_lt_of_le hHm hmI.1
        exact_mod_cast this
      have hL0 : 0 < log x := by linarith
      have hwa : γ ≤ log m / log x := by
        rw [le_div_iff₀ hL0]
        have := Real.log_le_log hHm hmI.1
        rw [le_div_iff₀ hL0] at hw1
        nlinarith
      have hwb : log m / log x ≤ 1 := by
        rw [div_le_iff₀ hL0]
        have := Real.log_le_log (lt_of_lt_of_le hHm hmI.1) hmI.2
        rw [div_le_iff₀ hL0] at hw2
        nlinarith
      exact (norm_coefN_le hm0 ((hX x hxX).1 _ hwa hwb)).trans hCα'
    · have : coefN γ x J v m = 0 := by unfold coefN; rw [if_neg hmJ]
      rw [this, norm_zero]; positivity
  have hα : ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
        ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * log x ^ B →
          ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
              α m * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A) := by
    intro A₀ B A hA₀ hB hA
    obtain ⟨C', x₀', hcb⟩ := rough_factor_coefficient_bound C γ wMinus wPlus hC hγ hγw hww hwPlus
      A₀ (B + 1) A hA₀ (by linarith) hA
    refine ⟨C', x₀', ?_⟩
    rintro x Hm Hn α β ⟨hxX, h1, h2, h3, h4, hw1, hw2, ⟨J, hJ, hJs, v, hv, hαe⟩, hβ1, hβ2⟩
      hx k hk hkle χ t ht
    dsimp only at hαe hxX h1 h2 h3 h4 hw1 hw2 hβ1 hβ2 hJ hJs hv; subst hαe
    obtain ⟨hx1, hL1, hLc, -, -⟩ := hXfacts x hxX
    have hx0 : 0 < x := by linarith
    have hL0 : 0 < log x := by linarith
    have ht' : |t| ≤ x * log x ^ (B + 1) := by
      rw [Real.rpow_add_one hL0.ne']
      have hLB : 0 ≤ log x ^ B := by positivity
      calc |t| ≤ 2 * (Hm * Hn) * log x ^ B := ht
        _ ≤ 2 * (c₂ * x) * log x ^ B := by gcongr
        _ = (2 * c₂) * (x * log x ^ B) := by ring
        _ ≤ log x * (x * log x ^ B) := by gcongr
        _ = x * (log x ^ B * log x) := by ring
    exact hcb x hx Hm hw1 hw2 J hJ hJs v hv k hk hkle χ t ht'
  obtain ⟨K₀, hK₀⟩ := marked_type_ii_of_coefficient_bound δ C Dstar q hδ hC hD hq0 hq1 c₁ c₂
    hc₁ S hS hα
  refine ⟨K₀, fun K hK1 hK a ha hab => ?_⟩
  obtain ⟨A, x₀, hmain⟩ := hK₀ K hK1 hK a ha hab
  refine ⟨A, max x₀ X, fun x hx Hm Hn h1 h2 h3 h4 hw1 hw2 F hF1 hF2 J hJ hJs v hv β hβ1 hβ2 => ?_⟩
  have hmem : (x, Hm, Hn, coefN γ x J v, β) ∈ S :=
    ⟨le_of_max_le_right hx, h1, h2, h3, h4, hw1, hw2, ⟨J, hJ, hJs, v, hv, rfl⟩, hβ1, hβ2⟩
  exact hmain x Hm Hn _ β hmem (le_of_max_le_left hx) F hF1 hF2
