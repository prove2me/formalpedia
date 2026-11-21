-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.proposition_a_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:51:38.767183+00:00
-- url     : https://prove2.me/submissions/6aee9ffd-ae6b-4686-aaea-eb9e0a0bece6

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri

section
open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.A1

open ApproxSyzygies.Smoothed

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma mem_monos_nat (d : ℕ) (α : σ →₀ ℕ) : α ∈ monos σ (d : ℤ) ↔ ∑ i, α i = d := by
  simp [monos, Finset.mem_finsuppAntidiag]

lemma monos_neg (d : ℤ) (h : d < 0) : monos σ d = ∅ := by
  simp [monos, not_le.2 h]

lemma mfact_pos (α : σ →₀ ℕ) : 0 < mfact α := by
  unfold mfact
  exact Finset.prod_pos fun i _ => by positivity

lemma coeff_toPoly (d : ℕ) (p : Hom σ (d : ℤ)) (α : σ →₀ ℕ) :
    coeff α (toPoly p) =
      if h : α ∈ monos σ (d : ℤ) then p ⟨α, h⟩ * Real.sqrt ((d.factorial : ℝ) / mfact α) else 0 := by
  unfold toPoly
  rw [coeff_sum]
  simp only [coeff_smul, bmono, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨α, h⟩]
    · have : Finsupp.degree α = d := by
        rw [Finsupp.degree_eq_sum]; exact (mem_monos_nat d α).1 h
      simp [this]
    · intro b _ hb
      have : (b : σ →₀ ℕ) ≠ α := fun e => hb (Subtype.ext e)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : (b : σ →₀ ℕ) ≠ α := fun e => h (e ▸ b.2)
    simp [this]

lemma normsq_ofPoly (e : ℤ) (f : MvPolynomial σ ℝ) :
    ‖ofPoly e f‖ ^ 2 = ∑ α ∈ monos σ e, (coeff α f) ^ 2 * mfact α / (e.toNat.factorial : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_coe_sort (monos σ e)]
  apply Finset.sum_congr rfl
  intro α _
  simp only [ofPoly, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [Real.sq_sqrt (div_nonneg (mfact_pos _).le (by positivity))]
  ring

lemma normsq_hom (d : ℕ) (p : Hom σ (d : ℤ)) :
    ‖p‖ ^ 2 = ∑ α ∈ monos σ (d : ℤ), (coeff α (toPoly p)) ^ 2 * mfact α / (d.factorial : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_coe_sort (monos σ (d : ℤ))]
  apply Finset.sum_congr rfl
  intro α _
  rw [coeff_toPoly, dif_pos α.2]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow]
  rw [Real.sq_sqrt (div_nonneg (by positivity) (mfact_pos _).le)]
  have := mfact_pos (α : σ →₀ ℕ)
  have h2 : (0:ℝ) < d.factorial := by positivity
  field_simp


lemma mfact_add_single (β : σ →₀ ℕ) (ℓ : σ) :
    mfact (β + Finsupp.single ℓ 1) = mfact β * ((β ℓ : ℝ) + 1) := by
  unfold mfact
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase Finset.univ (fun i => ((β i).factorial : ℝ)) (Finset.mem_univ ℓ)]
  have : ∏ i ∈ Finset.univ.erase ℓ, (((β + Finsupp.single ℓ 1 : σ →₀ ℕ) i).factorial : ℝ) =
      ∏ i ∈ Finset.univ.erase ℓ, ((β i).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro i hi
    have : i ≠ ℓ := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, this.symm]
  rw [this]
  simp [Nat.factorial_succ]
  ring

lemma sum_reindex (k : ℕ) (ℓ : σ) (G : (σ →₀ ℕ) → ℝ) (hG : ∀ α, α ℓ = 0 → G α = 0) :
    ∑ β ∈ monos σ (k : ℤ), G (β + Finsupp.single ℓ 1) =
      ∑ α ∈ monos σ ((k + 1 : ℕ) : ℤ), G α := by
  have hinj : Function.Injective (fun β : σ →₀ ℕ => β + Finsupp.single ℓ 1) :=
    fun a b h => add_right_cancel h
  rw [← Finset.sum_image (f := G) (g := fun β : σ →₀ ℕ => β + Finsupp.single ℓ 1)
    (fun a _ b _ h => hinj h)]
  apply Finset.sum_subset
  · intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨β, hβ, rfl⟩ := hα
    rw [mem_monos_nat] at hβ ⊢
    simp [Finsupp.add_apply, Finset.sum_add_distrib, hβ, Finsupp.single_apply]
  · intro α hα hnot
    apply hG
    by_contra hne
    apply hnot
    rw [Finset.mem_image]
    refine ⟨α - Finsupp.single ℓ 1, ?_, ?_⟩
    · rw [mem_monos_nat]
      rw [mem_monos_nat] at hα
      have h1 : ∑ i, (α - Finsupp.single ℓ 1 : σ →₀ ℕ) i + 1 = ∑ i, α i := by
        have : α = (α - Finsupp.single ℓ 1) + Finsupp.single ℓ 1 := by
          ext i
          by_cases h : i = ℓ
          · subst h; simp; omega
          · simp [Finsupp.single_apply, Ne.symm h]
        conv_rhs => rw [this]
        simp [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]
      omega
    · ext i
      by_cases h : i = ℓ
      · subst h; simp; omega
      · simp [Finsupp.single_apply, Ne.symm h]

lemma part1_pos (k : ℕ) (p : Hom σ ((k + 1 : ℕ) : ℤ)) :
    ∑ ℓ : σ, ‖ofPoly (((k + 1 : ℕ) : ℤ) - 1) (pderiv ℓ (toPoly p))‖ ^ 2 =
      ((k + 1 : ℕ) : ℝ) ^ 2 * ‖p‖ ^ 2 := by
  have e : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
  rw [e, normsq_hom]
  simp only [normsq_ofPoly, Int.toNat_natCast, coeff_pderiv]
  set c := fun α => coeff α (toPoly p) with hc
  have step : ∀ ℓ : σ, ∑ β ∈ monos σ (k : ℤ),
      (coeff (β + Finsupp.single ℓ 1) (toPoly p) * ((β ℓ : ℝ) + 1)) ^ 2 * mfact β / (k.factorial : ℝ) =
      ∑ α ∈ monos σ ((k + 1 : ℕ) : ℤ), (c α) ^ 2 * (α ℓ : ℝ) * mfact α / (k.factorial : ℝ) := by
    intro ℓ
    rw [← sum_reindex k ℓ (fun α => (c α) ^ 2 * (α ℓ : ℝ) * mfact α / (k.factorial : ℝ))]
    · apply Finset.sum_congr rfl
      intro β _
      simp only [hc, mfact_add_single]
      simp
      ring
    · intro α h
      simp [h]
  simp_rw [step]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [mem_monos_nat] at hα
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have h1 : ∑ ℓ, (α ℓ : ℝ) = (k + 1 : ℕ) := by exact_mod_cast hα
  rw [← Finset.mul_sum, h1]
  have : ((k + 1).factorial : ℝ) = (k + 1 : ℕ) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [this]
  have hk : (0:ℝ) < (k + 1 : ℕ) := by positivity
  have hk2 : (0:ℝ) < k.factorial := by positivity
  field_simp
  simp only [hc]
  ring

lemma part1 (n : ℕ) (d : ℕ) (p : Hom (Fin n) (d : ℤ)) :
    ∑ ℓ : Fin n, ‖ofPoly ((d : ℤ) - 1) (pderiv ℓ (toPoly p))‖ ^ 2 = (d : ℝ) ^ 2 * ‖p‖ ^ 2 := by
  cases d with
  | zero =>
    have h0 : monos (Fin n) (-1) = ∅ := monos_neg _ (by norm_num)
    simp [normsq_ofPoly, h0]
  | succ k => exact part1_pos k p


lemma sub_single_add (α : σ →₀ ℕ) (ℓ : σ) (h : α ℓ ≠ 0) :
    α - Finsupp.single ℓ 1 + Finsupp.single ℓ 1 = α := by
  ext i
  by_cases hi : i = ℓ
  · subst hi; simp; omega
  · simp [Finsupp.single_apply, Ne.symm hi]

lemma mfact_eq_of_ne (α : σ →₀ ℕ) (ℓ : σ) (h : α ℓ ≠ 0) :
    mfact α = mfact (α - Finsupp.single ℓ 1) * (α ℓ : ℝ) := by
  conv_lhs => rw [← sub_single_add α ℓ h]
  rw [mfact_add_single]
  congr 1
  have : (α - Finsupp.single ℓ 1 : σ →₀ ℕ) ℓ + 1 = α ℓ := by simp; omega
  rw [← this]; push_cast; ring

lemma part2 (d : ℕ) (p : σ → Hom σ (d : ℤ)) :
    ‖ofPoly ((d : ℤ) + 1) (∑ ℓ : σ, X ℓ * toPoly (p ℓ))‖ ^ 2 ≤ ∑ ℓ : σ, ‖p ℓ‖ ^ 2 := by
  have e : ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, normsq_ofPoly]
  simp only [Int.toNat_natCast]
  set H : σ → (σ →₀ ℕ) → ℝ := fun ℓ α =>
    if α ℓ ≠ 0 then (coeff (α - Finsupp.single ℓ 1) (toPoly (p ℓ))) ^ 2 *
      mfact (α - Finsupp.single ℓ 1) / (d.factorial : ℝ) else 0 with hH
  have hk : (0:ℝ) < (d + 1 : ℕ) := by positivity
  have hk2 : (0:ℝ) < d.factorial := by positivity
  have pt : ∀ α ∈ monos σ ((d + 1 : ℕ) : ℤ),
      (coeff α (∑ ℓ : σ, X ℓ * toPoly (p ℓ))) ^ 2 * mfact α / ((d + 1).factorial : ℝ) ≤
        ∑ ℓ, H ℓ α := by
    intro α hα
    rw [mem_monos_nat] at hα
    set s := Finset.univ.filter (fun ℓ : σ => α ℓ ≠ 0) with hs
    set c : σ → ℝ := fun ℓ => coeff (α - Finsupp.single ℓ 1) (toPoly (p ℓ)) with hc
    have hcoeff : coeff α (∑ ℓ : σ, X ℓ * toPoly (p ℓ)) = ∑ ℓ ∈ s, c ℓ := by
      rw [coeff_sum, hs, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [coeff_X_mul']
      simp [hc, Finsupp.mem_support_iff]
    have hsum : ∑ ℓ ∈ s, (α ℓ : ℝ) = (d + 1 : ℕ) := by
      rw [hs, Finset.sum_filter]
      have : ∑ ℓ, (if α ℓ ≠ 0 then (α ℓ : ℝ) else 0) = ∑ ℓ, (α ℓ : ℝ) := by
        apply Finset.sum_congr rfl; intro ℓ _; split_ifs with h
        · rfl
        · simp at h; simp [h]
      rw [this]; exact_mod_cast hα
    have hpos : ∀ ℓ ∈ s, 0 < (α ℓ : ℝ) := by
      intro ℓ hℓ
      have : α ℓ ≠ 0 := (Finset.mem_filter.1 hℓ).2
      positivity
    have sed := Finset.sq_sum_div_le_sum_sq_div s c hpos
    rw [hsum] at sed
    rw [div_le_iff₀ hk] at sed
    have hfa : ((d + 1).factorial : ℝ) = (d + 1 : ℕ) * d.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hcoeff, hfa]
    have hmf := mfact_pos α
    calc (∑ ℓ ∈ s, c ℓ) ^ 2 * mfact α / ((d + 1 : ℕ) * d.factorial)
        ≤ ((∑ ℓ ∈ s, c ℓ ^ 2 / (α ℓ : ℝ)) * (d + 1 : ℕ)) * mfact α / ((d + 1 : ℕ) * d.factorial) := by
          gcongr
      _ = ∑ ℓ ∈ s, c ℓ ^ 2 * (mfact α / (α ℓ : ℝ)) / d.factorial := by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          have := hpos ℓ hℓ
          field_simp
      _ = ∑ ℓ, H ℓ α := by
          rw [hs, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro ℓ _
          by_cases h : α ℓ ≠ 0
          · simp only [hH, hc, if_pos h]
            rw [mfact_eq_of_ne α ℓ h]
            have : (0:ℝ) < α ℓ := by positivity
            field_simp
          · simp [hH, h]
  refine (Finset.sum_le_sum pt).trans ?_
  rw [Finset.sum_comm]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [normsq_hom, ← sum_reindex d ℓ (H ℓ)]
  · apply Finset.sum_congr rfl
    intro β _
    simp [hH]
  · intro α h
    simp [hH, h]


lemma vand_nat (γ : σ →₀ ℕ) (d1 : ℕ) :
    ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) d1, ∏ i, (γ i).choose (l i) =
      (∑ i, γ i).choose d1 := by
  have h1 : (((∏ i : σ, ((1 + Polynomial.X : Polynomial ℕ) ^ (γ i)) : Polynomial ℕ)) :
      PowerSeries ℕ) = ∏ i : σ, ((((1 + Polynomial.X : Polynomial ℕ) ^ (γ i) : Polynomial ℕ)) :
      PowerSeries ℕ) := map_prod (Polynomial.coeToPowerSeries.ringHom) _ _
  have h2 : (∏ i : σ, ((1 + Polynomial.X : Polynomial ℕ) ^ (γ i))) =
      (1 + Polynomial.X : Polynomial ℕ) ^ (∑ i, γ i) := Finset.prod_pow_eq_pow_sum _ _ _
  have h3 := PowerSeries.coeff_prod (fun i => ((((1 + Polynomial.X : Polynomial ℕ) ^ (γ i) :
      Polynomial ℕ)) : PowerSeries ℕ)) d1 Finset.univ
  rw [← h1, h2, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow] at h3
  rw [Nat.cast_id] at h3
  rw [h3]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.cast_id]

lemma vand (γ : σ →₀ ℕ) (d1 : ℕ) :
    ∑ α ∈ monos σ (d1 : ℤ), ∏ i, ((γ i).choose (α i) : ℝ) = ((∑ i, γ i).choose d1 : ℝ) := by
  have := vand_nat γ d1
  have h : monos σ (d1 : ℤ) = Finset.finsuppAntidiag (Finset.univ : Finset σ) d1 := by
    simp [monos]
  rw [h]
  exact_mod_cast this


lemma sum_add_apply (x y : σ →₀ ℕ) : ∑ i, (x + y) i = ∑ i, x i + ∑ i, y i := by
  simp [Finsupp.add_apply, Finset.sum_add_distrib]

lemma mfact_split (α γ : σ →₀ ℕ) (h : α ≤ γ) :
    mfact γ = (∏ i, ((γ i).choose (α i) : ℝ)) * mfact α * mfact (γ - α) := by
  unfold mfact
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi : α i ≤ γ i := h i
  have := Nat.choose_mul_factorial_mul_factorial hi
  simp only [Finsupp.tsub_apply]
  exact_mod_cast this.symm

lemma coeff_mul_eq (d1 : ℕ) (f g : MvPolynomial σ ℝ)
    (hf : ∀ α, α ∉ monos σ (d1 : ℤ) → coeff α f = 0) (γ : σ →₀ ℕ) :
    coeff γ (f * g) = ∑ α ∈ (monos σ (d1 : ℤ)).filter (· ≤ γ), coeff α f * coeff (γ - α) g := by
  rw [coeff_mul]
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1) ?_ ?_ ?_ ?_
  · intro x hx hne
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · by_contra hn
      apply hne
      rw [hf _ hn, zero_mul]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [← hx]; exact le_self_add
  · intro x hx _ y hy _ h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    have h1 : x.1 = y.1 := h
    ext1
    · exact h1
    · have : x.2 = y.2 := by
        have := hx.trans hy.symm
        rw [h1] at this
        exact add_left_cancel this
      exact this
  · intro α hα hne
    rw [Finset.mem_filter] at hα
    refine ⟨(α, γ - α), ?_, hne, rfl⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact add_tsub_cancel_of_le hα.2
  · intro x hx _
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have : γ - x.1 = x.2 := by rw [← hx]; exact add_tsub_cancel_left _ _
    simp [this]

lemma sum_double (d1 d2 : ℕ) (K : (σ →₀ ℕ) → (σ →₀ ℕ) → ℝ) :
    ∑ γ ∈ monos σ ((d1 + d2 : ℕ) : ℤ), ∑ α ∈ (monos σ (d1 : ℤ)).filter (· ≤ γ), K α (γ - α) =
      ∑ α ∈ monos σ (d1 : ℤ), ∑ β ∈ monos σ (d2 : ℤ), K α β := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  rw [← Finset.sum_filter]
  rw [mem_monos_nat] at hα
  symm
  refine Finset.sum_nbij' (fun β => α + β) (fun γ => γ - α) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    rw [mem_monos_nat] at hβ
    rw [Finset.mem_filter, mem_monos_nat, sum_add_apply, hα, hβ]
    exact ⟨rfl, le_self_add⟩
  · intro γ hγ
    rw [Finset.mem_filter, mem_monos_nat] at hγ
    rw [mem_monos_nat]
    have h := sum_add_apply (γ - α) α
    rw [tsub_add_cancel_of_le hγ.2, hγ.1, hα] at h
    omega
  · intro β _; exact add_tsub_cancel_left _ _
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact add_tsub_cancel_of_le hγ.2
  · intro β _
    rw [add_tsub_cancel_left]


lemma part3 (d1 d2 : ℕ) (p : Hom σ (d1 : ℤ)) (q : Hom σ (d2 : ℤ)) :
    ‖ofPoly ((d1 : ℤ) + d2) (toPoly p * toPoly q)‖ ≤ ‖p‖ * ‖q‖ := by
  have e : ((d1 : ℤ) + d2) = ((d1 + d2 : ℕ) : ℤ) := by push_cast; ring
  set a : (σ →₀ ℕ) → ℝ := fun α => coeff α (toPoly p) with ha
  set b : (σ →₀ ℕ) → ℝ := fun α => coeff α (toPoly q) with hb
  have hfa : ∀ α, α ∉ monos σ (d1 : ℤ) → coeff α (toPoly p) = 0 := by
    intro α h; rw [coeff_toPoly, dif_neg h]
  set K : (σ →₀ ℕ) → (σ →₀ ℕ) → ℝ := fun α β =>
    a α ^ 2 * mfact α / (d1.factorial : ℝ) * (b β ^ 2 * mfact β / (d2.factorial : ℝ)) with hK
  have hR : (‖p‖ * ‖q‖) ^ 2 = ∑ α ∈ monos σ (d1 : ℤ), ∑ β ∈ monos σ (d2 : ℤ), K α β := by
    rw [mul_pow, normsq_hom d1 p, normsq_hom d2 q, Finset.sum_mul_sum]
  have hL : ‖ofPoly ((d1 : ℤ) + d2) (toPoly p * toPoly q)‖ ^ 2 ≤
      ∑ α ∈ monos σ (d1 : ℤ), ∑ β ∈ monos σ (d2 : ℤ), K α β := by
    rw [e, normsq_ofPoly, Int.toNat_natCast, ← sum_double d1 d2 K]
    apply Finset.sum_le_sum
    intro γ hγ
    rw [mem_monos_nat] at hγ
    set T := (monos σ (d1 : ℤ)).filter (· ≤ γ) with hT
    rw [coeff_mul_eq d1 _ _ hfa γ]
    set w : (σ →₀ ℕ) → ℝ := fun α => ∏ i, ((γ i).choose (α i) : ℝ) with hw
    have hwpos : ∀ α ∈ T, 0 < w α := by
      intro α hα
      have hle : α ≤ γ := (Finset.mem_filter.1 hα).2
      apply Finset.prod_pos
      intro i _
      exact_mod_cast Nat.choose_pos (hle i)
    have hwsum : ∑ α ∈ T, w α = ((d1 + d2).choose d1 : ℝ) := by
      rw [← hγ, ← vand γ d1, hT, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro α _
      split_ifs with h
      · rfl
      · symm
        simp only [Finsupp.le_def, not_forall, not_le] at h
        obtain ⟨i, hi⟩ := h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact_mod_cast Nat.choose_eq_zero_of_lt hi
    have hCpos : (0:ℝ) < ((d1 + d2).choose d1 : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
    have sed := Finset.sq_sum_div_le_sum_sq_div T (fun α => a α * b (γ - α)) hwpos
    rw [hwsum, div_le_iff₀ hCpos] at sed
    have hfa2 : ((d1 + d2).factorial : ℝ) = ((d1 + d2).choose d1 : ℝ) * d1.factorial * d2.factorial := by
      rw [Nat.choose_symm_add]
      exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial d1 d2).symm
    have hD : (0:ℝ) < ((d1 + d2).factorial : ℝ) := by positivity
    have hmf := mfact_pos γ
    calc (∑ α ∈ T, a α * b (γ - α)) ^ 2 * mfact γ / ((d1 + d2).factorial : ℝ)
        ≤ ((∑ α ∈ T, (a α * b (γ - α)) ^ 2 / w α) * ((d1 + d2).choose d1 : ℝ)) * mfact γ /
            ((d1 + d2).factorial : ℝ) := by gcongr
      _ = ∑ α ∈ T, K α (γ - α) := by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro α hα
          have hle : α ≤ γ := (Finset.mem_filter.1 hα).2
          have h1 := hwpos α hα
          have h2 : mfact γ = w α * mfact α * mfact (γ - α) := mfact_split α γ hle
          have h3 := mfact_pos α
          have h4 := mfact_pos (γ - α)
          have h5 : (0:ℝ) < d1.factorial := by positivity
          have h6 : (0:ℝ) < d2.factorial := by positivity
          rw [h2, hfa2]
          simp only [hK]
          field_simp
  have h2 : ‖ofPoly ((d1 : ℤ) + d2) (toPoly p * toPoly q)‖ ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
    rw [hR]; exact hL
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end ApproxSyzygies.Smoothed.Dev.A1

namespace ApproxSyzygies.Smoothed

theorem chk_proposition_a_1 (n : ℕ) :
    (∀ (d : ℕ) (p : Hom (Fin n) (d : ℤ)),
      ∑ ℓ : Fin n, ‖ofPoly ((d : ℤ) - 1) (pderiv ℓ (toPoly p))‖ ^ 2 = (d : ℝ) ^ 2 * ‖p‖ ^ 2) ∧
    (∀ (d : ℕ) (p : Fin n → Hom (Fin n) (d : ℤ)),
      ‖ofPoly ((d : ℤ) + 1) (∑ ℓ : Fin n, X ℓ * toPoly (p ℓ))‖ ^ 2 ≤ ∑ ℓ : Fin n, ‖p ℓ‖ ^ 2) ∧
    (∀ (d₁ d₂ : ℕ) (p : Hom (Fin n) (d₁ : ℤ)) (q : Hom (Fin n) (d₂ : ℤ)),
      ‖ofPoly ((d₁ : ℤ) + d₂) (toPoly p * toPoly q)‖ ≤ ‖p‖ * ‖q‖) :=
  ⟨fun d p => Dev.A1.part1 n d p, fun d p => Dev.A1.part2 d p,
    fun d₁ d₂ p q => Dev.A1.part3 d₁ d₂ p q⟩

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_proposition_a_1 := @ApproxSyzygies.Smoothed.chk_proposition_a_1
