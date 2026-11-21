-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:58:47.934536+00:00
-- url     : https://prove2.me/submissions/45f0cf5d-7007-46b0-9901-4738f19d5fd0

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

end ApproxSyzygies.Smoothed
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L42

open ApproxSyzygies.Smoothed

/-! ### Homogeneity with integer degrees -/

section Hom

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Homogeneity of integer degree `d` (for `d < 0` only `0` qualifies). -/
def HH (f : MvPolynomial σ ℝ) (d : ℤ) : Prop :=
  IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) f d

lemma weight_one_int (α : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) α = ((∑ i, α i : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

lemma HH_zero (d : ℤ) : HH (0 : MvPolynomial σ ℝ) d := isWeightedHomogeneous_zero _ _ _

lemma HH.add {f g : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (hg : HH g d) : HH (f + g) d :=
  IsWeightedHomogeneous.add hf hg

lemma HH.sub {f g : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (hg : HH g d) : HH (f - g) d :=
  IsWeightedHomogeneous.sub hf hg

lemma HH.smul {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (c : ℝ) : HH (c • f) d :=
  (weightedHomogeneousSubmodule ℝ (fun _ : σ => (1 : ℤ)) d).smul_mem c hf

lemma HH.mul {f g : MvPolynomial σ ℝ} {d e : ℤ} (hf : HH f d) (hg : HH g e) {k : ℤ}
    (hk : k = d + e) : HH (f * g) k := by
  subst hk; exact IsWeightedHomogeneous.mul hf hg

lemma HH_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (d : ℤ)
    (h : ∀ i ∈ s, HH (f i) d) : HH (∑ i ∈ s, f i) d :=
  IsWeightedHomogeneous.sum s f d h

lemma HH_X (ℓ : σ) : HH (X ℓ : MvPolynomial σ ℝ) 1 := isWeightedHomogeneous_X _ _ _

lemma HH.pow {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (n : ℕ) {k : ℤ} (hk : k = d * n) :
    HH (f ^ n) k := by
  have := IsWeightedHomogeneous.pow hf n
  subst hk; rw [nsmul_eq_mul] at this; rwa [mul_comm]

lemma HH.pderiv {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (ℓ : σ) {k : ℤ} (hk : k = d - 1) :
    HH (pderiv ℓ f) k :=
  IsWeightedHomogeneous.pderiv hf (by subst hk; ring)

lemma HH.congr {f : MvPolynomial σ ℝ} {d e : ℤ} (hf : HH f d) (h : d = e) : HH f e := h ▸ hf

lemma HH.eq_zero_of_neg {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (hd : d < 0) : f = 0 := by
  apply IsWeightedHomogeneous.eq_zero_of_no_monomials hf
  intro α h
  rw [weight_one_int] at h
  omega

lemma HH_toPoly {d : ℤ} (p : Hom σ d) : HH (toPoly p) d := by
  unfold toPoly
  apply HH_sum
  intro α _
  apply HH.smul
  unfold bmono
  apply isWeightedHomogeneous_monomial
  rw [weight_one_int]
  have := α.2
  unfold monos at this
  split_ifs at this with hd
  · rw [Finset.mem_finsuppAntidiag] at this
    rw [this.1]; omega
  · simp at this

lemma toPoly_ofPoly {d : ℤ} {f : MvPolynomial σ ℝ} (hf : HH f d) : toPoly (ofPoly d f) = f := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [hf.eq_zero_of_neg hd]
    unfold toPoly
    have : monos σ d = ∅ := Dev.A1.monos_neg d hd
    apply Finset.sum_eq_zero
    intro α _
    exact absurd α.2 (Finset.eq_empty_iff_forall_notMem.1 this _)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    ext α
    rw [Dev.A1.coeff_toPoly]
    split_ifs with h
    · simp only [ofPoly, Int.toNat_natCast]
      change coeff α f * Real.sqrt (mfact α / (n.factorial : ℝ)) *
        Real.sqrt ((n.factorial : ℝ) / mfact α) = coeff α f
      rw [mul_assoc, ← Real.sqrt_mul (div_nonneg (Dev.A1.mfact_pos α).le (by positivity))]
      have h1 := Dev.A1.mfact_pos α
      have h2 : (0 : ℝ) < n.factorial := by positivity
      rw [div_mul_div_comm, mul_comm (mfact α), div_self (by positivity), Real.sqrt_one, mul_one]
    · symm
      apply hf.coeff_eq_zero
      rw [weight_one_int]
      rw [Dev.A1.mem_monos_nat] at h
      omega

lemma ofPoly_toPoly {d : ℤ} (p : Hom σ d) : ofPoly d (toPoly p) = p := by
  rcases lt_or_ge d 0 with hd | hd
  · ext α
    exact absurd α.2 (Finset.eq_empty_iff_forall_notMem.1 (Dev.A1.monos_neg d hd) _)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    ext α
    simp only [ofPoly, Int.toNat_natCast]
    change coeff (α : σ →₀ ℕ) (toPoly p) * Real.sqrt (mfact (α : σ →₀ ℕ) / (n.factorial : ℝ)) = p α
    rw [Dev.A1.coeff_toPoly, dif_pos α.2]
    have h1 := Dev.A1.mfact_pos (α : σ →₀ ℕ)
    have h2 : (0 : ℝ) < n.factorial := by positivity
    rw [mul_assoc, ← Real.sqrt_mul (div_nonneg h2.le h1.le), div_mul_div_comm,
      mul_comm (n.factorial : ℝ), div_self (by positivity), Real.sqrt_one, mul_one]

lemma toPoly_injective {d : ℤ} : Function.Injective (toPoly (σ := σ) (d := d)) := by
  intro p q h
  rw [← ofPoly_toPoly p, ← ofPoly_toPoly q, h]

lemma mem_homSpace {d : ℤ} (f : MvPolynomial σ ℝ) : f ∈ homSpace σ d ↔ HH f d := by
  constructor
  · rintro ⟨p, rfl⟩; exact HH_toPoly p
  · intro h; exact ⟨ofPoly d f, toPoly_ofPoly h⟩

lemma toPoly_add {d : ℤ} (p q : Hom σ d) : toPoly (p + q) = toPoly p + toPoly q :=
  (toPolyL d).map_add p q

lemma toPoly_sub {d : ℤ} (p q : Hom σ d) : toPoly (p - q) = toPoly p - toPoly q :=
  (toPolyL d).map_sub p q

lemma toPoly_smul {d : ℤ} (c : ℝ) (p : Hom σ d) : toPoly (c • p) = c • toPoly p :=
  (toPolyL d).map_smul c p

lemma toPoly_sum {d : ℤ} {ι : Type*} (s : Finset ι) (p : ι → Hom σ d) :
    toPoly (∑ i ∈ s, p i) = ∑ i ∈ s, toPoly (p i) := map_sum (toPolyL d) p s

lemma ofPoly_add {d : ℤ} (f g : MvPolynomial σ ℝ) : ofPoly d (f + g) = ofPoly d f + ofPoly d g :=
  (ofPolyL d).map_add f g

lemma ofPoly_smul {d : ℤ} (c : ℝ) (f : MvPolynomial σ ℝ) : ofPoly d (c • f) = c • ofPoly d f :=
  (ofPolyL d).map_smul c f

lemma ofPoly_zero {d : ℤ} : ofPoly d (0 : MvPolynomial σ ℝ) = 0 := (ofPolyL d).map_zero

lemma mulMap_apply {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (s : ℤ)
    (v : Tup σ (fun i => s - e i)) :
    mulMap p s v = ∑ i, ofPoly s (toPoly (p i) * toPoly (v i)) := by
  simp [mulMap, LinearMap.sum_apply, ofPolyL, toPolyL]
  rfl

lemma toPoly_mulMap {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (s : ℤ)
    (v : Tup σ (fun i => s - e i)) :
    toPoly (mulMap p s v) = ∑ i, toPoly (p i) * toPoly (v i) := by
  rw [mulMap_apply, toPoly_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact toPoly_ofPoly ((HH_toPoly _).mul (HH_toPoly _) (by ring))

/-- Integer-degree version of Proposition A.1(2). -/
lemma part2Z (d d' : ℤ) (hd : d' = d + 1) (p : σ → Hom σ d) :
    ‖ofPoly d' (∑ ℓ : σ, X ℓ * toPoly (p ℓ))‖ ^ 2 ≤ ∑ ℓ : σ, ‖p ℓ‖ ^ 2 := by
  subst hd
  rcases lt_or_ge d 0 with h | h
  · have : ∀ ℓ, toPoly (p ℓ) = 0 := fun ℓ => (HH_toPoly (p ℓ)).eq_zero_of_neg h
    calc _ = (0:ℝ) := by simp [this, ofPoly_zero]
      _ ≤ _ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact Dev.A1.part2 n p

/-- Integer-degree version of Proposition A.1(3). -/
lemma part3Z (d1 d2 d3 : ℤ) (hd : d3 = d1 + d2) (p : Hom σ d1) (q : Hom σ d2) :
    ‖ofPoly d3 (toPoly p * toPoly q)‖ ≤ ‖p‖ * ‖q‖ := by
  subst hd
  rcases lt_or_ge d1 0 with h1 | h1
  · rw [(HH_toPoly p).eq_zero_of_neg h1, zero_mul, ofPoly_zero, norm_zero]; positivity
  rcases lt_or_ge d2 0 with h2 | h2
  · rw [(HH_toPoly q).eq_zero_of_neg h2, mul_zero, ofPoly_zero, norm_zero]; positivity
  obtain ⟨n1, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨n2, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  exact Dev.A1.part3 n1 n2 p q

/-- Euler's identity with integer degree. -/
lemma euler {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) :
    ∑ ℓ : σ, X ℓ * pderiv ℓ f = (d : ℝ) • f := by
  rcases lt_or_ge d 0 with h | h
  · rw [hf.eq_zero_of_neg h]; simp
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have hH : f.IsHomogeneous n := by
      intro α hα
      have := hf hα
      rw [weight_one_int] at this
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp only [Pi.one_apply, smul_eq_mul, mul_one]
      exact_mod_cast this
    rw [hH.sum_X_mul_pderiv, ← Nat.cast_smul_eq_nsmul ℝ]
    simp

end Hom

/-! ### The pure-`y` part -/

section YPart

variable {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The substitution `z ↦ 0`. -/
noncomputable abbrev rho : MvPolynomial (Y ⊕ Z) ℝ →ₐ[ℝ] MvPolynomial Y ℝ :=
  aeval (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)))

lemma HH_rho {f : MvPolynomial (Y ⊕ Z) ℝ} {d : ℤ} (hf : HH f d) :
    HH (rho (Y := Y) (Z := Z) f) d := by
  unfold HH at hf ⊢
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hf
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) hf
  · rintro _ ⟨α, hα, rfl⟩
    rw [Set.mem_ofPred] at hα
    change IsWeightedHomogeneous _ (rho (monomial α (1:ℝ))) d
    rw [aeval_monomial, map_one, one_mul]
    have hfac : ∀ i : Y ⊕ Z, HH (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)) i) 1 := by
      intro i
      cases i with
      | inl y => exact HH_X y
      | inr z => exact HH_zero 1
    have : IsWeightedHomogeneous (fun _ : Y => (1 : ℤ)) (α.prod fun i k => (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)) i) ^ k) d := by
      unfold Finsupp.prod
      have := IsWeightedHomogeneous.prod (w := fun _ : Y => (1 : ℤ)) α.support
        (fun i => (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)) i) ^ (α i))
        (fun i => ((α i : ℕ) : ℤ)) (fun i _ => (hfac i).pow (α i) (by ring))
      convert this using 1
      rw [← hα, Finsupp.weight_apply]
      simp [Finsupp.sum]
    exact this
  · rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  · rw [map_add]; exact hp.add hq
  · rw [map_smul]; exact (weightedHomogeneousSubmodule ℝ _ d).smul_mem r h

lemma toPoly_yPart {d : ℤ} (f : Hom (Y ⊕ Z) d) : toPoly (yPart f) = rho (toPoly f) :=
  toPoly_ofPoly (HH_rho (HH_toPoly f))

lemma yPart_mulMap {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom (Y ⊕ Z) (e i)) (s : ℤ)
    (h : Tup (Y ⊕ Z) (fun i => s - e i)) :
    yPart (mulMap p s h) = mulMap (yParts p) s (yPartTup h) := by
  apply toPoly_injective
  rw [toPoly_yPart, toPoly_mulMap, toPoly_mulMap, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  simp only [yParts, yPartTup, toPoly_yPart]

lemma toPoly_yParts_pow {d : ℤ} (a : Hom (Y ⊕ Z) d) (D : ℕ) :
    toPoly (yPart (powHom a D)) = toPoly (yPart a) ^ D := by
  rw [toPoly_yPart, toPoly_yPart, powHom, toPoly_ofPoly ((HH_toPoly a).pow D rfl), map_pow]

end YPart

/-! ### The pseudoinverse -/

section Pinv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `M` restricted to `(ker M)ᗮ`, onto its range. -/
noncomputable def resEquiv (M : E →ₗ[ℝ] F) :
    (LinearMap.ker M)ᗮ ≃ₗ[ℝ] LinearMap.range M :=
  LinearEquiv.ofBijective
    ((M.domRestrict (LinearMap.ker M)ᗮ).codRestrict (LinearMap.range M)
      (fun x => LinearMap.mem_range_self M _))
    (by
      constructor
      · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have h1 : (x : E) ∈ LinearMap.ker M := by
          rw [LinearMap.mem_ker]
          exact congrArg Subtype.val hx
        have h2 := x.2
        have : (x : E) = 0 := by
          have := Submodule.inf_orthogonal_eq_bot (LinearMap.ker M)
          rw [Submodule.eq_bot_iff] at this
          exact this _ ⟨h1, h2⟩
        exact Subtype.ext this
      · rintro ⟨y, x, rfl⟩
        obtain ⟨x1, hx1, x2, hx2, hsum⟩ :=
          Submodule.exists_add_mem_mem_orthogonal (K := LinearMap.ker M) x
        refine ⟨⟨x2, hx2⟩, ?_⟩
        apply Subtype.ext
        change M x2 = M x
        rw [hsum, map_add, LinearMap.mem_ker.1 hx1, zero_add])

lemma resEquiv_apply (M : E →ₗ[ℝ] F) (x : (LinearMap.ker M)ᗮ) :
    ((resEquiv M x : LinearMap.range M) : F) = M x := rfl

/-- The Moore–Penrose pseudoinverse. -/
noncomputable def Wl (M : E →ₗ[ℝ] F) : F →ₗ[ℝ] E :=
  (LinearMap.ker M)ᗮ.subtype ∘ₗ (resEquiv M).symm.toLinearMap ∘ₗ
    ((LinearMap.range M).orthogonalProjectionOnto : F →ₗ[ℝ] LinearMap.range M)

lemma M_Wl (M : E →ₗ[ℝ] F) (v : F) :
    M (Wl M v) = (LinearMap.range M).starProjection v := by
  simp only [Wl, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
  rw [← resEquiv_apply, LinearEquiv.apply_symm_apply]
  rfl

lemma Wl_mem (M : E →ₗ[ℝ] F) (v : F) : Wl M v ∈ (LinearMap.ker M)ᗮ := by
  simp only [Wl, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  exact Submodule.coe_mem _

lemma Wl_spec (M : E →ₗ[ℝ] F) (x : E) : Wl M (M x) - x ∈ LinearMap.ker M := by
  rw [LinearMap.mem_ker, map_sub, M_Wl,
    Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self M x), sub_self]

lemma pinvNorm_nonneg (M : E →ₗ[ℝ] F) : 0 ≤ pinvNorm M :=
  Real.sInf_nonneg (fun _ h => h.1)

lemma pinv_bound (M : E →ₗ[ℝ] F) (u : E) (hu : u ∈ (LinearMap.ker M)ᗮ) :
    ‖u‖ ≤ pinvNorm M * ‖M u‖ := by
  set S := {τ : ℝ | 0 ≤ τ ∧ ∀ u ∈ (LinearMap.ker M)ᗮ, ‖u‖ ≤ τ * ‖M u‖}
  have hne : S.Nonempty := by
    refine ⟨‖LinearMap.toContinuousLinearMap (resEquiv M).symm.toLinearMap‖, ContinuousLinearMap.opNorm_nonneg _,
      fun w hw => ?_⟩
    have h1 : (resEquiv M).symm (resEquiv M ⟨w, hw⟩) = ⟨w, hw⟩ := LinearEquiv.symm_apply_apply _ _
    have h2 := (LinearMap.toContinuousLinearMap (resEquiv M).symm.toLinearMap).le_opNorm
      (resEquiv M ⟨w, hw⟩)
    simp only [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, h1] at h2
    exact h2
  by_cases h0 : M u = 0
  · have : u = 0 := by
      have := Submodule.inf_orthogonal_eq_bot (LinearMap.ker M)
      rw [Submodule.eq_bot_iff] at this
      exact this _ ⟨LinearMap.mem_ker.2 h0, hu⟩
    rw [this, norm_zero]; exact mul_nonneg (pinvNorm_nonneg M) (norm_nonneg _)
  · have hpos : 0 < ‖M u‖ := norm_pos_iff.2 h0
    have : ‖u‖ / ‖M u‖ ≤ pinvNorm M := by
      apply le_csInf hne
      rintro τ ⟨_, hτ⟩
      rw [div_le_iff₀ hpos]
      exact hτ u hu
    rwa [div_le_iff₀ hpos] at this

lemma Wl_norm (M : E →ₗ[ℝ] F) (v : F) : ‖Wl M v‖ ≤ pinvNorm M * ‖v‖ := by
  refine (pinv_bound M _ (Wl_mem M v)).trans ?_
  rw [M_Wl]
  exact mul_le_mul_of_nonneg_left ((LinearMap.range M).norm_starProjection_apply_le v)
    (pinvNorm_nonneg M)

end Pinv

end ApproxSyzygies.Smoothed.Dev.L42
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L42

open ApproxSyzygies.Smoothed

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- `∂u/∂y_ℓ` in degree `s - 1`. -/
noncomputable def dP (s : ℤ) (ℓ : Y) (u : Hom Y s) : Hom Y (s - 1) :=
  ofPoly (s - 1) (pderiv ℓ (toPoly u))

lemma dP_add (s : ℤ) (ℓ : Y) (u v : Hom Y s) : dP s ℓ (u + v) = dP s ℓ u + dP s ℓ v := by
  simp only [dP, toPoly_add, map_add, ofPoly_add]

lemma dP_smul (s : ℤ) (ℓ : Y) (c : ℝ) (u : Hom Y s) : dP s ℓ (c • u) = c • dP s ℓ u := by
  simp only [dP, toPoly_smul, Derivation.map_smul, ofPoly_smul]

/-- The map `L₂(u) = (1/t) ∑_ℓ y_ℓ W^{(t-1)}(∂u/∂y_ℓ)`. -/
noncomputable def L2lin {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) :
    Hom Y (t : ℤ) →ₗ[ℝ] Tup Y (fun i => (t : ℤ) - e i) where
  toFun u := WithLp.toLp 2 (fun i => (1 / (t : ℝ)) • ofPoly ((t : ℤ) - e i)
      (∑ ℓ : Y, X ℓ * toPoly ((Wl (mulMap p ((t : ℤ) - 1)) (dP (t : ℤ) ℓ u)) i)))
  map_add' u v := by
    ext i : 2
    simp only [dP_add, map_add, PiLp.add_apply, toPoly_add, mul_add, Finset.sum_add_distrib,
      ofPoly_add, smul_add]
  map_smul' c u := by
    ext i : 2
    simp only [dP_smul, map_smul, PiLp.smul_apply, toPoly_smul,
      RingHom.id_apply, mul_smul_comm, ← Finset.smul_sum, ofPoly_smul, smul_comm c]

lemma L2lin_apply {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) (u : Hom Y (t : ℤ))
    (i : Fin m) :
    L2lin p t u i = (1 / (t : ℝ)) • ofPoly ((t : ℤ) - e i)
      (∑ ℓ : Y, X ℓ * toPoly ((Wl (mulMap p ((t : ℤ) - 1)) (dP (t : ℤ) ℓ u)) i)) := rfl

noncomputable def L2 {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) :
    Hom Y (t : ℤ) →L[ℝ] Tup Y (fun i => (t : ℤ) - e i) :=
  LinearMap.toContinuousLinearMap (L2lin p t)

noncomputable def L1 {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) :
    Tup Y (fun i => (t : ℤ) - e i) →L[ℝ] Tup Y (fun i => (t : ℤ) - e i) :=
  ContinuousLinearMap.id ℝ _ - (L2 p t).comp (LinearMap.toContinuousLinearMap (mulMap p (t : ℤ)))

lemma L1_apply {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ)
    (v : Tup Y (fun i => (t : ℤ) - e i)) : L1 p t v = v - L2lin p t (mulMap p (t : ℤ) v) := rfl

lemma L2_apply {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) (u : Hom Y (t : ℤ)) :
    L2 p t u = L2lin p t u := rfl

lemma pinvNorm_congr {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (s s' : ℤ) (h : s = s') :
    pinvNorm (mulMap p s) = pinvNorm (mulMap p s') := by subst h; rfl

lemma tau_ge {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) (ht : 1 ≤ t) :
    pinvNorm (mulMap p ((t : ℤ) - 1)) ≤ tauOf p t := by
  unfold tauOf
  have h := le_ciSup (f := fun s : Fin t => pinvNorm (mulMap p (s : ℤ)))
    (Set.finite_range _).bddAbove ⟨t - 1, by omega⟩
  refine le_trans (le_of_eq ?_) h
  apply pinvNorm_congr
  simp only
  omega

lemma norm_mulMap_le {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (s : ℤ)
    (v : Tup Y (fun i => s - e i)) : ‖mulMap p s v‖ ≤ tupNorm p * ‖v‖ := by
  rw [mulMap_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => part3Z (e i) (s - e i) s (by ring) (p i) (v i)).trans ?_
  rw [tupNorm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

lemma norm_L2lin_le {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) (ht : 1 ≤ t)
    (u : Hom Y (t : ℤ)) : ‖L2lin p t u‖ ≤ pinvNorm (mulMap p ((t : ℤ) - 1)) * ‖u‖ := by
  set τ := pinvNorm (mulMap p ((t : ℤ) - 1))
  have hτ : 0 ≤ τ := pinvNorm_nonneg _
  set Wv : Y → Tup Y (fun i => ((t : ℤ) - 1) - e i) :=
    fun ℓ => Wl (mulMap p ((t : ℤ) - 1)) (dP (t : ℤ) ℓ u) with hWv
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : ‖L2lin p t u‖ ^ 2 ≤ (1 / (t : ℝ)) ^ 2 * ∑ ℓ, ‖Wv ℓ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2,
      Finset.sum_congr rfl (fun ℓ _ => PiLp.norm_sq_eq_of_L2 _ (Wv ℓ)),
      Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [L2lin_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    gcongr
    exact part2Z _ _ (by ring) (fun ℓ => Wv ℓ i)
  have h2 : ∑ ℓ, ‖Wv ℓ‖ ^ 2 ≤ τ ^ 2 * ∑ ℓ, ‖dP (t : ℤ) ℓ u‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (Wl_norm _ _) 2
  have h3 : ∑ ℓ, ‖dP (t : ℤ) ℓ u‖ ^ 2 = (t : ℝ) ^ 2 * ‖u‖ ^ 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    exact Dev.A1.part1_pos k u
  have h4 : ‖L2lin p t u‖ ^ 2 ≤ (τ * ‖u‖) ^ 2 := by
    calc ‖L2lin p t u‖ ^ 2 ≤ (1 / (t : ℝ)) ^ 2 * (τ ^ 2 * ((t : ℝ) ^ 2 * ‖u‖ ^ 2)) := by
          rw [← h3]; exact h1.trans (by gcongr)
      _ = (τ * ‖u‖) ^ 2 := by field_simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

lemma norm_L2_le {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) (ht : 1 ≤ t) :
    ‖L2 p t‖ ≤ tauOf p t := by
  have hτ := pinvNorm_nonneg (mulMap p ((t : ℤ) - 1))
  apply ContinuousLinearMap.opNorm_le_bound _ (hτ.trans (tau_ge p t ht))
  intro u
  rw [L2_apply]
  exact (norm_L2lin_le p t ht u).trans (by gcongr; exact tau_ge p t ht)

lemma tupNorm_nonneg {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) : 0 ≤ tupNorm p :=
  norm_nonneg _

lemma norm_L1_le {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom Y (e i)) (t : ℕ) (ht : 1 ≤ t) :
    ‖L1 p t‖ ≤ 1 + tauOf p t * tupNorm p := by
  have hτ' := pinvNorm_nonneg (mulMap p ((t : ℤ) - 1))
  have hτ := hτ'.trans (tau_ge p t ht)
  have hb := tupNorm_nonneg p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [L1_apply]
  calc ‖v - L2lin p t (mulMap p (t : ℤ) v)‖
      ≤ ‖v‖ + ‖L2lin p t (mulMap p (t : ℤ) v)‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + tauOf p t * (tupNorm p * ‖v‖) := by
        gcongr
        refine (norm_L2lin_le p t ht _).trans ?_
        exact mul_le_mul (tau_ge p t ht) (norm_mulMap_le p _ v) (norm_nonneg _) hτ
    _ = (1 + tauOf p t * tupNorm p) * ‖v‖ := by ring

end ApproxSyzygies.Smoothed.Dev.L42
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L42

open ApproxSyzygies.Smoothed

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

lemma modDeg_self {m : ℕ} (d D : Fin m → ℕ) (i : Fin m) : modDeg d D i i = d i := by
  simp [modDeg]

lemma modDeg_ne {m : ℕ} (d D : Fin m → ℕ) {i j : Fin m} (h : j ≠ i) :
    modDeg d D i j = (d j : ℤ) * (D j : ℤ) := by
  simp [modDeg, h]

/-- The correction term `H_{ℓ j i}` in the derivative of `∑ b_i u_i`. -/
noncomputable def Hc {m : ℕ} (D : Fin m → ℕ) (A : Fin m → MvPolynomial Y ℝ) (ℓ : Y) (j i : Fin m) :
    MvPolynomial Y ℝ :=
  if i = j then (D j : ℝ) • pderiv ℓ (A j) else pderiv ℓ (A j ^ D j)

/-- The generator `G_{ij}` of `J_i`: `a_i` for `j = i`, `b_j` otherwise. -/
noncomputable def Gc {m : ℕ} (D : Fin m → ℕ) (A : Fin m → MvPolynomial Y ℝ) (i j : Fin m) :
    MvPolynomial Y ℝ :=
  if j = i then A i else A j ^ D j

lemma pderiv_pow_mul (A : MvPolynomial Y ℝ) (D : ℕ) (hD : 1 ≤ D) (ℓ : Y) :
    pderiv ℓ (A ^ D) * A = A ^ D * ((D : ℝ) • pderiv ℓ A) := by
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  rw [Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul, map_natCast]
  ring

/-- The derivative identity (12) of the paper. -/
lemma deriv_identity {m : ℕ} (D : Fin m → ℕ) (hD : ∀ i, 1 ≤ D i) (A : Fin m → MvPolynomial Y ℝ)
    (U : Fin m → MvPolynomial Y ℝ) (Γ : Fin m → Fin m → MvPolynomial Y ℝ)
    (hU : ∀ i, U i = ∑ j, Γ i j * Gc D A i j) (ℓ : Y) :
    pderiv ℓ (∑ i, A i ^ D i * U i) =
      ∑ i, A i ^ D i * (pderiv ℓ (U i) + ∑ j, Γ j i * Hc D A ℓ j i) := by
  rw [map_sum]
  simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => A i ^ D i * (Γ j i * Hc D A ℓ j i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hU i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold Gc Hc
  by_cases h : j = i
  · subst h
    have := pderiv_pow_mul (A j) (D j) (hD j) ℓ
    simp only [↓reduceIte, smul_eq_C_mul] at this ⊢
    linear_combination Γ j j * this
  · simp only [if_neg h, if_neg (Ne.symm h)]
    ring

/-- The Euler-identity step of the paper. -/
lemma euler_identity {m : ℕ} (d D : Fin m → ℕ) (t : ℕ) (A : Fin m → MvPolynomial Y ℝ)
    (hA : ∀ j, HH (A j) (d j))
    (U : Fin m → MvPolynomial Y ℝ) (Γ : Fin m → Fin m → MvPolynomial Y ℝ)
    (hU : ∀ i, U i = ∑ j, Γ i j * Gc D A i j)
    (hUh : ∀ i, HH (U i) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))) (i : Fin m) :
    ∑ ℓ : Y, X ℓ * (pderiv ℓ (U i) + ∑ j, Γ j i * Hc D A ℓ j i) =
      (t : ℝ) • U i + ∑ j, (if j = i then 0 else
        (((d j : ℝ) * (D j : ℝ)) • Γ j i - ((d i : ℝ) * (D i : ℝ)) • Γ i j)) * A j ^ D j := by
  have hE : ∀ j, ∑ ℓ : Y, X ℓ * Hc D A ℓ j i =
      if i = j then ((D j : ℝ) * (d j : ℝ)) • A j else ((d j : ℝ) * (D j : ℝ)) • A j ^ D j := by
    intro j
    unfold Hc
    by_cases h : i = j
    · simp only [if_pos h, mul_smul_comm, ← Finset.smul_sum, euler (hA j), smul_smul]
      simp
    · simp only [if_neg h]
      rw [euler ((hA j).pow (D j) rfl)]
      push_cast; rfl
  simp only [mul_add, Finset.sum_add_distrib, euler (hUh i), Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (X _) (Γ _ i), ← Finset.mul_sum, hE]
  conv_lhs => rw [hU i]
  conv_rhs => rw [hU i]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold Gc
  by_cases h : j = i
  · subst h
    simp only [↓reduceIte, smul_eq_C_mul, zero_mul, mul_zero, add_zero]
    simp only [map_sub, map_mul, map_natCast, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring
  · simp only [if_neg h, if_neg (Ne.symm h), smul_eq_C_mul]
    simp only [map_sub, map_mul, map_natCast, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring

/-- The heart of Lemma 4.2: for `u` with `u_i ∈ J_i`, `u - L₂(M u)` is a Koszul syzygy. -/
lemma key {m : ℕ} (d D : Fin m → ℕ) (hD : ∀ i, 1 ≤ D i) (t : ℕ) (ht : 1 ≤ t)
    (A : Fin m → MvPolynomial Y ℝ) (hA : ∀ j, HH (A j) (d j))
    (p : ∀ i, Hom Y ((d i : ℤ) * (D i : ℤ))) (hp : ∀ j, toPoly (p j) = A j ^ D j)
    (hker : (LinearMap.ker (mulMap p ((t : ℤ) - 1)) :
        Set (Tup Y (fun i => (t : ℤ) - 1 - (d i : ℤ) * (D i : ℤ)))) = koszul p ((t : ℤ) - 1))
    (u : Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)))
    (Γ : Fin m → Fin m → MvPolynomial Y ℝ)
    (hΓ : ∀ i j, HH (Γ i j) ((t : ℤ) - (d i : ℤ) * (D i : ℤ) - modDeg d D i j))
    (hu : ∀ i, toPoly (u i) = ∑ j, Γ i j * Gc D A i j) :
    u - L2lin p t (mulMap p (t : ℤ) u) ∈ koszul p (t : ℤ) := by
  have htne : (t : ℝ) ≠ 0 := by have : (0 : ℝ) < t := by exact_mod_cast ht
                                exact this.ne'
  -- the polynomials `P ℓ i`
  set P : Y → Fin m → MvPolynomial Y ℝ :=
    fun ℓ i => pderiv ℓ (toPoly (u i)) + ∑ j, Γ j i * Hc D A ℓ j i with hPdef
  have hP : ∀ ℓ i, HH (P ℓ i) ((t : ℤ) - 1 - (d i : ℤ) * (D i : ℤ)) := by
    intro ℓ i
    refine HH.add ((HH_toPoly (u i)).pderiv ℓ (by ring)) (HH_sum _ _ _ fun j _ => ?_)
    unfold Hc
    by_cases h : i = j
    · subst h
      simp only [if_pos rfl]
      have h1 := hΓ i i
      rw [modDeg_self] at h1
      exact h1.mul (((hA i).pderiv ℓ rfl).smul _) (by ring)
    · simp only [if_neg h]
      have h1 := hΓ j i
      rw [modDeg_ne d D h] at h1
      exact h1.mul (((hA j).pow (D j) rfl).pderiv ℓ rfl) (by ring)
  set w : Y → Tup Y (fun i => ((t : ℤ) - 1) - (d i : ℤ) * (D i : ℤ)) :=
    fun ℓ => WithLp.toLp 2 (fun i => ofPoly _ (P ℓ i)) with hwdef
  have hw : ∀ ℓ i, toPoly (w ℓ i) = P ℓ i := fun ℓ i => toPoly_ofPoly (hP ℓ i)
  have hMw : ∀ ℓ, mulMap p ((t : ℤ) - 1) (w ℓ) = dP (t : ℤ) ℓ (mulMap p (t : ℤ) u) := by
    intro ℓ
    apply toPoly_injective
    rw [toPoly_mulMap, dP, toPoly_ofPoly ((HH_toPoly _).pderiv ℓ rfl), toPoly_mulMap]
    simp only [hw, hp]
    rw [deriv_identity D hD A (fun i => toPoly (u i)) Γ hu ℓ]
  -- the Koszul corrections `κ ℓ`
  have hκ : ∀ ℓ, Wl (mulMap p ((t : ℤ) - 1)) (dP (t : ℤ) ℓ (mulMap p (t : ℤ) u)) - w ℓ ∈
      koszul p ((t : ℤ) - 1) := by
    intro ℓ
    rw [← hMw ℓ, ← hker]
    exact Wl_spec _ _
  choose Ωl hΩl_hom hΩl_skew hΩl_eq using hκ
  have hWi : ∀ ℓ i, toPoly ((Wl (mulMap p ((t : ℤ) - 1)) (dP (t : ℤ) ℓ (mulMap p (t : ℤ) u))) i) =
      P ℓ i + ∑ j, Ωl ℓ i j * A j ^ D j := by
    intro ℓ i
    have := hΩl_eq ℓ i
    simp only [hp] at this
    rw [← this, PiLp.sub_apply, toPoly_sub, hw]
    ring
  -- the skew matrix from Euler's identity
  set Ω0 : Fin m → Fin m → MvPolynomial Y ℝ := fun i j => if j = i then 0 else
    (((d j : ℝ) * (D j : ℝ)) • Γ j i - ((d i : ℝ) * (D i : ℝ)) • Γ i j) with hΩ0
  have hUh : ∀ i, HH (toPoly (u i)) ((t : ℤ) - (d i : ℤ) * (D i : ℤ)) := fun i => HH_toPoly _
  have hEul := euler_identity d D t A hA (fun i => toPoly (u i)) Γ hu hUh
  refine ⟨fun i j => (-(1 / (t : ℝ))) • (Ω0 i j + ∑ ℓ, X ℓ * Ωl ℓ i j), ?_, ?_, ?_⟩
  · intro i j
    rw [mem_homSpace]
    apply HH.smul
    refine HH.add ?_ (HH_sum _ _ _ fun ℓ _ => ?_)
    · simp only [hΩ0]
      split_ifs with h
      · exact HH_zero _
      · have h1 := hΓ j i
        rw [modDeg_ne d D (Ne.symm h)] at h1
        have h2 := hΓ i j
        rw [modDeg_ne d D h] at h2
        exact HH.sub ((h1.smul _).congr (by ring)) (h2.smul _)
    · have := (mem_homSpace _).1 (hΩl_hom ℓ i j)
      exact (HH_X ℓ).mul this (by ring)
  · intro i j
    have h0 : Ω0 i j = -Ω0 j i := by
      simp only [hΩ0]
      by_cases h : j = i
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]
        abel
    simp only
    rw [h0]
    simp_rw [hΩl_skew _ i j]
    simp only [mul_neg, Finset.sum_neg_distrib, ← neg_add, smul_neg]
  · intro i
    rw [PiLp.sub_apply, toPoly_sub, L2lin_apply, toPoly_smul,
      toPoly_ofPoly (HH_sum _ _ _ fun ℓ _ => (HH_X ℓ).mul (HH_toPoly _) (by ring))]
    simp only [hWi, hp]
    have e1 : ∑ ℓ : Y, X ℓ * (P ℓ i + ∑ j, Ωl ℓ i j * A j ^ D j) =
        ∑ ℓ : Y, X ℓ * P ℓ i + ∑ j, (∑ ℓ : Y, X ℓ * Ωl ℓ i j) * A j ^ D j := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (f := fun ℓ j => X ℓ * (Ωl ℓ i j * A j ^ D j))]
      simp only [mul_assoc]
    have e2 : ∑ j, (-(1 / (t : ℝ))) • (Ω0 i j + ∑ ℓ : Y, X ℓ * Ωl ℓ i j) * A j ^ D j =
        (-(1 / (t : ℝ))) • (∑ j, Ω0 i j * A j ^ D j +
          ∑ j, (∑ ℓ : Y, X ℓ * Ωl ℓ i j) * A j ^ D j) := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_mul_assoc, add_mul]
    have e3 : ∑ ℓ : Y, X ℓ * P ℓ i = (t : ℝ) • toPoly (u i) + ∑ j, Ω0 i j * A j ^ D j :=
      hEul i
    rw [e1, e2, e3, smul_add, smul_add, smul_smul, one_div, inv_mul_cancel₀ htne, one_smul,
      neg_smul, smul_add]
    abel

end ApproxSyzygies.Smoothed.Dev.L42
end

section
set_option autoImplicit false

namespace ApproxSyzygies.Smoothed.Dev.L42

open ApproxSyzygies.Smoothed

/-- `u_i = Π_{J_i} h_i[0]` lies in `J_i`, so it is `∑_j Γ_{ij} G_{ij}`. -/
lemma jpiece_decomp {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ) (t : ℕ)
    (a₀ : ∀ j, Hom Y (d j : ℤ)) (h₀ : Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)))
    (i : Fin m) :
    ∃ Γ : Fin m → MvPolynomial Y ℝ,
      (∀ j, HH (Γ j) ((t : ℤ) - (d i : ℤ) * (D i : ℤ) - modDeg d D i j)) ∧
      toPoly ((h₀ - gVec d D t a₀ h₀) i) = ∑ j, Γ j * Gc D (fun j => toPoly (a₀ j)) i j := by
  have hmem : (h₀ - gVec d D t a₀ h₀) i ∈ Jpiece d D t a₀ i := by
    simp only [PiLp.sub_apply, gVec, Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    exact Submodule.starProjection_apply_mem _ _
  obtain ⟨Γ', hΓ'⟩ := hmem
  refine ⟨fun j => toPoly (Γ' j), fun j => HH_toPoly _, ?_⟩
  rw [← hΓ', toPoly_mulMap]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1
  simp only [modGen, Gc]
  apply toPoly_ofPoly
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, modDeg_self]
    exact HH_toPoly _
  · rw [if_neg h, modDeg_ne d D h]
    exact (HH_toPoly _).pow _ rfl

end ApproxSyzygies.Smoothed.Dev.L42

namespace ApproxSyzygies.Smoothed

open ApproxSyzygies.Smoothed.Dev.L42 in
theorem chk_lemma_4_2 {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hD : ∀ i, 1 ≤ D i) (t : ℕ) (ht : 1 ≤ t) :
    ∃ L₁ : (∀ i, Hom Y ((d i : ℤ) * (D i : ℤ))) →
        (Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)) →L[ℝ]
          Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ))),
    ∃ L₂ : (∀ i, Hom Y ((d i : ℤ) * (D i : ℤ))) →
        (Hom Y (t : ℤ) →L[ℝ] Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ))),
    ∀ (Z : Type) [Fintype Z] [DecidableEq Z] (a : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)),
      (LinearMap.ker (mulMap (yParts fun i => powHom (a i) (D i)) ((t : ℤ) - 1)) :
          Set (Tup Y (fun i => (t : ℤ) - 1 - (d i : ℤ) * (D i : ℤ)))) =
        koszul (yParts fun i => powHom (a i) (D i)) ((t : ℤ) - 1) →
      ‖L₁ (yParts fun i => powHom (a i) (D i))‖ ≤
          1 + tauOf (yParts fun i => powHom (a i) (D i)) t *
            tupNorm (yParts fun i => powHom (a i) (D i)) ∧
        ‖L₂ (yParts fun i => powHom (a i) (D i))‖ ≤
          tauOf (yParts fun i => powHom (a i) (D i)) t ∧
        ∀ h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)),
          ∃ k₀ ∈ koszul (yParts fun i => powHom (a i) (D i)) (t : ℤ),
            yPartTup h = k₀ +
              L₁ (yParts fun i => powHom (a i) (D i)) (gVec d D t (yParts a) (yPartTup h)) +
              L₂ (yParts fun i => powHom (a i) (D i))
                (yPart (mulMap (fun i => powHom (a i) (D i)) (t : ℤ) h)) := by
  refine ⟨fun p => L1 p t, fun p => L2 p t, ?_⟩
  intro Z _ _ a hker
  refine ⟨norm_L1_le _ t ht, norm_L2_le _ t ht, ?_⟩
  intro h
  rw [yPart_mulMap]
  set b0 := yParts fun i => powHom (a i) (D i) with hb0
  set h0 := yPartTup h with hh0
  set g := gVec d D t (yParts a) h0 with hg
  refine ⟨h0 - L1 b0 t g - L2 b0 t (mulMap b0 (t : ℤ) h0), ?_, by abel⟩
  have e : h0 - L1 b0 t g - L2 b0 t (mulMap b0 (t : ℤ) h0) =
      (h0 - g) - L2lin b0 t (mulMap b0 (t : ℤ) (h0 - g)) := by
    rw [L1_apply, L2_apply, map_sub, map_sub]
    abel
  rw [e]
  choose Γ hΓ hu using jpiece_decomp d D t (yParts a) h0
  exact key d D hD t ht (fun j => toPoly (yParts a j)) (fun j => HH_toPoly _) b0
    (fun j => toPoly_yParts_pow (a j) (D j)) hker (h0 - g) Γ hΓ hu

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_lemma_4_2 := @ApproxSyzygies.Smoothed.chk_lemma_4_2
