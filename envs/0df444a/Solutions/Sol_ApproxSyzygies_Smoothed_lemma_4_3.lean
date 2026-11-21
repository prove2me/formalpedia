-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:58:48.361915+00:00
-- url     : https://prove2.me/submissions/4e548b95-81a7-4b4f-bfa7-cc2efd8b2844

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
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L43

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

/-! ### Generic facts about `toPoly`, `ofPoly` and homogeneity -/

section Generic

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Total degree of a multi-index. -/
def deg (γ : σ →₀ ℕ) : ℕ := ∑ i, γ i

lemma mem_monos_iff (d : ℤ) (γ : σ →₀ ℕ) : γ ∈ monos σ d ↔ ((deg γ : ℕ) : ℤ) = d := by
  unfold monos deg
  split_ifs with h
  · rw [Finset.mem_finsuppAntidiag]
    simp only [Finset.subset_univ, and_true]
    show (∑ i, γ i) = d.toNat ↔ ((∑ i, γ i : ℕ) : ℤ) = d
    omega
  · simp only [Finset.notMem_empty, false_iff]
    omega

/-- Homogeneity of integer degree `d` (forces `f = 0` when `d < 0`). -/
def IsH (d : ℤ) (f : MvPolynomial σ ℝ) : Prop :=
  ∀ γ, coeff γ f ≠ 0 → ((deg γ : ℕ) : ℤ) = d

lemma coeff_toPoly' (d : ℤ) (p : Hom σ d) (α : σ →₀ ℕ) :
    coeff α (toPoly p) =
      if h : α ∈ monos σ d then p ⟨α, h⟩ * Real.sqrt ((d.toNat.factorial : ℝ) / mfact α) else 0 := by
  unfold toPoly
  rw [coeff_sum]
  simp only [coeff_smul, bmono, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨α, h⟩]
    · have h1 := (mem_monos_iff d α).1 h
      have : Finsupp.degree α = d.toNat := by
        rw [Finsupp.degree_eq_sum]; unfold deg at h1; omega
      simp [this]
    · intro b _ hb
      have : (b : σ →₀ ℕ) ≠ α := fun e => hb (Subtype.ext e)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : (b : σ →₀ ℕ) ≠ α := fun e => h (e ▸ b.2)
    simp [this]

lemma IsH_toPoly {d : ℤ} (p : Hom σ d) : IsH d (toPoly p) := by
  intro γ h
  rw [coeff_toPoly'] at h
  split_ifs at h with hm
  · exact (mem_monos_iff d γ).1 hm
  · exact absurd rfl h

lemma toPoly_ofPoly (d : ℤ) (f : MvPolynomial σ ℝ) (hf : IsH d f) : toPoly (ofPoly d f) = f := by
  ext γ
  rw [coeff_toPoly']
  split_ifs with hm
  · simp only [ofPoly]
    have h1 := mfact_pos γ
    have h2 : (0:ℝ) < (d.toNat.factorial : ℝ) := by positivity
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    rw [show mfact γ / (d.toNat.factorial : ℝ) * ((d.toNat.factorial : ℝ) / mfact γ) = 1 by
      field_simp]
    simp
  · by_contra hne
    exact hm ((mem_monos_iff d γ).2 (hf γ (Ne.symm hne)))

lemma ofPoly_toPoly {d : ℤ} (p : Hom σ d) : ofPoly d (toPoly p) = p := by
  ext ⟨γ, hγ⟩
  simp only [ofPoly]
  rw [coeff_toPoly', dif_pos hγ]
  have h1 := mfact_pos γ
  have h2 : (0:ℝ) < (d.toNat.factorial : ℝ) := by positivity
  rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
  rw [show (d.toNat.factorial : ℝ) / mfact γ * (mfact γ / (d.toNat.factorial : ℝ)) = 1 by
    field_simp]
  simp

lemma toPoly_inj {d : ℤ} {p q : Hom σ d} (h : toPoly p = toPoly q) : p = q := by
  rw [← ofPoly_toPoly p, h, ofPoly_toPoly]

lemma toPoly_add {d : ℤ} (p q : Hom σ d) : toPoly (p + q) = toPoly p + toPoly q :=
  (toPolyL (σ := σ) d).map_add p q

lemma toPoly_sub {d : ℤ} (p q : Hom σ d) : toPoly (p - q) = toPoly p - toPoly q :=
  (toPolyL (σ := σ) d).map_sub p q

lemma toPoly_zero {d : ℤ} : toPoly (0 : Hom σ d) = 0 :=
  (toPolyL (σ := σ) d).map_zero

lemma toPoly_smul {d : ℤ} (c : ℝ) (p : Hom σ d) : toPoly (c • p) = c • toPoly p :=
  (toPolyL (σ := σ) d).map_smul c p

lemma toPoly_sum {d : ℤ} {ι : Type} (s : Finset ι) (p : ι → Hom σ d) :
    toPoly (∑ i ∈ s, p i) = ∑ i ∈ s, toPoly (p i) :=
  map_sum (toPolyL (σ := σ) d) p s

lemma IsH.add {d : ℤ} {f g : MvPolynomial σ ℝ} (hf : IsH d f) (hg : IsH d g) : IsH d (f + g) := by
  intro γ h
  rw [coeff_add] at h
  by_cases h1 : coeff γ f = 0
  · rw [h1, zero_add] at h; exact hg γ h
  · exact hf γ h1

lemma IsH.neg {d : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) : IsH d (-f) := by
  intro γ h
  rw [coeff_neg, neg_ne_zero] at h; exact hf γ h

lemma IsH_zero (d : ℤ) : IsH d (0 : MvPolynomial σ ℝ) := by
  intro γ h; simp at h

lemma IsH_sum {d : ℤ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i ∈ s, IsH d (f i)) : IsH d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsH_zero d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma deg_add (a b : σ →₀ ℕ) : deg (a + b) = deg a + deg b := by
  unfold deg; simp [Finset.sum_add_distrib]

lemma IsH.mul {d d' : ℤ} {f g : MvPolynomial σ ℝ} (hf : IsH d f) (hg : IsH d' g) :
    IsH (d + d') (f * g) := by
  intro γ h
  rw [coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 := hf x.1 (left_ne_zero_of_mul hne)
  have h2 := hg x.2 (right_ne_zero_of_mul hne)
  rw [← hx, deg_add]; push_cast; omega

lemma IsH.of_eq {d d' : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) (h : d = d') : IsH d' f := h ▸ hf

lemma mem_homSpace_iff (d : ℤ) (f : MvPolynomial σ ℝ) : f ∈ homSpace σ d ↔ IsH d f := by
  constructor
  · rintro ⟨x, rfl⟩; exact IsH_toPoly x
  · intro h; exact ⟨ofPoly d f, toPoly_ofPoly d f h⟩

lemma toPoly_mulMap {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (t : ℤ)
    (u : Tup σ (fun i => t - e i)) :
    toPoly (mulMap p t u) = ∑ i, toPoly (p i) * toPoly (u i) := by
  have : mulMap p t u = ∑ i, ofPoly t (toPoly (p i) * toPoly (u i)) := by
    simp [mulMap, LinearMap.sum_apply, ofPolyL, toPolyL]
    rfl
  rw [this, toPoly_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  apply toPoly_ofPoly
  exact ((IsH_toPoly (p i)).mul (IsH_toPoly (u i))).of_eq (by ring)

lemma hom_eq_zero_of_neg {d : ℤ} (hd : d < 0) (x : Hom σ d) : x = 0 := by
  ext ⟨γ, hγ⟩
  rw [monos_neg d hd] at hγ
  simp at hγ

lemma koszul_add {m : ℕ} {e : Fin m → ℤ} {p : ∀ i, Hom σ (e i)} {t : ℤ}
    {h h' : Tup σ (fun i => t - e i)} (hh : h ∈ koszul p t) (hh' : h' ∈ koszul p t) :
    h + h' ∈ koszul p t := by
  obtain ⟨Ω, h1, h2, h3⟩ := hh
  obtain ⟨Ω', h1', h2', h3'⟩ := hh'
  refine ⟨fun i j => Ω i j + Ω' i j, fun i j => add_mem (h1 i j) (h1' i j), fun i j => ?_, fun i => ?_⟩
  · show Ω i j + Ω' i j = -(Ω j i + Ω' j i)
    rw [h2 i j, h2' i j, neg_add]
  · rw [PiLp.add_apply, toPoly_add, h3 i, h3' i, ← Finset.sum_add_distrib]
    simp [add_mul]

lemma mulMap_koszul {m : ℕ} {e : Fin m → ℤ} {p : ∀ i, Hom σ (e i)} {t : ℤ}
    {h : Tup σ (fun i => t - e i)} (hh : h ∈ koszul p t) : mulMap p t h = 0 := by
  obtain ⟨Ω, _, h2, h3⟩ := hh
  apply toPoly_inj
  rw [toPoly_mulMap, toPoly_zero]
  simp_rw [h3, Finset.mul_sum]
  set S := ∑ i, ∑ j, toPoly (p i) * (Ω i j * toPoly (p j)) with hS
  have : S = -S := by
    conv_lhs => rw [hS, Finset.sum_comm]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2 i j]; ring
  have h2S : (2 : ℝ) • S = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel S
  exact (smul_eq_zero.1 h2S).resolve_left two_ne_zero

end Generic

/-! ### Splitting variables `x = (y, z)` -/

section Split

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The `y`-part of a multi-index. -/
noncomputable def yp (γ : (Y ⊕ Z) →₀ ℕ) : Y →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp γ).1
/-- The `z`-part of a multi-index. -/
noncomputable def zp (γ : (Y ⊕ Z) →₀ ℕ) : Z →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp γ).2
/-- Joining a `y`- and a `z`-multi-index. -/
noncomputable def join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : (Y ⊕ Z) →₀ ℕ :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm (β, α)

@[simp] lemma yp_apply (γ : (Y ⊕ Z) →₀ ℕ) (y : Y) : yp γ y = γ (Sum.inl y) := by
  simp [yp, Finsupp.fst_sumFinsuppEquivProdFinsupp]

@[simp] lemma zp_apply (γ : (Y ⊕ Z) →₀ ℕ) (z : Z) : zp γ z = γ (Sum.inr z) := by
  simp [zp, Finsupp.snd_sumFinsuppEquivProdFinsupp]

@[simp] lemma yp_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : yp (join β α) = β := by
  simp [yp, join]

@[simp] lemma zp_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : zp (join β α) = α := by
  simp [zp, join]

@[simp] lemma join_yp_zp (γ : (Y ⊕ Z) →₀ ℕ) : join (yp γ) (zp γ) = γ := by
  simp [yp, zp, join]

lemma eq_iff_yp_zp (γ γ' : (Y ⊕ Z) →₀ ℕ) : γ = γ' ↔ yp γ = yp γ' ∧ zp γ = zp γ' := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← join_yp_zp γ, ← join_yp_zp γ', h1, h2]

lemma deg_split (γ : (Y ⊕ Z) →₀ ℕ) : deg γ = deg (yp γ) + deg (zp γ) := by
  unfold deg; rw [Fintype.sum_sum_type]; simp

lemma deg_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : deg (join β α) = deg β + deg α := by
  rw [deg_split]; simp

lemma zdeg_eq (γ : (Y ⊕ Z) →₀ ℕ) : zdeg γ = deg (zp γ) := by
  simp [zdeg, deg]

lemma mfact_split (γ : (Y ⊕ Z) →₀ ℕ) : mfact γ = mfact (yp γ) * mfact (zp γ) := by
  unfold mfact; rw [Fintype.prod_sum_type]; simp

lemma mfact_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : mfact (join β α) = mfact β * mfact α := by
  rw [mfact_split]; simp

/-- Reading a polynomial in `x = (y, z)` as a polynomial in `z` with coefficients in `ℝ[y]`. -/
noncomputable def Phi : MvPolynomial (Y ⊕ Z) ℝ →ₐ[ℝ] MvPolynomial Z (MvPolynomial Y ℝ) :=
  aeval (Sum.elim (fun y => C (X y)) (fun z => X z))

lemma Phi_monomial (γ : (Y ⊕ Z) →₀ ℕ) (c : ℝ) :
    Phi (monomial γ c) = monomial (zp γ) (monomial (yp γ) c) := by
  rw [Phi, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  rw [monomial_eq, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Sum.elim_inl, Sum.elim_inr, yp_apply, zp_apply, map_mul, map_prod, map_pow]
  simp only [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  ring

/-- The coefficient of `z^α` of a polynomial in `(y, z)`, as a polynomial in `y`. -/
noncomputable def E (α : Z →₀ ℕ) (f : MvPolynomial (Y ⊕ Z) ℝ) : MvPolynomial Y ℝ :=
  coeff α (Phi f)

lemma coeff_E (f : MvPolynomial (Y ⊕ Z) ℝ) (γ : (Y ⊕ Z) →₀ ℕ) :
    coeff γ f = coeff (yp γ) (E (zp γ) f) := by
  unfold E
  induction f using MvPolynomial.induction_on' with
  | monomial γ' c =>
    rw [Phi_monomial, coeff_monomial, coeff_monomial]
    by_cases h : γ' = γ
    · subst h; simp
    · rw [if_neg h]
      rw [eq_iff_yp_zp] at h
      by_cases hz : zp γ' = zp γ
      · rw [if_pos hz, coeff_monomial, if_neg (fun h' => h ⟨h', hz⟩)]
      · rw [if_neg hz]; simp
  | add p q hp hq => simp [hp, hq]

lemma coeff_E_join (f : MvPolynomial (Y ⊕ Z) ℝ) (β : Y →₀ ℕ) (α : Z →₀ ℕ) :
    coeff β (E α f) = coeff (join β α) f := by
  rw [coeff_E]; simp

lemma E_add (α : Z →₀ ℕ) (f g : MvPolynomial (Y ⊕ Z) ℝ) : E α (f + g) = E α f + E α g := by
  simp [E]

lemma E_sub (α : Z →₀ ℕ) (f g : MvPolynomial (Y ⊕ Z) ℝ) : E α (f - g) = E α f - E α g := by
  simp [E]

lemma E_neg (α : Z →₀ ℕ) (f : MvPolynomial (Y ⊕ Z) ℝ) : E α (-f) = -E α f := by
  simp [E]

lemma E_smul (α : Z →₀ ℕ) (c : ℝ) (f : MvPolynomial (Y ⊕ Z) ℝ) : E α (c • f) = c • E α f := by
  simp [E]

lemma E_zero (α : Z →₀ ℕ) : E α (0 : MvPolynomial (Y ⊕ Z) ℝ) = 0 := by
  simp [E]

lemma E_sum {ι : Type} (α : Z →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial (Y ⊕ Z) ℝ) :
    E α (∑ i ∈ s, f i) = ∑ i ∈ s, E α (f i) := by
  simp [E, map_sum, coeff_sum]

lemma ext_E {f g : MvPolynomial (Y ⊕ Z) ℝ} (h : ∀ α, E α f = E α g) : f = g := by
  ext γ; rw [coeff_E, coeff_E, h]

lemma hom_ext_E {d : ℤ} {x x' : Hom (Y ⊕ Z) d}
    (h : ∀ α, E α (toPoly x) = E α (toPoly x')) : x = x' :=
  toPoly_inj (ext_E h)

lemma Phi_rename_inl (g : MvPolynomial Y ℝ) : Phi (rename Sum.inl g : MvPolynomial (Y ⊕ Z) ℝ) = C g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [Phi, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p y hp => rw [map_mul, rename_X, map_mul, hp]; simp [Phi]

lemma E_rename_inl_mul (α : Z →₀ ℕ) (g : MvPolynomial Y ℝ) (f : MvPolynomial (Y ⊕ Z) ℝ) :
    E α (rename Sum.inl g * f) = g * E α f := by
  simp [E, Phi_rename_inl, coeff_C_mul]

lemma E_rename_inl (α : Z →₀ ℕ) (g : MvPolynomial Y ℝ) :
    E α (rename Sum.inl g : MvPolynomial (Y ⊕ Z) ℝ) = if α = 0 then g else 0 := by
  simp [E, Phi_rename_inl, coeff_C, eq_comm]

/-- The monomial `z^α` in `ℝ[y, z]`. -/
noncomputable def zmon (α : Z →₀ ℕ) : MvPolynomial (Y ⊕ Z) ℝ := monomial (join (0 : Y →₀ ℕ) α) 1

lemma Phi_zmon (α : Z →₀ ℕ) : Phi (zmon (Y := Y) α) = monomial α 1 := by
  simp [zmon, Phi_monomial]

lemma E_zmon_mul (α α' : Z →₀ ℕ) (f : MvPolynomial (Y ⊕ Z) ℝ) :
    E α' (zmon α * f) = if α ≤ α' then E (α' - α) f else 0 := by
  simp only [E, map_mul, Phi_zmon]
  rw [coeff_monomial_mul']
  split_ifs <;> simp

lemma E_zmon_mul_rename (α α' : Z →₀ ℕ) (g : MvPolynomial Y ℝ) :
    E α' (zmon α * rename Sum.inl g) = if α = α' then g else 0 := by
  rw [E_zmon_mul]
  split_ifs with h1 h2 h2
  · rw [E_rename_inl, if_pos (by rw [h2, tsub_self])]
  · rw [E_rename_inl, if_neg]
    intro h; apply h2
    exact le_antisymm h1 (tsub_eq_zero_iff_le.1 h)
  · exact absurd (h2 ▸ le_refl α) h1
  · rfl

lemma IsH_E {d : ℤ} {f : MvPolynomial (Y ⊕ Z) ℝ} (hf : IsH d f) (α : Z →₀ ℕ) :
    IsH (d - deg α) (E α f) := by
  intro β h
  rw [coeff_E_join] at h
  have := hf _ h
  rw [deg_join] at this; push_cast at this; omega

lemma IsH_rename_inl {d : ℤ} {g : MvPolynomial Y ℝ} (hg : IsH d g) :
    IsH d (rename Sum.inl g : MvPolynomial (Y ⊕ Z) ℝ) := by
  intro γ h
  rw [coeff_E, E_rename_inl] at h
  split_ifs at h with hz
  · have := hg _ h
    rw [deg_split, hz]; simpa [deg] using this
  · exact absurd (coeff_zero _) h

lemma IsH_zmon (α : Z →₀ ℕ) : IsH (deg α : ℤ) (zmon (Y := Y) α) := by
  intro γ h
  rw [zmon, coeff_monomial] at h
  split_ifs at h with h1
  · subst h1; rw [deg_join]; simp [deg]
  · exact absurd rfl h

/-! ### `grade`, `yPart`, `liftY` in terms of `E` -/

lemma E_grade (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) (α : Z →₀ ℕ) :
    E α (toPoly (grade r f)) = if deg α = r then E α (toPoly f) else 0 := by
  ext β
  rw [coeff_E_join]
  split_ifs with h
  · rw [coeff_E_join, coeff_toPoly', coeff_toPoly']
    split_ifs with hm
    · simp [grade, zdeg_eq, h]
    · rfl
  · rw [coeff_toPoly']
    split_ifs with hm
    · simp [grade, zdeg_eq, h]
    · simp

lemma aeval_elim_eq_E (g : MvPolynomial (Y ⊕ Z) ℝ) :
    aeval (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ))) g = E 0 g := by
  rw [show E 0 g = constantCoeff (Phi g) from rfl]
  induction g using MvPolynomial.induction_on with
  | C a => simp [Phi, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    rcases v with y | z <;> simp [Phi]

lemma toPoly_yPart {d : ℤ} (f : Hom (Y ⊕ Z) d) : toPoly (yPart f) = E 0 (toPoly f) := by
  rw [yPart, aeval_elim_eq_E, toPoly_ofPoly]
  simpa [deg] using IsH_E (IsH_toPoly f) 0

lemma toPoly_liftY {d : ℤ} (u : Hom Y d) :
    toPoly (liftY (Z := Z) u) = rename Sum.inl (toPoly u) := by
  rw [liftY, toPoly_ofPoly]
  exact IsH_rename_inl (IsH_toPoly u)

lemma E_liftY {d : ℤ} (u : Hom Y d) (α : Z →₀ ℕ) :
    E α (toPoly (liftY (Z := Z) u)) = if α = 0 then toPoly u else 0 := by
  rw [toPoly_liftY, E_rename_inl]

lemma deg_eq_zero_iff (α : Z →₀ ℕ) : deg α = 0 ↔ α = 0 := by
  unfold deg
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; ext z; simpa using h z (Finset.mem_univ z)
  · rintro rfl; simp

lemma grade_zero_eq {d : ℤ} (f : Hom (Y ⊕ Z) d) : grade 0 f = liftY (yPart f) := by
  apply hom_ext_E
  intro α
  rw [E_grade, E_liftY, toPoly_yPart]
  by_cases h : α = 0
  · subst h; simp [deg]
  · rw [if_neg ((deg_eq_zero_iff α).not.2 h), if_neg h]

lemma yPart_liftY {d : ℤ} (u : Hom Y d) : yPart (liftY (Z := Z) u) = u := by
  apply toPoly_inj
  rw [toPoly_yPart, E_liftY, if_pos rfl]

lemma yPart_eq_of_grade_zero {d : ℤ} {f f' : Hom (Y ⊕ Z) d} (h : grade 0 f = grade 0 f') :
    yPart f = yPart f' := by
  rw [grade_zero_eq, grade_zero_eq] at h
  rw [← yPart_liftY (Z := Z) (yPart f), h, yPart_liftY]

lemma mem_monos_Z (R : ℕ) (α : Z →₀ ℕ) : α ∈ monos Z (R : ℤ) ↔ deg α = R := by
  rw [mem_monos_iff]; omega

/-- The `z`-degree-`R` part of `v` as `∑_{|α| = R} z^α · E_α v`. -/
lemma toPoly_grade_decomp (R : ℕ) {d : ℤ} (v : Hom (Y ⊕ Z) d) :
    toPoly (grade R v) =
      ∑ α ∈ monos Z (R : ℤ), zmon α * rename Sum.inl (E α (toPoly v)) := by
  apply ext_E
  intro α'
  rw [E_grade, E_sum]
  simp_rw [E_zmon_mul_rename]
  rw [Finset.sum_ite_eq']
  simp only [mem_monos_Z]

lemma sum_monos_split (d : ℤ) (R : ℕ) (φ : ((Y ⊕ Z) →₀ ℕ) → ℝ)
    (hφ : ∀ γ, deg (zp γ) ≠ R → φ γ = 0) :
    ∑ γ ∈ monos (Y ⊕ Z) d, φ γ =
      ∑ α ∈ monos Z (R : ℤ), ∑ β ∈ monos Y (d - R), φ (join β α) := by
  rw [← Finset.sum_filter_of_ne (p := fun γ => deg (zp γ) = R)
    (fun γ _ h => by_contra fun h' => h (hφ γ h'))]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun γ => (zp γ, yp γ)) (fun x => join x.2 x.1) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    simp only [Finset.mem_coe, Finset.mem_filter, mem_monos_iff] at hγ
    simp only [Finset.mem_coe, Finset.mem_product, mem_monos_iff]
    rw [deg_split] at hγ; push_cast at hγ ⊢; omega
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, mem_monos_iff] at hx
    simp only [Finset.mem_coe, Finset.mem_filter, mem_monos_iff, deg_join, zp_join]
    push_cast; omega
  · intro γ _; simp
  · intro x _; simp
  · intro γ _; simp

lemma coeff_zsum (R : ℕ) (G : (Z →₀ ℕ) → MvPolynomial Y ℝ) (γ : (Y ⊕ Z) →₀ ℕ) :
    coeff γ (∑ α ∈ monos Z (R : ℤ), zmon α * rename Sum.inl (G α)) =
      if zp γ ∈ monos Z (R : ℤ) then coeff (yp γ) (G (zp γ)) else 0 := by
  rw [coeff_E, E_sum]
  simp_rw [E_zmon_mul_rename]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp

lemma norm_sq_zsum (d : ℤ) (R : ℕ) (G : (Z →₀ ℕ) → MvPolynomial Y ℝ) :
    ‖ofPoly d (∑ α ∈ monos Z (R : ℤ), zmon α * rename Sum.inl (G α))‖ ^ 2 =
      ∑ α ∈ monos Z (R : ℤ), (mfact α * ((d - R).toNat.factorial : ℝ) / (d.toNat.factorial : ℝ)) *
        ‖ofPoly (d - R) (G α)‖ ^ 2 := by
  rw [normsq_ofPoly, sum_monos_split d R]
  · apply Finset.sum_congr rfl
    intro α hα
    rw [normsq_ofPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [coeff_zsum, yp_join, zp_join, if_pos hα, mfact_join]
    have h1 : ((d - R).toNat.factorial : ℝ) ≠ 0 := by positivity
    have h2 : (d.toNat.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro γ hγ
    rw [coeff_zsum, if_neg (by rwa [mem_monos_Z])]
    simp

lemma norm_sq_le_of_coord {d : ℤ} {σ : Type} [Fintype σ] [DecidableEq σ] (x x' : Hom σ d)
    (h : ∀ γ, |x γ| ≤ |x' γ|) : ‖x‖ ≤ ‖x'‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro γ _
  simp only [Real.norm_eq_abs, sq_abs]
  exact sq_le_sq.2 (h γ)

lemma norm_grade_le (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) : ‖grade r f‖ ≤ ‖f‖ := by
  apply norm_sq_le_of_coord
  intro γ
  simp only [grade]
  split_ifs <;> simp

lemma grade_add (r : ℕ) {d : ℤ} (f g : Hom (Y ⊕ Z) d) : grade r (f + g) = grade r f + grade r g := by
  ext γ; simp only [grade, PiLp.add_apply]; split_ifs <;> simp

lemma grade_sub (r : ℕ) {d : ℤ} (f g : Hom (Y ⊕ Z) d) : grade r (f - g) = grade r f - grade r g := by
  ext γ; simp only [grade, PiLp.sub_apply]; split_ifs <;> simp

lemma grade_zero' (r : ℕ) {d : ℤ} : grade r (0 : Hom (Y ⊕ Z) d) = 0 := by
  ext γ; simp only [grade]; split_ifs <;> simp

lemma grade_grade (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) : grade r (grade r f) = grade r f := by
  ext γ; simp only [grade]; split_ifs <;> simp

lemma zmon_zero : zmon (Y := Y) (0 : Z →₀ ℕ) = 1 := by
  rw [zmon, show join (0 : Y →₀ ℕ) (0 : Z →₀ ℕ) = 0 by
    rw [eq_iff_yp_zp]; constructor <;> ext <;> simp]
  rfl

lemma norm_liftY {d : ℤ} (u : Hom Y d) : ‖liftY (Z := Z) u‖ = ‖u‖ := by
  have h0 : monos Z ((0 : ℕ) : ℤ) = {0} := by simp [monos]
  have : rename Sum.inl (toPoly u) =
      ∑ α ∈ monos Z ((0 : ℕ) : ℤ), zmon α * rename (R := ℝ) (Sum.inl (β := Z)) (toPoly u) := by
    rw [h0, Finset.sum_singleton, zmon_zero, one_mul]
  have h := norm_sq_zsum (Y := Y) (Z := Z) d 0 (fun _ => toPoly u)
  rw [← this, h0, Finset.sum_singleton] at h
  simp only [Nat.cast_zero, sub_zero, ofPoly_toPoly] at h
  have hm : mfact (0 : Z →₀ ℕ) = 1 := by simp [mfact]
  rw [hm, one_mul, div_self (by positivity), one_mul] at h
  rw [liftY]
  rw [show d - ((0:ℕ):ℤ) = d by simp, ofPoly_toPoly] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma E_mul (α : Z →₀ ℕ) (f g : MvPolynomial (Y ⊕ Z) ℝ) :
    E α (f * g) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, E x.1 f * E x.2 g := by
  simp [E, map_mul, coeff_mul]

lemma gradeTup_apply (r : ℕ) {m : ℕ} {e : Fin m → ℤ} (h : Tup (Y ⊕ Z) e) (i : Fin m) :
    gradeTup r h i = grade r (h i) := rfl

lemma grade_mulMap {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom (Y ⊕ Z) (e i)) (t : ℤ)
    (w : Tup (Y ⊕ Z) (fun i => t - e i)) (n : ℕ) :
    grade n (mulMap p t w) = ∑ s ∈ Finset.range (n + 1),
      mulMap (fun i => grade (n - s) (p i)) t (gradeTup s w) := by
  apply hom_ext_E
  intro α
  rw [E_grade, toPoly_sum, E_sum]
  simp_rw [toPoly_mulMap, E_sum, E_mul, gradeTup_apply, E_grade]
  by_cases hα : deg α = n
  · rw [if_pos hα]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hd : deg x.1 + deg x.2 = n := by rw [← deg_add, hx, hα]
    rw [Finset.sum_eq_single (deg x.2)]
    · rw [if_pos (by omega), if_pos rfl]
    · intro s _ hs; rw [if_neg (Ne.symm hs), mul_zero]
    · intro hn; exfalso; apply hn; rw [Finset.mem_range]; omega
  · rw [if_neg hα]; symm
    apply Finset.sum_eq_zero; intro s hs
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Finset.mem_range] at hs
    have hd : deg x.1 + deg x.2 = deg α := by rw [← deg_add, hx]
    split_ifs with h1 h2
    · exfalso; omega
    · simp
    · simp
    · simp

end Split

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L43

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

/-! ### The pseudoinverse of a linear map between finite-dimensional inner product spaces -/

section Pinv

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `M` restricted to `(ker M)ᗮ`. -/
noncomputable def Mres (M : E →ₗ[ℝ] F) : (LinearMap.ker M)ᗮ →ₗ[ℝ] F :=
  M ∘ₗ (LinearMap.ker M)ᗮ.subtype

lemma Mres_ker (M : E →ₗ[ℝ] F) : LinearMap.ker (Mres M) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h1 : (x : E) ∈ LinearMap.ker M := hx
  have h0 := Submodule.inner_right_of_mem_orthogonal h1 x.2
  rw [inner_self_eq_zero] at h0
  exact Subtype.ext h0

/-- A left inverse of `Mres M`. -/
noncomputable def Linv (M : E →ₗ[ℝ] F) : F →ₗ[ℝ] (LinearMap.ker M)ᗮ :=
  (LinearMap.exists_leftInverse_of_injective (Mres M) (Mres_ker M)).choose

lemma Linv_Mres (M : E →ₗ[ℝ] F) (u : (LinearMap.ker M)ᗮ) : Linv M (Mres M u) = u := by
  have := (LinearMap.exists_leftInverse_of_injective (Mres M) (Mres_ker M)).choose_spec
  exact LinearMap.congr_fun this u

lemma range_Mres (M : E →ₗ[ℝ] F) (x : E) : ∃ u : (LinearMap.ker M)ᗮ, Mres M u = M x := by
  refine ⟨⟨(LinearMap.ker M)ᗮ.starProjection x, Submodule.starProjection_apply_mem _ x⟩, ?_⟩
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (LinearMap.ker M)ᗮ) x
  rw [Submodule.orthogonal_orthogonal] at h
  have := LinearMap.mem_ker.1 h
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

/-- The Moore–Penrose pseudoinverse. -/
noncomputable def Wp (M : E →ₗ[ℝ] F) : F →ₗ[ℝ] E :=
  (LinearMap.ker M)ᗮ.subtype ∘ₗ Linv M ∘ₗ
    ((LinearMap.range M).starProjection : F →L[ℝ] F).toLinearMap

lemma M_Wp (M : E →ₗ[ℝ] F) (v : F) : M (Wp M v) = (LinearMap.range M).starProjection v := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (Submodule.starProjection_apply_mem (LinearMap.range M) v)
  obtain ⟨u, hu⟩ := range_Mres M x
  simp only [Wp, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [← hx, ← hu, Linv_Mres]
  rfl

lemma Wp_mem (M : E →ₗ[ℝ] F) (v : F) : Wp M v ∈ (LinearMap.ker M)ᗮ := (Linv M _).2

lemma Wp_M_sub (M : E →ₗ[ℝ] F) (x : E) : x - Wp M (M x) ∈ LinearMap.ker M := by
  rw [LinearMap.mem_ker, map_sub, M_Wp,
    (Submodule.starProjection_eq_self_iff).2 (LinearMap.mem_range_self M x), sub_self]

lemma pinv_set_nonempty (M : E →ₗ[ℝ] F) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ u ∈ (LinearMap.ker M)ᗮ, ‖u‖ ≤ τ * ‖M u‖ := by
  let L := LinearMap.toContinuousLinearMap (Linv M)
  refine ⟨‖L‖, ContinuousLinearMap.opNorm_nonneg L, fun u hu => ?_⟩
  have h : L (M u) = ⟨u, hu⟩ := Linv_Mres M ⟨u, hu⟩
  calc ‖u‖ = ‖(⟨u, hu⟩ : (LinearMap.ker M)ᗮ)‖ := rfl
    _ = ‖L (M u)‖ := by rw [h]
    _ ≤ ‖L‖ * ‖M u‖ := L.le_opNorm _

lemma pinvNorm_nonneg (M : E →ₗ[ℝ] F) : 0 ≤ pinvNorm M :=
  Real.sInf_nonneg fun _ hτ => hτ.1

lemma norm_Wp (M : E →ₗ[ℝ] F) (v : F) : ‖Wp M v‖ ≤ pinvNorm M * ‖v‖ := by
  have key : ∀ τ ∈ {τ : ℝ | 0 ≤ τ ∧ ∀ u ∈ (LinearMap.ker M)ᗮ, ‖u‖ ≤ τ * ‖M u‖},
      ‖Wp M v‖ ≤ τ * ‖v‖ := by
    rintro τ ⟨hτ0, hτ⟩
    refine (hτ _ (Wp_mem M v)).trans ?_
    rw [M_Wp]
    exact mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ v) hτ0
  by_cases hv : v = 0
  · subst hv; simp
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have : ‖Wp M v‖ / ‖v‖ ≤ pinvNorm M := by
      apply le_csInf
      · obtain ⟨τ, h⟩ := pinv_set_nonempty M; exact ⟨τ, h⟩
      · intro τ hτ; exact (div_le_iff₀ hvpos).2 (key τ hτ)
    rwa [div_le_iff₀ hvpos] at this

end Pinv

lemma norm_ofPoly_toPoly_eq {σ : Type} [Fintype σ] [DecidableEq σ] {d d' : ℤ} (h : d = d')
    (x : Hom σ d) : ‖ofPoly d' (toPoly x)‖ = ‖x‖ := by
  subst h; rw [ofPoly_toPoly]

lemma norm_ofPoly_congr {σ : Type} [Fintype σ] [DecidableEq σ] {d d' : ℤ} (h : d = d')
    (f : MvPolynomial σ ℝ) : ‖ofPoly d f‖ = ‖ofPoly d' f‖ := by
  subst h; rfl

/-! ### The extended pseudoinverse `Ŵ_R` -/

section What

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

/-- The `z^α`-slice `E_α v`, read in `ℝ[y]_{=t-R}`. -/
noncomputable def sl (t R : ℕ) (α : Z →₀ ℕ) : Hom (Y ⊕ Z) (t : ℤ) →ₗ[ℝ] Hom Y ((t - R : ℕ) : ℤ) where
  toFun v := ofPoly ((t - R : ℕ) : ℤ) (E α (toPoly v))
  map_add' a b := by rw [toPoly_add, E_add]; exact (ofPolyL _).map_add _ _
  map_smul' c a := by rw [toPoly_smul, E_smul]; exact (ofPolyL _).map_smul _ _

lemma sl_apply (t R : ℕ) (α : Z →₀ ℕ) (v : Hom (Y ⊕ Z) (t : ℤ)) :
    sl t R α v = ofPoly ((t - R : ℕ) : ℤ) (E α (toPoly v)) := rfl

/-- `i`-th component of `Ŵ_R`. -/
noncomputable def WhC (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) (i : Fin m) :
    Hom (Y ⊕ Z) (t : ℤ) →ₗ[ℝ] Hom (Y ⊕ Z) ((t : ℤ) - (e i : ℤ)) where
  toFun v := ofPoly ((t : ℤ) - (e i : ℤ)) (∑ α ∈ monos Z (R : ℤ), zmon α *
      rename Sum.inl (toPoly ((Wp (mulMap p0 ((t - R : ℕ) : ℤ)) (sl t R α v)) i)))
  map_add' a b := by
    simp only [map_add, PiLp.add_apply, toPoly_add, mul_add, Finset.sum_add_distrib]
    exact (ofPolyL _).map_add _ _
  map_smul' c a := by
    simp only [map_smul, PiLp.smul_apply, toPoly_smul, mul_smul_comm, ← Finset.smul_sum,
      RingHom.id_apply]
    exact (ofPolyL _).map_smul _ _

lemma WhC_apply (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) (i : Fin m)
    (v : Hom (Y ⊕ Z) (t : ℤ)) :
    WhC e p0 t R i v = ofPoly ((t : ℤ) - (e i : ℤ)) (∑ α ∈ monos Z (R : ℤ), zmon α *
      rename Sum.inl (toPoly ((Wp (mulMap p0 ((t - R : ℕ) : ℤ)) (sl t R α v)) i))) := rfl

/-- The extended pseudoinverse `Ŵ_R`. -/
noncomputable def Wh (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) :
    Hom (Y ⊕ Z) (t : ℤ) →ₗ[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)) where
  toFun v := WithLp.toLp 2 (fun i => WhC e p0 t R i v)
  map_add' a b := by
    simp only [map_add]; rfl
  map_smul' c a := by
    simp only [map_smul]; rfl

lemma Wh_apply (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) (v : Hom (Y ⊕ Z) (t : ℤ))
    (i : Fin m) : Wh e p0 t R v i = WhC e p0 t R i v := rfl

lemma toPoly_Wh (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) (hR : R ≤ t)
    (v : Hom (Y ⊕ Z) (t : ℤ)) (i : Fin m) :
    toPoly (Wh e p0 t R v i) = ∑ α ∈ monos Z (R : ℤ), zmon α *
      rename Sum.inl (toPoly ((Wp (mulMap p0 ((t - R : ℕ) : ℤ)) (sl t R α v)) i)) := by
  rw [Wh_apply, WhC_apply, toPoly_ofPoly]
  apply IsH_sum
  intro α hα
  rw [mem_monos_Z] at hα
  refine ((IsH_zmon α).mul (IsH_rename_inl (IsH_toPoly _))).of_eq ?_
  rw [hα]; push_cast [Nat.cast_sub hR]; ring

lemma E_Wh (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) (hR : R ≤ t)
    (v : Hom (Y ⊕ Z) (t : ℤ)) (i : Fin m) (α' : Z →₀ ℕ) :
    E α' (toPoly (Wh e p0 t R v i)) = if α' ∈ monos Z (R : ℤ) then
      toPoly ((Wp (mulMap p0 ((t - R : ℕ) : ℤ)) (sl t R α' v)) i) else 0 := by
  rw [toPoly_Wh e p0 t R hR, E_sum]
  simp_rw [E_zmon_mul_rename]
  rw [Finset.sum_ite_eq']

lemma norm_sq_grade_eq (t R : ℕ) (hR : R ≤ t) (v : Hom (Y ⊕ Z) (t : ℤ)) :
    ‖grade R v‖ ^ 2 = ∑ α ∈ monos Z (R : ℤ),
      (mfact α * ((t - R).factorial : ℝ) / (t.factorial : ℝ)) * ‖sl (Y := Y) t R α v‖ ^ 2 := by
  rw [← ofPoly_toPoly (grade R v), toPoly_grade_decomp, norm_sq_zsum]
  have h1 : (t : ℤ) - (R : ℤ) = ((t - R : ℕ) : ℤ) := by push_cast [Nat.cast_sub hR]; ring
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sl_apply, norm_ofPoly_congr h1, h1]
  simp only [Int.toNat_natCast]

lemma coef_le (n R : ℕ) (hR : R ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    a * ((n - R).factorial : ℝ) / (n.factorial : ℝ) ≤ a / (R.factorial : ℝ) := by
  have h := Nat.factorial_mul_factorial_dvd_factorial hR
  have h2 : ((R.factorial * (n - R).factorial : ℕ) : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos n) h
  push_cast at h2
  have h3 : (0 : ℝ) < R.factorial := by positivity
  have h4 : (0 : ℝ) < n.factorial := by positivity
  rw [div_le_div_iff₀ h4 h3]
  nlinarith

lemma norm_Wh_sq (e : Fin m → ℕ) (p0 : ∀ i, Hom Y (e i : ℤ)) (t R : ℕ) (hR : R ≤ t)
    (v : Hom (Y ⊕ Z) (t : ℤ)) :
    ‖Wh e p0 t R v‖ ^ 2 ≤
      (t.choose R : ℝ) * pinvNorm (mulMap p0 ((t - R : ℕ) : ℤ)) ^ 2 * ‖v‖ ^ 2 := by
  set M := mulMap p0 ((t - R : ℕ) : ℤ) with hM
  set τ' := pinvNorm M
  set w : (Z →₀ ℕ) → Tup Y (fun i => ((t - R : ℕ) : ℤ) - (e i : ℤ)) :=
    fun α => Wp M (sl t R α v) with hw
  have hstep1 : ∀ i, ‖Wh e p0 t R v i‖ ^ 2 ≤
      ∑ α ∈ monos Z (R : ℤ), (mfact α / (R.factorial : ℝ)) * ‖w α i‖ ^ 2 := by
    intro i
    rw [Wh_apply, WhC_apply, norm_sq_zsum]
    apply Finset.sum_le_sum
    intro α _
    have hdeg : ((t - R : ℕ) : ℤ) - (e i : ℤ) = (t : ℤ) - (e i : ℤ) - (R : ℤ) := by
      push_cast [Nat.cast_sub hR]; ring
    rw [norm_ofPoly_toPoly_eq hdeg]
    by_cases hneg : (t : ℤ) - (e i : ℤ) - (R : ℤ) < 0
    · have : w α i = 0 := hom_eq_zero_of_neg (by show ((t - R : ℕ) : ℤ) - (e i : ℤ) < 0; omega) _
      rw [this]; simp
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have e1 : ((t : ℤ) - (e i : ℤ) - (R : ℤ)).toNat = ((t : ℤ) - (e i : ℤ)).toNat - R := by
        omega
      rw [e1]
      exact coef_le _ R (by omega) _ (mfact_pos α).le
  have hstep2 : ‖Wh e p0 t R v‖ ^ 2 ≤
      ∑ α ∈ monos Z (R : ℤ), (mfact α / (R.factorial : ℝ)) * ‖w α‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine (Finset.sum_le_sum fun i _ => hstep1 i).trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]
  have hstep3 : ∀ α, ‖w α‖ ^ 2 ≤ τ' ^ 2 * ‖sl (Y := Y) t R α v‖ ^ 2 := by
    intro α
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Wp M _) 2
  have hgr := norm_sq_grade_eq (Y := Y) t R hR v
  have hfac : (t.factorial : ℝ) = (t.choose R : ℝ) * R.factorial * (t - R).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hR).symm
  have hgle : ‖grade R v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_grade_le R v) 2
  calc ‖Wh e p0 t R v‖ ^ 2
      ≤ ∑ α ∈ monos Z (R : ℤ), (mfact α / (R.factorial : ℝ)) * (τ' ^ 2 * ‖sl (Y := Y) t R α v‖ ^ 2) :=
        hstep2.trans (Finset.sum_le_sum fun α _ =>
          mul_le_mul_of_nonneg_left (hstep3 α) (div_nonneg (mfact_pos α).le (by positivity)))
    _ = (t.choose R : ℝ) * τ' ^ 2 * ‖grade R v‖ ^ 2 := by
        rw [hgr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        have h3 : (0 : ℝ) < R.factorial := by positivity
        have h4 : (0 : ℝ) < (t - R).factorial := by positivity
        have h5 : (0 : ℝ) < (t.choose R : ℝ) := by exact_mod_cast Nat.choose_pos hR
        rw [hfac]
        field_simp
    _ ≤ (t.choose R : ℝ) * τ' ^ 2 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hgle (by positivity)

/-- The slices `E_α u_i`, read in `ℝ[y]_{=t-R-e_i}`. -/
noncomputable def sU (e : Fin m → ℕ) (t R : ℕ) (α : Z →₀ ℕ)
    (u : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) :
    Tup Y (fun i => ((t - R : ℕ) : ℤ) - (e i : ℤ)) :=
  WithLp.toLp 2 fun i => ofPoly _ (E α (toPoly (u i)))

lemma toPoly_sU (e : Fin m → ℕ) (t R : ℕ) (hR : R ≤ t) (α : Z →₀ ℕ) (hα : deg α = R)
    (u : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) (i : Fin m) :
    toPoly (sU e t R α u i) = E α (toPoly (u i)) := by
  apply toPoly_ofPoly
  refine (IsH_E (IsH_toPoly (u i)) α).of_eq ?_
  rw [hα]; push_cast [Nat.cast_sub hR]; ring

lemma key_slice (e : Fin m → ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (t R : ℕ) (hR : R ≤ t)
    (u : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) (α : Z →₀ ℕ) (hα : deg α = R) :
    sl t R α (mulMap (fun i => grade 0 (p i)) (t : ℤ) u) =
      mulMap (yParts p) ((t - R : ℕ) : ℤ) (sU e t R α u) := by
  apply toPoly_inj
  rw [sl_apply, toPoly_ofPoly]
  · rw [toPoly_mulMap, toPoly_mulMap, E_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [grade_zero_eq, toPoly_liftY, E_rename_inl_mul, toPoly_sU e t R hR α hα]
    rfl
  · refine (IsH_E (IsH_toPoly _) α).of_eq ?_
    rw [hα]; push_cast [Nat.cast_sub hR]; ring

lemma eq_of_le_deg {α α' : Z →₀ ℕ} (h : α ≤ α') (hd : deg α' ≤ deg α) : α = α' := by
  have h1 : α' = α + (α' - α) := (add_tsub_cancel_of_le h).symm
  have h2 : deg (α' - α) = 0 := by
    have := congrArg deg h1
    rw [deg_add] at this; omega
  rw [deg_eq_zero_iff, tsub_eq_zero_iff_le] at h2
  exact le_antisymm h h2

lemma key (e : Fin m → ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (t R : ℕ) (hR1 : 1 ≤ R) (hR : R ≤ t)
    (hK : KernelCond (yParts p) t)
    (u : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) (hu : gradeTup R u = u) :
    ∃ k' ∈ koszul p (t : ℤ), (∀ r < R, gradeTup r k' = 0) ∧
      gradeTup R k' = u - Wh e (yParts p) t R (mulMap (fun i => grade 0 (p i)) (t : ℤ) u) := by
  set M := mulMap (yParts p) ((t - R : ℕ) : ℤ) with hM
  set v := mulMap (fun i => grade 0 (p i)) (t : ℤ) u with hv
  have hΩ : ∀ α : Z →₀ ℕ, ∃ Ω : Fin m → Fin m → MvPolynomial Y ℝ,
      (∀ i j, IsH (((t - R : ℕ) : ℤ) - (e i : ℤ) - (e j : ℤ)) (Ω i j)) ∧
      (∀ i j, Ω i j = -Ω j i) ∧
      (deg α = R → ∀ i, toPoly ((sU e t R α u - Wp M (M (sU e t R α u))) i) =
        ∑ j, Ω i j * toPoly (yParts p j)) := by
    intro α
    by_cases hα : deg α = R
    · have hmem := Wp_M_sub M (sU e t R α u)
      have hk := hK (t - R) (by omega)
      have hmem' : sU e t R α u - Wp M (M (sU e t R α u)) ∈ koszul (yParts p) ((t - R : ℕ) : ℤ) := by
        rw [← hk]; exact hmem
      obtain ⟨Ω, h1, h2, h3⟩ := hmem'
      exact ⟨Ω, fun i j => (mem_homSpace_iff _ _).1 (h1 i j), h2, fun _ => h3⟩
    · exact ⟨0, fun i j => IsH_zero _, fun i j => by simp, fun h => absurd h hα⟩
  choose Ω hΩ1 hΩ2 hΩ3 using hΩ
  set Ω' : Fin m → Fin m → MvPolynomial (Y ⊕ Z) ℝ :=
    fun i j => ∑ α ∈ monos Z (R : ℤ), zmon α * rename Sum.inl (Ω α i j) with hΩ'
  have hΩ'H : ∀ i j, IsH ((t : ℤ) - (e i : ℤ) - (e j : ℤ)) (Ω' i j) := by
    intro i j
    apply IsH_sum
    intro α hα
    rw [mem_monos_Z] at hα
    refine ((IsH_zmon α).mul (IsH_rename_inl (hΩ1 α i j))).of_eq ?_
    rw [hα]; push_cast [Nat.cast_sub hR]; ring
  set k' : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)) :=
    WithLp.toLp 2 fun i => ofPoly _ (∑ j, Ω' i j * toPoly (p j)) with hk'
  have htk : ∀ i, toPoly (k' i) = ∑ j, Ω' i j * toPoly (p j) := by
    intro i
    apply toPoly_ofPoly
    apply IsH_sum
    intro j _
    exact ((hΩ'H i j).mul (IsH_toPoly (p j))).of_eq (by ring)
  have hkos : k' ∈ koszul p (t : ℤ) := by
    refine ⟨Ω', fun i j => (mem_homSpace_iff _ _).2 (hΩ'H i j), fun i j => ?_, htk⟩
    simp only [hΩ', hΩ2 _ i j, map_neg, mul_neg, Finset.sum_neg_distrib]
  have hEk : ∀ α' i, deg α' ≤ R → E α' (toPoly (k' i)) =
      if deg α' = R then ∑ j, Ω α' i j * toPoly (yParts p j) else 0 := by
    intro α' i hα'
    rw [htk, E_sum]
    have hj : ∀ j, E α' (Ω' i j * toPoly (p j)) =
        if deg α' = R then Ω α' i j * toPoly (yParts p j) else 0 := by
      intro j
      rw [hΩ', Finset.sum_mul, E_sum]
      simp_rw [mul_assoc, E_zmon_mul, E_rename_inl_mul]
      by_cases hd : deg α' = R
      · rw [if_pos hd, Finset.sum_eq_single α']
        · rw [if_pos le_rfl, tsub_self, ← toPoly_yPart]; rfl
        · intro α hα hne
          rw [mem_monos_Z] at hα
          rw [if_neg]
          intro hle; exact hne (eq_of_le_deg hle (by omega))
        · intro h; exfalso; exact h ((mem_monos_Z R α').2 hd)
      · rw [if_neg hd]
        apply Finset.sum_eq_zero
        intro α hα
        rw [mem_monos_Z] at hα
        rw [if_neg]
        intro hle
        have := eq_of_le_deg hle (by omega)
        subst this; exact hd hα
    simp_rw [hj]
    by_cases hd : deg α' = R
    · simp only [hd, if_true]
    · simp only [hd, if_false, Finset.sum_const_zero]
  refine ⟨k', hkos, ?_, ?_⟩
  · intro r hr
    ext1 i
    apply hom_ext_E
    intro α'
    rw [gradeTup_apply, E_grade]
    simp only [PiLp.zero_apply, toPoly_zero, E_zero]
    split_ifs with h
    · rw [hEk α' i (by omega), if_neg (by omega)]
    · rfl
  · ext1 i
    apply hom_ext_E
    intro α'
    rw [gradeTup_apply, E_grade, PiLp.sub_apply, toPoly_sub, E_sub, E_Wh e _ t R hR]
    by_cases hd : deg α' = R
    · rw [if_pos hd, if_pos ((mem_monos_Z R α').2 hd), hEk α' i hd.le, if_pos hd,
        ← hΩ3 α' hd i, PiLp.sub_apply, toPoly_sub, toPoly_sU e t R hR α' hd,
        key_slice e p t R hR u α' hd]
    · rw [if_neg hd, if_neg (fun h => hd ((mem_monos_Z R α').1 h)), sub_zero]
      rw [← hu, gradeTup_apply, E_grade, if_neg hd]

end What

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L43

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

section Rec

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

lemma liftY_add {d : ℤ} (a b : Hom Y d) : liftY (Z := Z) (a + b) = liftY a + liftY b := by
  apply toPoly_inj; rw [toPoly_add, toPoly_liftY, toPoly_liftY, toPoly_liftY, toPoly_add, map_add]

lemma liftY_smul {d : ℤ} (c : ℝ) (a : Hom Y d) : liftY (Z := Z) (c • a) = c • liftY a := by
  apply toPoly_inj; rw [toPoly_smul, toPoly_liftY, toPoly_liftY, toPoly_smul, map_smul]

lemma liftY_sub {d : ℤ} (a b : Hom Y d) : liftY (Z := Z) (a - b) = liftY a - liftY b := by
  apply toPoly_inj; rw [toPoly_sub, toPoly_liftY, toPoly_liftY, toPoly_liftY, toPoly_sub, map_sub]

lemma yPart_add {d : ℤ} (a b : Hom (Y ⊕ Z) d) : yPart (a + b) = yPart a + yPart b := by
  apply toPoly_inj; rw [toPoly_add, toPoly_yPart, toPoly_yPart, toPoly_yPart, toPoly_add, E_add]

lemma yPart_zero {d : ℤ} : yPart (0 : Hom (Y ⊕ Z) d) = 0 := by
  apply toPoly_inj; rw [toPoly_yPart, toPoly_zero, toPoly_zero, E_zero]

variable (e : Fin m → ℕ) (t : ℕ)

/-- `h₀ ↦ (liftY h₀_i)_i`. -/
noncomputable def liftL :
    Tup Y (fun i => (t : ℤ) - (e i : ℤ)) →ₗ[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)) where
  toFun h₀ := WithLp.toLp 2 fun i => liftY (h₀ i)
  map_add' a b := by
    ext1 i; simp only [PiLp.add_apply, liftY_add]
  map_smul' c a := by
    ext1 i; simp only [PiLp.smul_apply, liftY_smul, RingHom.id_apply]

variable (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))

/-- The maps `F_r`, on sequences `(f[0], f[1], …)`. -/
noncomputable def FL : ℕ →
    ((ℕ → Hom (Y ⊕ Z) (t : ℤ)) →ₗ[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)))
  | 0 => 0
  | r + 1 => Wh e (yParts p) t (r + 1) ∘ₗ
      (LinearMap.proj (R := ℝ) (φ := fun _ : ℕ => Hom (Y ⊕ Z) (t : ℤ)) (r + 1) -
        ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) ∘ₗ FL s)
termination_by r => r
decreasing_by exact s.isLt

/-- The maps `H_r`. -/
noncomputable def HL : ℕ →
    (Tup Y (fun i => (t : ℤ) - (e i : ℤ)) →ₗ[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)))
  | 0 => liftL e t
  | r + 1 => -(Wh e (yParts p) t (r + 1) ∘ₗ
        ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) ∘ₗ HL s)
termination_by r => r
decreasing_by exact s.isLt

lemma FL_zero (x : ℕ → Hom (Y ⊕ Z) (t : ℤ)) : FL e t p 0 x = 0 := by
  rw [FL]; rfl

lemma FL_succ (r : ℕ) (x : ℕ → Hom (Y ⊕ Z) (t : ℤ)) :
    FL e t p (r + 1) x = Wh e (yParts p) t (r + 1) (x (r + 1) -
      ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (FL e t p s x)) := by
  rw [FL]
  simp [LinearMap.sub_apply, LinearMap.sum_apply]

lemma HL_zero (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ))) : HL e t p 0 h₀ = liftL e t h₀ := by
  rw [HL]

lemma HL_succ (r : ℕ) (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ))) :
    HL e t p (r + 1) h₀ = -Wh e (yParts p) t (r + 1)
      (∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (HL e t p s h₀)) := by
  rw [HL]
  simp [LinearMap.sum_apply]

lemma FL_congr_x (r : ℕ) (x x' : ℕ → Hom (Y ⊕ Z) (t : ℤ)) (h : ∀ s ≤ r, x s = x' s) :
    FL e t p r x = FL e t p r x' := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    cases r with
    | zero => rw [FL_zero, FL_zero]
    | succ r =>
      rw [FL_succ, FL_succ, h (r + 1) le_rfl]
      congr 2
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ih s s.isLt fun s' hs' => h s' (by omega)]

lemma yParts_congr (p p' : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))
    (h : ∀ i, grade 0 (p i) = grade 0 (p' i)) : yParts p = yParts p' := by
  funext i
  exact yPart_eq_of_grade_zero (h i)

lemma FL_congr_p (r : ℕ) (p p' : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))
    (h : ∀ r', r' ≤ r → ∀ i, grade r' (p i) = grade r' (p' i)) :
    FL e t p r = FL e t p' r ∧ HL e t p r = HL e t p' r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    cases r with
    | zero => exact ⟨by rw [FL, FL], by rw [HL, HL]⟩
    | succ r =>
      have hy := yParts_congr e p p' (h 0 (Nat.zero_le _))
      have hg : ∀ s : Fin (r + 1), (fun i => grade (r + 1 - s) (p i)) =
          (fun i => grade (r + 1 - s) (p' i)) :=
        fun s => funext fun i => h _ (Nat.sub_le _ _) i
      have ih' : ∀ s : Fin (r + 1), FL e t p s = FL e t p' s ∧ HL e t p s = HL e t p' s :=
        fun s => ih s s.isLt fun r' hr' => h r' (by omega)
      constructor
      · ext1 x
        rw [FL_succ, FL_succ, hy]
        have : ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (FL e t p s x) =
            ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p' i)) (t : ℤ) (FL e t p' s x) :=
          Finset.sum_congr rfl fun s _ => by rw [hg s, (ih' s).1]
        rw [this]
      · ext1 x
        rw [HL_succ, HL_succ, hy]
        have : ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (HL e t p s x) =
            ∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p' i)) (t : ℤ) (HL e t p' s x) :=
          Finset.sum_congr rfl fun s _ => by rw [hg s, (ih' s).2]
        rw [this]

end Rec

/-! ### Norm bounds -/

section Bounds

lemma part3' {σ : Type} [Fintype σ] [DecidableEq σ] {d1 d2 d : ℤ} (hd : d = d1 + d2)
    (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (x : Hom σ d1) (y : Hom σ d2) :
    ‖ofPoly d (toPoly x * toPoly y)‖ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨n1, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨n2, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  subst hd
  exact part3 n1 n2 x y

lemma mulMap_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} {e : Fin m → ℤ}
    (q : ∀ i, Hom σ (e i)) (t : ℤ) (w : Tup σ (fun i => t - e i)) :
    mulMap q t w = ∑ i, ofPoly t (toPoly (q i) * toPoly (w i)) := by
  simp [mulMap, LinearMap.sum_apply, ofPolyL, toPolyL]
  rfl

lemma norm_mulMap_le {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} {e : Fin m → ℕ}
    (q : ∀ i, Hom σ (e i : ℤ)) (t : ℤ) (w : Tup σ (fun i => t - (e i : ℤ))) :
    ‖mulMap q t w‖ ≤ tupNorm q * ‖w‖ := by
  rw [mulMap_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i, ‖ofPoly t (toPoly (q i) * toPoly (w i))‖ ≤ ‖q i‖ * ‖w i‖ := by
    intro i
    by_cases hneg : t - (e i : ℤ) < 0
    · have h0 : ofPoly t (0 : MvPolynomial σ ℝ) = 0 := (ofPolyL (σ := σ) t).map_zero
      rw [hom_eq_zero_of_neg hneg (w i), toPoly_zero, mul_zero, h0, norm_zero]
      positivity
    · exact part3' (by ring) (by positivity) (by show (0:ℤ) ≤ t - (e i : ℤ); omega) (q i) (w i)
  calc ∑ i, ‖ofPoly t (toPoly (q i) * toPoly (w i))‖ ≤ ∑ i, ‖q i‖ * ‖w i‖ :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ √(∑ i, ‖q i‖ ^ 2) * √(∑ i, ‖w i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = tupNorm q * ‖w‖ := by
        rw [tupNorm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

lemma tupNorm_grade_le {e : Fin m → ℕ} (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (k : ℕ) :
    tupNorm (fun i => grade k (p i)) ≤ tupNorm p := by
  rw [tupNorm, tupNorm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_grade_le k (p i)) 2

lemma tauOf_nonneg {e : Fin m → ℕ} (p0 : ∀ i, Hom Y (e i : ℤ)) (t : ℕ) : 0 ≤ tauOf p0 t :=
  Real.iSup_nonneg fun _ => pinvNorm_nonneg _

lemma tupNorm_nonneg {e : Fin m → ℕ} (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) : 0 ≤ tupNorm p :=
  norm_nonneg _

lemma Wh_bound (T : ℕ) (e : Fin m → ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (t R : ℕ) (hR1 : 1 ≤ R)
    (hR : R ≤ t) (htT : t ≤ T) (v : Hom (Y ⊕ Z) (t : ℤ)) :
    ‖Wh e (yParts p) t R v‖ ≤ (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * ‖v‖ := by
  set τ' := pinvNorm (mulMap (yParts p) ((t - R : ℕ) : ℤ)) with hτ'def
  have hτ' : τ' ≤ tauOf (yParts p) t := by
    unfold tauOf
    exact le_ciSup (f := fun s : Fin t => pinvNorm (mulMap (yParts p) ((s : ℕ) : ℤ)))
      (Set.finite_range _).bddAbove ⟨t - R, by omega⟩
  have hτ'0 : 0 ≤ τ' := pinvNorm_nonneg _
  have hτ0 := tauOf_nonneg (yParts p) t
  have hc : ((2 : ℝ) ^ ((T : ℝ) / 2)) ^ 2 = 2 ^ T := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((T : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (T : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((T : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hb : (t.choose R : ℝ) ≤ 2 ^ T := by
    have h1 : t.choose R ≤ 2 ^ T :=
      (Nat.choose_le_two_pow t R).trans (Nat.pow_le_pow_right (by norm_num) htT)
    exact_mod_cast h1
  have h := norm_Wh_sq e (yParts p) t R hR v
  have hsq : ‖Wh e (yParts p) t R v‖ ^ 2 ≤
      ((2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * ‖v‖) ^ 2 := by
    calc ‖Wh e (yParts p) t R v‖ ^ 2 ≤ (t.choose R : ℝ) * τ' ^ 2 * ‖v‖ ^ 2 := h
      _ ≤ 2 ^ T * (tauOf (yParts p) t) ^ 2 * ‖v‖ ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, hc]
  have hpos : 0 ≤ (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * ‖v‖ :=
    mul_nonneg (mul_nonneg (by positivity) hτ0) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).1 hsq

/-- Bound sequence for `F_r`. -/
noncomputable def bF (K X : ℝ) (r : ℕ) : ℝ := if r = 0 then 0 else K * X ^ (r - 1)

/-- Bound sequence for `H_r`. -/
noncomputable def bH (K P X : ℝ) (r : ℕ) : ℝ := if r = 0 then 1 else K * P * X ^ (r - 1)

lemma geoF (K P : ℝ) (r : ℕ) :
    K * (1 + P * ∑ s ∈ Finset.range (r + 1), bF K (1 + K * P) s) = bF K (1 + K * P) (r + 1) := by
  induction r with
  | zero => simp [bF]
  | succ r ih =>
    have e1 : bF K (1 + K * P) (r + 1) = K * (1 + K * P) ^ r := by simp [bF]
    have e2 : bF K (1 + K * P) (r + 1 + 1) = K * (1 + K * P) ^ (r + 1) := by simp [bF]
    rw [Finset.sum_range_succ, e1, e2]
    rw [e1] at ih
    rw [pow_succ]
    linear_combination ih

lemma geoH (K P : ℝ) (r : ℕ) :
    K * P * ∑ s ∈ Finset.range (r + 1), bH K P (1 + K * P) s = bH K P (1 + K * P) (r + 1) := by
  induction r with
  | zero => simp [bH]
  | succ r ih =>
    have e1 : bH K P (1 + K * P) (r + 1) = K * P * (1 + K * P) ^ r := by simp [bH]
    have e2 : bH K P (1 + K * P) (r + 1 + 1) = K * P * (1 + K * P) ^ (r + 1) := by simp [bH]
    rw [Finset.sum_range_succ, e1, e2]
    rw [e1] at ih
    rw [pow_succ]
    linear_combination ih

lemma FL_bound (T : ℕ) (e : Fin m → ℕ) (t : ℕ) (htT : t ≤ T) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))
    (r : ℕ) (hr : r ≤ t) (x : ℕ → Hom (Y ⊕ Z) (t : ℤ)) (A : ℝ) (hA : 0 ≤ A)
    (hx : ∀ s ≤ r, ‖x s‖ ≤ A) :
    ‖FL e t p r x‖ ≤ bF ((2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t)
      (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) r * A := by
  set K := (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t with hK
  set P := tupNorm p with hP
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (tauOf_nonneg _ _)
  have hP0 : 0 ≤ P := tupNorm_nonneg p
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    cases r with
    | zero => rw [FL_zero]; simp [bF]
    | succ r =>
      rw [FL_succ]
      have hsum : ‖∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ)
          (FL e t p s x)‖ ≤ ∑ s ∈ Finset.range (r + 1), P * (bF K (1 + K * P) s * A) := by
        rw [← Fin.sum_univ_eq_sum_range (fun s => P * (bF K (1 + K * P) s * A))]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        refine (norm_mulMap_le _ _ _).trans ?_
        exact mul_le_mul (tupNorm_grade_le p _)
          (ih s s.isLt (by omega) fun s' hs' => hx s' (by omega)) (norm_nonneg _) hP0
      calc ‖Wh e (yParts p) t (r + 1) (x (r + 1) - ∑ s : Fin (r + 1),
            mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (FL e t p s x))‖
          ≤ K * ‖x (r + 1) - ∑ s : Fin (r + 1),
            mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (FL e t p s x)‖ :=
            Wh_bound T e p t (r + 1) (by omega) hr htT _
        _ ≤ K * (A + ∑ s ∈ Finset.range (r + 1), P * (bF K (1 + K * P) s * A)) := by
            gcongr
            exact (norm_sub_le _ _).trans (add_le_add (hx _ le_rfl) hsum)
        _ = K * (1 + P * ∑ s ∈ Finset.range (r + 1), bF K (1 + K * P) s) * A := by
            rw [show ∑ s ∈ Finset.range (r + 1), P * (bF K (1 + K * P) s * A) =
                P * (∑ s ∈ Finset.range (r + 1), bF K (1 + K * P) s) * A by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun s _ => by ring]
            ring
        _ = bF K (1 + K * P) (r + 1) * A := by rw [geoF]

lemma norm_liftL (e : Fin m → ℕ) (t : ℕ) (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ))) :
    ‖liftL (Z := Z) e t h₀‖ = ‖h₀‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show ‖liftY (h₀ i)‖ ^ 2 = _
  rw [norm_liftY]

lemma HL_bound (T : ℕ) (e : Fin m → ℕ) (t : ℕ) (htT : t ≤ T) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))
    (r : ℕ) (hr : r ≤ t) (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ))) :
    ‖HL e t p r h₀‖ ≤ bH ((2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t) (tupNorm p)
      (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) r * ‖h₀‖ := by
  set K := (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t with hK
  set P := tupNorm p with hP
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (tauOf_nonneg _ _)
  have hP0 : 0 ≤ P := tupNorm_nonneg p
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    cases r with
    | zero => rw [HL_zero, norm_liftL]; simp [bH]
    | succ r =>
      rw [HL_succ, norm_neg]
      have hsum : ‖∑ s : Fin (r + 1), mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ)
          (HL e t p s h₀)‖ ≤ ∑ s ∈ Finset.range (r + 1), P * (bH K P (1 + K * P) s * ‖h₀‖) := by
        rw [← Fin.sum_univ_eq_sum_range (fun s => P * (bH K P (1 + K * P) s * ‖h₀‖))]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        refine (norm_mulMap_le _ _ _).trans ?_
        exact mul_le_mul (tupNorm_grade_le p _) (ih s s.isLt (by omega)) (norm_nonneg _) hP0
      calc ‖Wh e (yParts p) t (r + 1) (∑ s : Fin (r + 1),
            mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (HL e t p s h₀))‖
          ≤ K * ‖∑ s : Fin (r + 1),
            mulMap (fun i => grade (r + 1 - s) (p i)) (t : ℤ) (HL e t p s h₀)‖ :=
            Wh_bound T e p t (r + 1) (by omega) hr htT _
        _ ≤ K * (∑ s ∈ Finset.range (r + 1), P * (bH K P (1 + K * P) s * ‖h₀‖)) := by
            gcongr
        _ = K * P * (∑ s ∈ Finset.range (r + 1), bH K P (1 + K * P) s) * ‖h₀‖ := by
            rw [show ∑ s ∈ Finset.range (r + 1), P * (bH K P (1 + K * P) s * ‖h₀‖) =
                P * (∑ s ∈ Finset.range (r + 1), bH K P (1 + K * P) s) * ‖h₀‖ by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun s _ => by ring]
            ring
        _ = bH K P (1 + K * P) (r + 1) * ‖h₀‖ := by rw [geoH]

end Bounds

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false

namespace ApproxSyzygies.Smoothed.Dev.L43

open MvPolynomial

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

section Identity

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

lemma gradeTup_add' (r : ℕ) {e : Fin m → ℤ} (a b : Tup (Y ⊕ Z) e) :
    gradeTup r (a + b) = gradeTup r a + gradeTup r b := by
  ext1 i; rw [PiLp.add_apply, gradeTup_apply, gradeTup_apply, gradeTup_apply, PiLp.add_apply,
    grade_add]

lemma gradeTup_sub' (r : ℕ) {e : Fin m → ℤ} (a b : Tup (Y ⊕ Z) e) :
    gradeTup r (a - b) = gradeTup r a - gradeTup r b := by
  ext1 i; rw [PiLp.sub_apply, gradeTup_apply, gradeTup_apply, gradeTup_apply, PiLp.sub_apply,
    grade_sub]

lemma gradeTup_gradeTup (r : ℕ) {e : Fin m → ℤ} (a : Tup (Y ⊕ Z) e) :
    gradeTup r (gradeTup r a) = gradeTup r a := by
  ext1 i; rw [gradeTup_apply, gradeTup_apply, grade_grade]

/-- Extension of `(f[0], …, f[r])` by zero. -/
noncomputable def extL (t r : ℕ) :
    (PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →ₗ[ℝ] (ℕ → Hom (Y ⊕ Z) (t : ℤ)) where
  toFun y s := if h : s < r + 1 then y ⟨s, h⟩ else 0
  map_add' a b := by
    funext s
    show (if h : s < r + 1 then (a + b) ⟨s, h⟩ else 0) =
      (if h : s < r + 1 then a ⟨s, h⟩ else 0) + (if h : s < r + 1 then b ⟨s, h⟩ else 0)
    split_ifs <;> simp
  map_smul' c a := by
    funext s
    show (if h : s < r + 1 then (c • a) ⟨s, h⟩ else 0) = c • (if h : s < r + 1 then a ⟨s, h⟩ else 0)
    split_ifs <;> simp

lemma FL_gradeSeg (e : Fin m → ℕ) (t : ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (r : ℕ)
    (f : Hom (Y ⊕ Z) (t : ℤ)) :
    (FL e t p r ∘ₗ extL t r) (gradeSeg r f) = FL e t p r (fun s => grade s f) := by
  rw [LinearMap.comp_apply]
  apply FL_congr_x
  intro s hs
  simp only [extL, LinearMap.coe_mk, AddHom.coe_mk, dif_pos (Nat.lt_succ_of_le hs)]
  rfl

lemma identity (e : Fin m → ℕ) (t : ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))
    (hK : KernelCond (yParts p) t) (R : ℕ) (hR : R ≤ t)
    (h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ)))
    (hh : h₀ - yPartTup h ∈ koszul (yParts p) (t : ℤ)) :
    ∃ k ∈ koszul p (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
      ∀ r ≤ R, gradeTup r h = gradeTup r k +
        FL e t p r (fun s => grade s (mulMap p (t : ℤ) h)) + HL e t p r h₀ := by
  induction R with
  | zero =>
    obtain ⟨Ω, h1, h2, h3⟩ := hh
    set Ω'' : Fin m → Fin m → MvPolynomial (Y ⊕ Z) ℝ :=
      fun i j => -rename Sum.inl (Ω i j) with hΩ''
    have hH : ∀ i j, IsH ((t : ℤ) - (e i : ℤ) - (e j : ℤ)) (Ω'' i j) :=
      fun i j => (IsH_rename_inl ((mem_homSpace_iff _ _).1 (h1 i j))).neg
    set k : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)) :=
      WithLp.toLp 2 fun i => ofPoly _ (∑ j, Ω'' i j * toPoly (p j)) with hk
    have htk : ∀ i, toPoly (k i) = ∑ j, Ω'' i j * toPoly (p j) := by
      intro i
      apply toPoly_ofPoly
      apply IsH_sum
      intro j _
      exact ((hH i j).mul (IsH_toPoly (p j))).of_eq (by ring)
    have hyk : yPartTup k = yPartTup h - h₀ := by
      ext1 i
      apply toPoly_inj
      rw [PiLp.sub_apply]
      show toPoly (yPart (k i)) = toPoly (yPart (h i) - h₀ i)
      rw [toPoly_yPart, htk, E_sum, toPoly_sub, toPoly_yPart]
      have h3i := h3 i
      rw [PiLp.sub_apply, toPoly_sub] at h3i
      simp only [hΩ'', neg_mul, E_neg, E_rename_inl_mul, Finset.sum_neg_distrib]
      have e2 : ∀ j, E 0 (toPoly (p j)) = toPoly (yParts p j) := fun j => (toPoly_yPart _).symm
      simp only [e2, ← h3i]
      rw [show yPartTup h i = yPart (h i) from rfl, toPoly_yPart]
      ring
    refine ⟨k, ⟨Ω'', fun i j => (mem_homSpace_iff _ _).2 (hH i j), fun i j => ?_, htk⟩, hyk, ?_⟩
    · simp only [hΩ'']; rw [h2 i j, map_neg, neg_neg]
    · intro r hr
      have : r = 0 := by omega
      subst this
      rw [FL_zero, HL_zero, add_zero]
      ext1 i
      rw [PiLp.add_apply, gradeTup_apply, gradeTup_apply, grade_zero_eq, grade_zero_eq]
      have hyi : yPart (k i) = yPart (h i) - h₀ i := by
        have := congrArg (fun x => x i) hyk
        simp only [PiLp.sub_apply] at this
        exact this
      rw [hyi, liftY_sub]
      show _ = _ + liftY (h₀ i)
      abel
  | succ R ih =>
    obtain ⟨k, hk, hy, hrows⟩ := ih (by omega)
    set h' := h - k with hh'
    set u := gradeTup (R + 1) h' with hu
    obtain ⟨k', hk', hlow, hrow⟩ :=
      key e p t (R + 1) (by omega) hR hK u (gradeTup_gradeTup (R + 1) h')
    refine ⟨k + k', koszul_add hk hk', ?_, ?_⟩
    · ext1 i
      show yPart ((k + k') i) = _
      rw [PiLp.add_apply, yPart_add]
      have hz : yPart (k' i) = 0 := by
        have h0 : grade 0 (k' i) = grade 0 (0 : Hom (Y ⊕ Z) ((t : ℤ) - (e i : ℤ))) := by
          rw [grade_zero']
          have := congrArg (fun x => x i) (hlow 0 (by omega))
          simpa [gradeTup_apply] using this
        rw [yPart_eq_of_grade_zero h0, yPart_zero]
      rw [hz, add_zero]
      exact congrArg (fun x => x i) hy
    · intro r hr
      rcases Nat.lt_or_ge r (R + 1) with hlt | hge
      · rw [gradeTup_add', hlow r hlt, add_zero]
        exact hrows r (by omega)
      · have hr' : r = R + 1 := by omega
        subst hr'
        set xf : ℕ → Hom (Y ⊕ Z) (t : ℤ) := fun s => grade s (mulMap p (t : ℤ) h) with hxf
        have hIH : ∀ s : Fin (R + 1), FL e t p s xf + HL e t p s h₀ = gradeTup s h' := by
          intro s
          rw [hh', gradeTup_sub', hrows s (by omega)]
          abel
        have hMh : mulMap p (t : ℤ) h = mulMap p (t : ℤ) h' := by
          rw [hh', map_sub, mulMap_koszul hk, sub_zero]
        have hrowf : xf (R + 1) =
            ∑ s : Fin (R + 1), mulMap (fun i => grade (R + 1 - s) (p i)) (t : ℤ) (gradeTup s h') +
              mulMap (fun i => grade 0 (p i)) (t : ℤ) u := by
          rw [hxf]
          simp only []
          rw [hMh, grade_mulMap, Finset.sum_range_succ, Nat.sub_self,
            Fin.sum_univ_eq_sum_range (fun s => mulMap (fun i => grade (R + 1 - s) (p i)) (t : ℤ)
              (gradeTup s h')) (R + 1)]
        have hFH : FL e t p (R + 1) xf + HL e t p (R + 1) h₀ =
            Wh e (yParts p) t (R + 1) (mulMap (fun i => grade 0 (p i)) (t : ℤ) u) := by
          rw [FL_succ, HL_succ, ← sub_eq_add_neg, ← map_sub]
          congr 1
          rw [hrowf, sub_sub, ← Finset.sum_add_distrib]
          have : ∀ s : Fin (R + 1),
              mulMap (fun i => grade (R + 1 - s) (p i)) (t : ℤ) (FL e t p s xf) +
                mulMap (fun i => grade (R + 1 - s) (p i)) (t : ℤ) (HL e t p s h₀) =
              mulMap (fun i => grade (R + 1 - s) (p i)) (t : ℤ) (gradeTup s h') := by
            intro s; rw [← map_add, hIH s]
          simp only [this]
          abel
        rw [gradeTup_add', hrow, add_assoc _ (FL e t p (R + 1) xf), hFH, hu, hh', gradeTup_sub']
        abel

/-- The continuous linear map `F_r`. -/
noncomputable def Fmap (e : Fin m → ℕ) (t : ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (r : ℕ) :
    (PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
      Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)) :=
  haveI : ContinuousSMul ℝ (PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) :=
    IsBoundedSMul.continuousSMul
  LinearMap.toContinuousLinearMap (FL e t p r ∘ₗ extL t r)

/-- The continuous linear map `H_r`. -/
noncomputable def Hmap (e : Fin m → ℕ) (t : ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (r : ℕ) :
    Tup Y (fun i => (t : ℤ) - (e i : ℤ)) →L[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ)) :=
  LinearMap.toContinuousLinearMap (HL e t p r)

lemma Fmap_apply (e : Fin m → ℕ) (t : ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (r : ℕ)
    (y : PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) :
    Fmap e t p r y = FL e t p r (extL t r y) := rfl

lemma Hmap_apply (e : Fin m → ℕ) (t : ℕ) (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ)) (r : ℕ)
    (y : Tup Y (fun i => (t : ℤ) - (e i : ℤ))) : Hmap e t p r y = HL e t p r y := rfl

end Identity

end ApproxSyzygies.Smoothed.Dev.L43

namespace ApproxSyzygies.Smoothed

open ApproxSyzygies.Smoothed.Dev.L43 in
theorem chk_lemma_4_3 (T : ℕ) {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} (e : Fin m → ℕ) (he : ∀ i, 1 ≤ e i) (t : ℕ) (htT : t ≤ T) (R : ℕ) (hR : R ≤ t) :
    ∃ F : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e i : ℤ)) →
        ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
          Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))),
    ∃ H : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e i : ℤ)) →
        (Tup Y (fun i => (t : ℤ) - (e i : ℤ)) →L[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))),
      (∀ r, r ≤ R → ∀ p p' : ∀ i, Hom (Y ⊕ Z) (e i : ℤ),
          (∀ r', r' ≤ r → ∀ i, grade r' (p i) = grade r' (p' i)) →
          F r p = F r p' ∧ H r p = H r p') ∧
      ∀ p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ), KernelCond (yParts p) t →
        (∀ r, r ≤ R →
          ‖F r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1)) ∧
          ‖H r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))) ∧
        ∀ (h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ))),
          h₀ - yPartTup h ∈ koszul (yParts p) (t : ℤ) →
          ∃ k ∈ koszul p (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
            ∀ r, r ≤ R →
              gradeTup r h = gradeTup r k + F r p (gradeSeg r (mulMap p (t : ℤ) h)) + H r p h₀ := by
  refine ⟨fun r p => Fmap e t p r, fun r p => Hmap e t p r, ?_, ?_⟩
  · intro r _ p p' hpp
    obtain ⟨h1, h2⟩ := FL_congr_p e t r p p' hpp
    exact ⟨by show Fmap e t p r = Fmap e t p' r; unfold Fmap; rw [h1],
      by show Hmap e t p r = Hmap e t p' r; unfold Hmap; rw [h2]⟩
  · intro p hK
    set K := (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t with hKdef
    set P := tupNorm p with hPdef
    set X := 1 + K * P with hXdef
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (tauOf_nonneg _ _)
    have hP0 : 0 ≤ P := tupNorm_nonneg p
    have hX1 : 1 ≤ X := by
      rw [hXdef]; linarith [mul_nonneg hK0 hP0]
    have hX0 : 0 ≤ X := by linarith
    set B := 1 + K * max (X ^ ((R : ℤ) - 1)) (P * X ^ ((R : ℤ) - 1)) with hB
    have hmax0 : 0 ≤ max (X ^ ((R : ℤ) - 1)) (P * X ^ ((R : ℤ) - 1)) :=
      le_max_of_le_left (zpow_nonneg hX0 _)
    have hB1 : 1 ≤ B := by
      rw [hB]; linarith [mul_nonneg hK0 hmax0]
    have hbF : ∀ r ≤ R, bF K X r ≤ B := by
      intro r hr
      unfold bF
      split_ifs with h0
      · linarith
      · have hzp : X ^ ((R : ℤ) - 1) = X ^ (R - 1) := by
          rw [show (R : ℤ) - 1 = ((R - 1 : ℕ) : ℤ) by omega, zpow_natCast]
        have h1 : X ^ (r - 1) ≤ X ^ (R - 1) := pow_le_pow_right₀ hX1 (by omega)
        have h2 : X ^ (R - 1) ≤ max (X ^ ((R : ℤ) - 1)) (P * X ^ ((R : ℤ) - 1)) := by
          rw [hzp]; exact le_max_left _ _
        rw [hB]
        nlinarith
    have hbH : ∀ r ≤ R, bH K P X r ≤ B := by
      intro r hr
      unfold bH
      split_ifs with h0
      · exact hB1
      · have hzp : X ^ ((R : ℤ) - 1) = X ^ (R - 1) := by
          rw [show (R : ℤ) - 1 = ((R - 1 : ℕ) : ℤ) by omega, zpow_natCast]
        have h1 : X ^ (r - 1) ≤ X ^ (R - 1) := pow_le_pow_right₀ hX1 (by omega)
        have h2 : P * X ^ (R - 1) ≤ max (X ^ ((R : ℤ) - 1)) (P * X ^ ((R : ℤ) - 1)) := by
          rw [hzp]; exact le_max_right _ _
        have h3 : P * X ^ (r - 1) ≤ P * X ^ (R - 1) := mul_le_mul_of_nonneg_left h1 hP0
        rw [hB, mul_assoc]
        nlinarith
    refine ⟨fun r hr => ⟨?_, ?_⟩, ?_⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun y => ?_
      rw [Fmap_apply]
      refine (FL_bound T e t htT p r (by omega) _ ‖y‖ (norm_nonneg _) fun s hs => ?_).trans ?_
      · simp only [extL, LinearMap.coe_mk, AddHom.coe_mk, dif_pos (Nat.lt_succ_of_le hs)]
        exact PiLp.norm_apply_le y _
      · exact mul_le_mul_of_nonneg_right (hbF r hr) (norm_nonneg _)
    · refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun y => ?_
      rw [Hmap_apply]
      exact (HL_bound T e t htT p r (by omega) y).trans
        (mul_le_mul_of_nonneg_right (hbH r hr) (norm_nonneg _))
    · intro h h₀ hh
      obtain ⟨k, hk, hy, hrows⟩ := identity e t p hK R hR h h₀ hh
      refine ⟨k, hk, hy, fun r hr => ?_⟩
      rw [hrows r hr, Fmap_apply, Hmap_apply, ← LinearMap.comp_apply, FL_gradeSeg]

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_lemma_4_3 := @ApproxSyzygies.Smoothed.chk_lemma_4_3
