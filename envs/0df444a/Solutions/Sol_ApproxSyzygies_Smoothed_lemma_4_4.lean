-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T22:27:38.855664+00:00
-- url     : https://prove2.me/submissions/7440e48b-3fcd-45e3-9490-ef789d48b47d

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_2
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_3

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

lemma IsH.sub {d : ℤ} {f g : MvPolynomial σ ℝ} (hf : IsH d f) (hg : IsH d g) : IsH d (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

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

lemma grade_sub (r : ℕ) {d : ℤ} (f g : Hom (Y ⊕ Z) d) : grade r (f - g) = grade r f - grade r g := by
  ext γ; simp only [grade, PiLp.sub_apply]; split_ifs <;> simp

lemma grade_zero' (r : ℕ) {d : ℤ} : grade r (0 : Hom (Y ⊕ Z) d) = 0 := by
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

lemma pinvNorm_nonneg (M : E →ₗ[ℝ] F) : 0 ≤ pinvNorm M :=
  Real.sInf_nonneg fun _ hτ => hτ.1

end Pinv

lemma norm_ofPoly_toPoly_eq {σ : Type} [Fintype σ] [DecidableEq σ] {d d' : ℤ} (h : d = d')
    (x : Hom σ d) : ‖ofPoly d' (toPoly x)‖ = ‖x‖ := by
  subst h; rw [ofPoly_toPoly]

/-! ### The extended pseudoinverse `Ŵ_R` -/

section What

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

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

variable (e : Fin m → ℕ) (t : ℕ)

variable (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))

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

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

end Bounds

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

/-! ### Generic algebra -/

section Generic

variable {σ : Type} [Fintype σ] [DecidableEq σ]

lemma ofPoly_add' (d : ℤ) (f g : MvPolynomial σ ℝ) : ofPoly d (f + g) = ofPoly d f + ofPoly d g :=
  (ofPolyL d).map_add f g

lemma ofPoly_smul' (d : ℤ) (c : ℝ) (f : MvPolynomial σ ℝ) : ofPoly d (c • f) = c • ofPoly d f :=
  (ofPolyL d).map_smul c f

lemma ofPoly_zero' (d : ℤ) : ofPoly d (0 : MvPolynomial σ ℝ) = 0 := (ofPolyL d).map_zero

lemma IsH_pow {d : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) (n : ℕ) : IsH (d * n) (f ^ n) := by
  induction n with
  | zero =>
    intro γ h
    simp only [pow_zero, coeff_one] at h
    split_ifs at h with h0
    · subst h0; simp [deg]
    · exact absurd rfl h
  | succ n ih => rw [pow_succ]; exact (ih.mul hf).of_eq (by push_cast; ring)

lemma IsH.eq_zero_of_neg {d : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) (hd : d < 0) : f = 0 := by
  ext γ
  by_contra h
  have := hf γ (by simpa using h)
  omega

/-- `‖x^n w‖ ≤ ‖x‖^n ‖w‖`. -/
lemma norm_pow_mul_le {k s : ℤ} (hk : 0 ≤ k) (x : Hom σ k) (w : Hom σ s) (n : ℕ) (u : ℤ)
    (hu : u = k * n + s) : ‖ofPoly u (toPoly x ^ n * toPoly w)‖ ≤ ‖x‖ ^ n * ‖w‖ := by
  induction n generalizing u with
  | zero =>
    subst hu
    simp only [pow_zero, one_mul]
    rw [norm_ofPoly_toPoly_eq (by push_cast; ring)]
  | succ n ih =>
    set u' : ℤ := k * n + s
    by_cases hu' : 0 ≤ u'
    · have hH : IsH u' (toPoly x ^ n * toPoly w) :=
        ((IsH_pow (IsH_toPoly x) n).mul (IsH_toPoly w)).of_eq rfl
      have e1 : toPoly x ^ (n + 1) * toPoly w =
          toPoly x * toPoly (ofPoly u' (toPoly x ^ n * toPoly w)) := by
        rw [toPoly_ofPoly u' _ hH]; ring
      rw [e1]
      calc _ ≤ ‖x‖ * ‖ofPoly u' (toPoly x ^ n * toPoly w)‖ :=
            part3' (by rw [hu]; push_cast; ring) hk hu' x _
        _ ≤ ‖x‖ * (‖x‖ ^ n * ‖w‖) := mul_le_mul_of_nonneg_left (ih u' rfl) (norm_nonneg _)
        _ = _ := by ring
    · have hs : s < 0 := by
        have : (0 : ℤ) ≤ k * n := mul_nonneg hk (by positivity)
        omega
      rw [IsH.eq_zero_of_neg (IsH_toPoly w) hs, mul_zero, ofPoly_zero', norm_zero]
      positivity

lemma norm_tup_le_of {σ' : Type} [Fintype σ'] [DecidableEq σ'] {m : ℕ} {e e' : Fin m → ℤ}
    (x : Tup σ e) (y : Tup σ' e') (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j, ‖x j‖ ≤ c * ‖y j‖) : ‖x‖ ≤ c * ‖y‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2

lemma norm_mulMap_leZ {m : ℕ} {e : Fin m → ℤ} (he : ∀ j, 0 ≤ e j)
    (q : ∀ i, Hom σ (e i)) (t : ℤ) (w : Tup σ (fun i => t - e i)) :
    ‖mulMap q t w‖ ≤ tupNorm q * ‖w‖ := by
  rw [mulMap_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i, ‖ofPoly t (toPoly (q i) * toPoly (w i))‖ ≤ ‖q i‖ * ‖w i‖ := by
    intro i
    by_cases hneg : t - e i < 0
    · rw [hom_eq_zero_of_neg hneg (w i), toPoly_zero, mul_zero, ofPoly_zero', norm_zero]
      positivity
    · exact part3' (by ring) (he i) (not_lt.1 hneg) (q i) (w i)
  calc ∑ i, ‖ofPoly t (toPoly (q i) * toPoly (w i))‖ ≤ ∑ i, ‖q i‖ * ‖w i‖ :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ √(∑ i, ‖q i‖ ^ 2) * √(∑ i, ‖w i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = tupNorm q * ‖w‖ := by
        rw [tupNorm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]

lemma tupNorm_nonneg' {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) : 0 ≤ tupNorm p := by
  unfold tupNorm; exact norm_nonneg _

lemma norm_le_tupNorm {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (j : Fin m) :
    ‖p j‖ ≤ tupNorm p :=
  PiLp.norm_apply_le (WithLp.toLp 2 p : Tup σ e) j

end Generic

/-! ### Splitting variables -/

section Split

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

lemma E0_eq (f : MvPolynomial (Y ⊕ Z) ℝ) : E 0 f = constantCoeff (Phi f) := rfl

lemma E0_mul (f g : MvPolynomial (Y ⊕ Z) ℝ) : E 0 (f * g) = E 0 f * E 0 g := by
  rw [E0_eq, E0_eq, E0_eq, map_mul, map_mul]

lemma E0_pow (f : MvPolynomial (Y ⊕ Z) ℝ) (n : ℕ) : E 0 (f ^ n) = E 0 f ^ n := by
  rw [E0_eq, E0_eq, map_pow, map_pow]

lemma Phi_rename_inr (W : MvPolynomial Z ℝ) :
    Phi (rename Sum.inr W : MvPolynomial (Y ⊕ Z) ℝ) = map C W := by
  induction W using MvPolynomial.induction_on with
  | C a => simp [Phi, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p z hp => rw [map_mul, rename_X, map_mul, hp]; simp [Phi]

lemma E_rename_inr (α : Z →₀ ℕ) (W : MvPolynomial Z ℝ) :
    E α (rename Sum.inr W : MvPolynomial (Y ⊕ Z) ℝ) = C (coeff α W) := by
  rw [E, Phi_rename_inr, coeff_map]

lemma IsH_rename_inr {d : ℤ} {g : MvPolynomial Z ℝ} (hg : IsH d g) :
    IsH d (rename Sum.inr g : MvPolynomial (Y ⊕ Z) ℝ) := by
  intro γ h
  rw [coeff_E, E_rename_inr, coeff_C] at h
  split_ifs at h with hy
  · have := hg _ h
    rw [deg_split, ← hy]; simpa [deg] using this
  · exact absurd rfl h

lemma toPoly_liftZ {d : ℤ} (u : Hom Z d) :
    toPoly (liftZ (Y := Y) u) = rename Sum.inr (toPoly u) := by
  rw [liftZ, toPoly_ofPoly]
  exact IsH_rename_inr (IsH_toPoly u)

lemma E0_liftZ {d : ℤ} (hd : 1 ≤ d) (u : Hom Z d) : E 0 (toPoly (liftZ (Y := Y) u)) = 0 := by
  rw [toPoly_liftZ, E_rename_inr]
  have : coeff 0 (toPoly u) = 0 := by
    by_contra h
    have := IsH_toPoly u 0 h
    simp [deg] at this; omega
  rw [this, C_0]

lemma E_rename_inr_mul (α : Z →₀ ℕ) (W : MvPolynomial Z ℝ) (G : MvPolynomial (Y ⊕ Z) ℝ) :
    E α (rename Sum.inr W * G) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, C (coeff x.1 W) * E x.2 G := by
  rw [E_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [E_rename_inr]

lemma E_rinr_mul_of_deg {R : ℕ} {W : MvPolynomial Z ℝ} (hW : IsH (R : ℤ) W)
    (G : MvPolynomial (Y ⊕ Z) ℝ) (α : Z →₀ ℕ) (hα : deg α = R) :
    E α (rename Sum.inr W * G) = C (coeff α W) * E 0 G := by
  rw [E_rename_inr_mul, Finset.sum_eq_single (α, 0)]
  · intro x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hc : coeff x.1 W = 0
    · rw [hc, C_0, zero_mul]
    · exfalso
      have h1 := hW _ hc
      have h2 : deg x.1 + deg x.2 = deg α := by rw [← deg_add, hx]
      have h3 : deg x.2 = 0 := by omega
      rw [deg_eq_zero_iff] at h3
      apply hne
      ext1
      · simp only; rw [← hx, h3, add_zero]
      · exact h3
  · intro h; exfalso; apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_zero]

lemma E_rinr_mul_of_lt {R : ℕ} {W : MvPolynomial Z ℝ} (hW : IsH (R : ℤ) W)
    (G : MvPolynomial (Y ⊕ Z) ℝ) (α : Z →₀ ℕ) (hα : deg α < R) :
    E α (rename Sum.inr W * G) = 0 := by
  rw [E_rename_inr_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases hc : coeff x.1 W = 0
  · rw [hc, C_0, zero_mul]
  · exfalso
    have h1 := hW _ hc
    have h2 : deg x.1 + deg x.2 = deg α := by rw [← deg_add, hx]
    omega

lemma norm_yPart_le {d : ℤ} (f : Hom (Y ⊕ Z) d) : ‖yPart f‖ ≤ ‖f‖ := by
  rw [← norm_liftY (Z := Z), ← grade_zero_eq]; exact norm_grade_le 0 f

lemma norm_gradeSeg_le (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) :
    ‖gradeSeg r f‖ ≤ ((r : ℝ) + 1) * ‖f‖ := by
  rw [PiLp.norm_eq_of_L2, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ r' : Fin (r + 1), ‖(gradeSeg r f) r'‖ ^ 2 ≤ ∑ _r' : Fin (r + 1), ‖f‖ ^ 2 :=
        Finset.sum_le_sum fun r' _ => pow_le_pow_left₀ (norm_nonneg _) (norm_grade_le _ f) 2
    _ = ((r : ℝ) + 1) * ‖f‖ ^ 2 := by simp
    _ ≤ (((r : ℝ) + 1) * ‖f‖) ^ 2 := by
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        nlinarith

lemma grade_rinr_eq_zero {R : ℕ} {W : MvPolynomial Z ℝ} (hW : IsH (R : ℤ) W) {t : ℤ}
    (G : MvPolynomial (Y ⊕ Z) ℝ) (hG : IsH t (rename Sum.inr W * G)) (r : ℕ) (hr : r < R) :
    grade r (ofPoly t (rename Sum.inr W * G)) = 0 := by
  apply hom_ext_E
  intro α
  rw [E_grade, toPoly_ofPoly t _ hG, toPoly_zero, E_zero]
  split_ifs with h
  · exact E_rinr_mul_of_lt hW G α (by omega)
  · rfl

end Split

/-! ### The projection `Π^⊥_J` applied to the `y`-coefficients of the `z`-monomials of degree `R` -/

section Proj

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- `f ↦ ∑_{|α| = R} z^α · Π^⊥_Q (E_α f)`. -/
noncomputable def Pproj (t R : ℕ) {s : ℤ} (Q : Submodule ℝ (Hom Y s)) :
    Hom (Y ⊕ Z) (t : ℤ) →ₗ[ℝ] Hom (Y ⊕ Z) (t : ℤ) where
  toFun f := ofPoly (t : ℤ) (∑ α ∈ monos Z (R : ℤ), zmon α *
      rename Sum.inl (toPoly (Qᗮ.starProjection (ofPoly s (E α (toPoly f))))))
  map_add' a b := by
    simp only [toPoly_add, E_add, ofPoly_add', map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [toPoly_smul, E_smul, ofPoly_smul', map_smul, toPoly_smul, mul_smul_comm,
      ← Finset.smul_sum, RingHom.id_apply]

lemma Pproj_apply (t R : ℕ) {s : ℤ} (Q : Submodule ℝ (Hom Y s)) (f : Hom (Y ⊕ Z) (t : ℤ)) :
    Pproj t R Q f = ofPoly (t : ℤ) (∑ α ∈ monos Z (R : ℤ), zmon α *
      rename Sum.inl (toPoly (Qᗮ.starProjection (ofPoly s (E α (toPoly f)))))) := rfl

lemma Pproj_grade (t R : ℕ) {s : ℤ} (Q : Submodule ℝ (Hom Y s)) (f : Hom (Y ⊕ Z) (t : ℤ)) :
    Pproj (Z := Z) t R Q (grade R f) = Pproj t R Q f := by
  rw [Pproj_apply, Pproj_apply]
  apply congrArg (ofPoly (t : ℤ))
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [mem_monos_Z] at hα
  rw [E_grade, if_pos hα]

lemma norm_Pproj_le (t R : ℕ) {s : ℤ} (hs : s = (t : ℤ) - (R : ℤ)) (Q : Submodule ℝ (Hom Y s))
    (f : Hom (Y ⊕ Z) (t : ℤ)) : ‖Pproj t R Q f‖ ≤ ‖f‖ := by
  subst hs
  have h1 := norm_sq_zsum (Y := Y) (Z := Z) (t : ℤ) R
    (fun α => toPoly (Qᗮ.starProjection (ofPoly ((t : ℤ) - (R : ℤ)) (E α (toPoly f)))))
  have h2 := norm_sq_zsum (Y := Y) (Z := Z) (t : ℤ) R (fun α => E α (toPoly f))
  rw [← toPoly_grade_decomp, ofPoly_toPoly] at h2
  rw [← Pproj_apply] at h1
  simp only [ofPoly_toPoly] at h1
  have h3 : ‖Pproj (Z := Z) t R Q f‖ ^ 2 ≤ ‖grade R f‖ ^ 2 := by
    rw [h1, h2]
    refine Finset.sum_le_sum fun α _ => ?_
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2
    · have := mfact_pos α
      positivity
  have h4 := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
  exact h4.trans (norm_grade_le R f)

lemma Pproj_mul_mem (t R : ℕ) {s : ℤ} (Q : Submodule ℝ (Hom Y s)) (U : MvPolynomial Y ℝ)
    (G : MvPolynomial (Y ⊕ Z) ℝ) (hUG : IsH (t : ℤ) (rename Sum.inl U * G))
    (hU : ∀ α : Z →₀ ℕ, deg α = R → ofPoly s (U * E α G) ∈ Q) :
    Pproj t R Q (ofPoly (t : ℤ) (rename Sum.inl U * G)) = 0 := by
  rw [Pproj_apply, toPoly_ofPoly _ _ hUG]
  rw [← ofPoly_zero' (σ := Y ⊕ Z) (t : ℤ)]
  apply congrArg (ofPoly (t : ℤ))
  apply Finset.sum_eq_zero
  intro α hα
  rw [mem_monos_Z] at hα
  rw [E_rename_inl_mul, Submodule.starProjection_orthogonal_apply_eq_zero (hU α hα), toPoly_zero,
    map_zero, mul_zero]

lemma Pproj_rinr (t R : ℕ) {s : ℤ} (Q : Submodule ℝ (Hom Y s)) {W : MvPolynomial Z ℝ}
    (hW : IsH (R : ℤ) W) (G : MvPolynomial (Y ⊕ Z) ℝ) (hG : IsH (t : ℤ) (rename Sum.inr W * G)) :
    Pproj t R Q (ofPoly (t : ℤ) (rename Sum.inr W * G)) =
      ofPoly (t : ℤ) (rename Sum.inr W *
        rename Sum.inl (toPoly (Qᗮ.starProjection (ofPoly s (E 0 G))))) := by
  rw [Pproj_apply, toPoly_ofPoly _ _ hG]
  apply congrArg (ofPoly (t : ℤ))
  apply ext_E
  intro α'
  rw [E_sum]
  simp_rw [E_zmon_mul_rename]
  rw [Finset.sum_ite_eq']
  split_ifs with hα
  · rw [mem_monos_Z] at hα
    rw [E_rinr_mul_of_deg hW _ _ hα, E_rinr_mul_of_deg hW _ _ hα, E_rename_inl, if_pos rfl,
      C_mul', C_mul', ofPoly_smul', map_smul, toPoly_smul]
  · rw [E_rename_inr_mul]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [E_rename_inl]
    split_ifs with h0
    · rw [h0, add_zero] at hx
      rw [hx]
      by_cases hc : coeff α' W = 0
      · rw [hc, C_0, zero_mul]
      · exact absurd ((mem_monos_iff _ _).2 (hW _ hc)) hα
    · rw [mul_zero]

end Proj

end ApproxSyzygies.Smoothed.Dev.L44
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

section Fam

variable {m : ℕ} (d D : Fin m → ℕ) (i : Fin m)

lemma modDeg_self : modDeg d D i i = d i := by simp [modDeg]

lemma modDeg_ne {j : Fin m} (h : j ≠ i) : modDeg d D i j = (d j : ℤ) * (D j : ℤ) := by
  simp [modDeg, h]

lemma modDeg_nonneg (j : Fin m) : 0 ≤ modDeg d D i j := by
  unfold modDeg; split_ifs <;> positivity

lemma toPoly_powHom {σ : Type} [Fintype σ] [DecidableEq σ] {e : ℤ} (x : Hom σ e) (n : ℕ) :
    toPoly (powHom x n) = toPoly x ^ n :=
  toPoly_ofPoly _ _ (IsH_pow (IsH_toPoly x) n)

lemma toPoly_modGen {σ : Type} [Fintype σ] [DecidableEq σ] (c : MvPolynomial σ ℝ)
    (hc : IsH (d i : ℤ) c) (a : ∀ j, Hom σ (d j : ℤ)) (j : Fin m) :
    toPoly (modGen d D i c a j) = if j = i then c else toPoly (a j) ^ D j := by
  unfold modGen
  split_ifs with h
  · subst h; exact toPoly_ofPoly _ _ (hc.of_eq (modDeg_self d D _).symm)
  · exact toPoly_ofPoly _ _ ((IsH_pow (IsH_toPoly (a j)) (D j)).of_eq (modDeg_ne d D i h).symm)

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The modified family `b̃`. -/
noncomputable def btil (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ)) :
    ∀ j, Hom (Y ⊕ Z) (modDeg d D i j) :=
  modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a

variable (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ))

lemma toPoly_btil (j : Fin m) :
    toPoly (btil d D i a v j) =
      if j = i then toPoly (a i) - toPoly (liftZ (Y := Y) v) else toPoly (a j) ^ D j :=
  toPoly_modGen d D i _ ((IsH_toPoly _).sub (IsH_toPoly _)) a j

lemma yPart_eq {d : ℤ} (f : Hom (Y ⊕ Z) d) : yPart f = ofPoly d (E 0 (toPoly f)) := by
  rw [yPart, aeval_elim_eq_E]

lemma toPoly_yPart_btil (hd : 1 ≤ d i) (j : Fin m) :
    toPoly (yPart (btil d D i a v j)) =
      if j = i then E 0 (toPoly (a i)) else E 0 (toPoly (a j)) ^ D j := by
  rw [toPoly_yPart, toPoly_btil]
  split_ifs
  · rw [E_sub, E0_liftZ (by exact_mod_cast hd), sub_zero]
  · rw [E0_pow]

lemma yParts_btil (hd : 1 ≤ d i) :
    yParts (btil d D i a v) = modGen d D i (toPoly (yParts a i)) (yParts a) := by
  funext j
  apply toPoly_inj
  rw [show yParts (btil d D i a v) j = yPart (btil d D i a v j) from rfl,
    toPoly_yPart_btil d D i a v hd, toPoly_modGen d D i _ (IsH_toPoly _)]
  simp only [yParts, toPoly_yPart]

lemma Jpiece_eq (t : ℕ) (hd : 1 ≤ d i) :
    Jpiece d D t (yParts a) i =
      idealDeg (yParts (btil d D i a v)) ((t : ℤ) - (d i : ℤ) * (D i : ℤ)) := by
  rw [yParts_btil d D i a v hd]; rfl

/-- `b[0]` reconstructed from `b̃`. -/
noncomputable def b0fun (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) :
    ∀ j, Hom Y ((d j : ℤ) * (D j : ℤ)) :=
  fun j => ofPoly ((d j : ℤ) * (D j : ℤ))
    (if j = i then toPoly (yPart (b i)) ^ D i else toPoly (yPart (b j)))

lemma b0fun_btil (hd : 1 ≤ d i) :
    b0fun d D i (btil d D i a v) = yParts (fun j => powHom (a j) (D j)) := by
  funext j
  apply toPoly_inj
  rw [show yParts (fun j => powHom (a j) (D j)) j = yPart (powHom (a j) (D j)) from rfl,
    toPoly_yPart, toPoly_powHom, E0_pow]
  unfold b0fun
  rw [toPoly_ofPoly]
  · split_ifs with h
    · subst h; rw [toPoly_yPart_btil d D _ a v hd, if_pos rfl]
    · rw [toPoly_yPart_btil d D i a v hd, if_neg h]
  · split_ifs with h
    · subst h
      exact (IsH_pow (IsH_toPoly _) _).of_eq (by rw [modDeg_self])
    · exact (IsH_toPoly _).of_eq (modDeg_ne d D i h)

lemma norm_b0fun_le (hD : 1 ≤ D i) (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) :
    tupNorm (b0fun d D i b) ≤ (1 + tupNorm b) ^ (D i - 1) * tupNorm b := by
  have hβ : 0 ≤ tupNorm b := tupNorm_nonneg' b
  have hc1 : 1 ≤ (1 + tupNorm b) ^ (D i - 1) := one_le_pow₀ (by linarith)
  have key : ∀ j, ‖b0fun d D i b j‖ ≤ (1 + tupNorm b) ^ (D i - 1) * ‖b j‖ := by
    intro j
    unfold b0fun
    split_ifs with h
    · subst h
      have e1 : toPoly (yPart (b j)) ^ D j =
          toPoly (yPart (b j)) ^ (D j - 1) * toPoly (yPart (b j)) := by
        rw [← pow_succ, Nat.sub_add_cancel hD]
      rw [e1]
      refine (norm_pow_mul_le (modDeg_nonneg d D j j) _ _ _ _ ?_).trans ?_
      · rw [modDeg_self]; push_cast [Nat.cast_sub hD]; ring
      · have h1 : ‖yPart (b j)‖ ≤ ‖b j‖ := norm_yPart_le _
        have h2 : ‖b j‖ ≤ tupNorm b := norm_le_tupNorm b j
        gcongr
        linarith
    · rw [norm_ofPoly_toPoly_eq (modDeg_ne d D i h)]
      calc ‖yPart (b j)‖ ≤ ‖b j‖ := norm_yPart_le _
        _ ≤ (1 + tupNorm b) ^ (D i - 1) * ‖b j‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hc1
  unfold tupNorm
  exact norm_tup_le_of _ _ _ (by positivity) key

/-- `w ↦ w̃`: multiply slot `i` by `a_i[0]^{D_i - 1}`. -/
noncomputable def tildeL (t : ℕ) (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) :
    Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →ₗ[ℝ]
      Tup Y (fun j => (t : ℤ) - modDeg d D i j) where
  toFun w := WithLp.toLp 2 fun j => ofPoly ((t : ℤ) - modDeg d D i j)
    (if j = i then toPoly (yPart (b i)) ^ (D i - 1) * toPoly (w i) else toPoly (w j))
  map_add' x y := by
    ext1 j
    simp only [PiLp.add_apply, WithLp.ofLp_toLp]
    split_ifs <;> simp [toPoly_add, mul_add, ofPoly_add']
  map_smul' c x := by
    ext1 j
    simp only [PiLp.smul_apply, WithLp.ofLp_toLp, RingHom.id_apply]
    split_ifs <;> simp [toPoly_smul, mul_smul_comm, ofPoly_smul']

lemma tildeL_apply (t : ℕ) (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j))
    (w : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) (j : Fin m) :
    tildeL d D i t b w j = ofPoly ((t : ℤ) - modDeg d D i j)
      (if j = i then toPoly (yPart (b i)) ^ (D i - 1) * toPoly (w i) else toPoly (w j)) := rfl

lemma norm_tildeL_le (hD : 1 ≤ D i) (t : ℕ) (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j))
    (w : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) :
    ‖tildeL d D i t b w‖ ≤ (1 + tupNorm b) ^ (D i - 1) * ‖w‖ := by
  have hβ : 0 ≤ tupNorm b := tupNorm_nonneg' b
  have hc1 : 1 ≤ (1 + tupNorm b) ^ (D i - 1) := one_le_pow₀ (by linarith)
  apply norm_tup_le_of _ _ _ (by positivity)
  intro j
  rw [tildeL_apply]
  split_ifs with h
  · subst h
    refine (norm_pow_mul_le (modDeg_nonneg d D j j) _ _ _ _ ?_).trans ?_
    · rw [modDeg_self]; push_cast [Nat.cast_sub hD]; ring
    · have h1 : ‖yPart (b j)‖ ≤ ‖b j‖ := norm_yPart_le _
      have h2 : ‖b j‖ ≤ tupNorm b := norm_le_tupNorm b j
      gcongr
      linarith
  · rw [norm_ofPoly_toPoly_eq (by rw [modDeg_ne d D i h])]
    exact le_mul_of_one_le_left (norm_nonneg _) hc1

/-- `q = ∑_{k < n} A^k V^{n - 1 - k}`. -/
noncomputable def qpoly {σ : Type} (A V : MvPolynomial σ ℝ) (n : ℕ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.range n, A ^ k * V ^ (n - 1 - k)

lemma qpoly_mul {σ : Type} (A V : MvPolynomial σ ℝ) (n : ℕ) :
    qpoly A V n * (A - V) = A ^ n - V ^ n := geom_sum₂_mul A V n

lemma IsH_qpoly {σ : Type} [Fintype σ] [DecidableEq σ] {e : ℤ} {A V : MvPolynomial σ ℝ}
    (hA : IsH e A) (hV : IsH e V) (n : ℕ) : IsH (e * ((n - 1 : ℕ) : ℤ)) (qpoly A V n) := by
  apply IsH_sum
  intro k hk
  rw [Finset.mem_range] at hk
  refine ((IsH_pow hA k).mul (IsH_pow hV (n - 1 - k))).of_eq ?_
  have : ((n - 1 : ℕ) : ℤ) = (k : ℤ) + ((n - 1 - k : ℕ) : ℤ) := by omega
  rw [this]; ring

lemma E0_qpoly {A V : MvPolynomial (Y ⊕ Z) ℝ} (hV : E 0 V = 0) (n : ℕ) (hn : 1 ≤ n) :
    E 0 (qpoly A V n) = E 0 A ^ (n - 1) := by
  rw [qpoly, E_sum]
  simp_rw [E0_mul, E0_pow, hV]
  rw [Finset.sum_eq_single (n - 1)]
  · simp
  · intro k hk hne
    rw [Finset.mem_range] at hk
    rw [zero_pow (by omega), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

/-- `h̃`: slot `i` multiplied by `q`. -/
noncomputable def htil (t : ℕ) (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) :
    Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j) :=
  WithLp.toLp 2 fun j => ofPoly ((t : ℤ) - modDeg d D i j)
    (if j = i then qpoly (toPoly (a i)) (toPoly (liftZ (Y := Y) v)) (D i) * toPoly (h i)
      else toPoly (h j))

lemma toPoly_htil (hD : 1 ≤ D i) (t : ℕ)
    (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) (j : Fin m) :
    toPoly (htil d D i a v t h j) =
      if j = i then qpoly (toPoly (a i)) (toPoly (liftZ (Y := Y) v)) (D i) * toPoly (h i)
        else toPoly (h j) := by
  show toPoly (ofPoly _ _) = _
  rw [toPoly_ofPoly]
  split_ifs with hj
  · subst hj
    refine ((IsH_qpoly (IsH_toPoly (a j)) (IsH_toPoly (liftZ v)) (D j)).mul
      (IsH_toPoly (h j))).of_eq ?_
    beta_reduce; rw [modDeg_self]; push_cast [Nat.cast_sub hD]; ring
  · exact (IsH_toPoly (h j)).of_eq (by beta_reduce; rw [modDeg_ne d D i hj])

lemma IsH_vpow_mul {t : ℤ} {e : ℤ} (he : e = (d i : ℤ) * (D i : ℤ)) (u : Hom (Y ⊕ Z) (t - e)) :
    IsH t (toPoly (liftZ (Y := Y) v) ^ D i * toPoly u) :=
  ((IsH_pow (IsH_toPoly (liftZ v)) (D i)).mul (IsH_toPoly u)).of_eq (by rw [he]; ring)

lemma mulMap_htil (hD : 1 ≤ D i) (t : ℕ)
    (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) :
    mulMap (btil d D i a v) (t : ℤ) (htil d D i a v t h) =
      mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h -
        ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i * toPoly (h i)) := by
  apply toPoly_inj
  rw [toPoly_mulMap, toPoly_sub, toPoly_mulMap, toPoly_ofPoly _ _ (IsH_vpow_mul d D i v rfl _)]
  calc ∑ j, toPoly (btil d D i a v j) * toPoly (htil d D i a v t h j)
      = ∑ j, (toPoly (powHom (a j) (D j)) * toPoly (h j) -
          if j = i then toPoly (liftZ (Y := Y) v) ^ D i * toPoly (h i) else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [toPoly_btil, toPoly_htil d D i a v hD, toPoly_powHom]
        split_ifs with hj
        · subst hj
          linear_combination (toPoly (h j)) *
            qpoly_mul (toPoly (a j)) (toPoly (liftZ (Y := Y) v)) (D j)
        · ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']; simp

lemma yPartTup_htil (hd : 1 ≤ d i) (hD : 1 ≤ D i) (t : ℕ)
    (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) :
    yPartTup (htil d D i a v t h) = tildeL d D i t (btil d D i a v) (yPartTup h) := by
  ext1 j
  rw [tildeL_apply]
  show yPart (htil d D i a v t h j) = _
  rw [yPart_eq, toPoly_htil d D i a v hD]
  apply congrArg
  split_ifs with hj
  · subst hj
    rw [E0_mul, E0_qpoly (E0_liftZ (by exact_mod_cast hd) v) _ hD, toPoly_yPart_btil d D _ a v hd,
      if_pos rfl]
    show _ = _ * toPoly (yPart (h j))
    rw [toPoly_yPart]
  · show _ = toPoly (yPart (h j))
    rw [toPoly_yPart]

lemma gradeSeg_htil (hD : 1 ≤ D i) (t : ℕ)
    (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) (s : ℕ) (hs : s < d i * D i) :
    gradeSeg s (mulMap (btil d D i a v) (t : ℤ) (htil d D i a v t h)) =
      gradeSeg s (mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h) := by
  rw [mulMap_htil d D i a v hD]
  unfold gradeSeg
  apply congrArg (WithLp.toLp 2)
  funext r
  have hW : IsH ((d i * D i : ℕ) : ℤ) (toPoly v ^ D i) :=
    (IsH_pow (IsH_toPoly v) (D i)).of_eq (by push_cast; ring)
  have e1 : toPoly (liftZ (Y := Y) v) ^ D i * toPoly (h i) =
      rename Sum.inr (toPoly v ^ D i) * toPoly (h i) := by
    rw [toPoly_liftZ, map_pow]
  rw [grade_sub, e1, grade_rinr_eq_zero hW _ (e1 ▸ IsH_vpow_mul d D i v rfl _) r
    (by have := r.isLt; omega), sub_zero]

/-- Koszul syzygies of `p[0]` lift to Koszul syzygies of `p`. -/
lemma lift_koszul {e : Fin m → ℤ} (p : ∀ j, Hom (Y ⊕ Z) (e j)) (s : ℤ)
    (k₀ : Tup Y (fun j => s - e j)) (hk₀ : k₀ ∈ koszul (yParts p) s) :
    ∃ k ∈ koszul p s, yPartTup k = k₀ := by
  obtain ⟨Ω, hΩ1, hΩ2, hΩ3⟩ := hk₀
  have hH : ∀ j, IsH (s - e j) (∑ l, rename Sum.inl (Ω j l) * toPoly (p l)) := by
    intro j
    apply IsH_sum
    intro l _
    exact ((IsH_rename_inl ((mem_homSpace_iff _ _).1 (hΩ1 j l))).mul (IsH_toPoly (p l))).of_eq
      (by ring)
  refine ⟨WithLp.toLp 2 fun j => ofPoly (s - e j) (∑ l, rename Sum.inl (Ω j l) * toPoly (p l)),
    ⟨fun j l => rename Sum.inl (Ω j l), fun j l => ?_, fun j l => ?_, fun j => ?_⟩, ?_⟩
  · exact (mem_homSpace_iff _ _).2 (IsH_rename_inl ((mem_homSpace_iff _ _).1 (hΩ1 j l)))
  · show rename Sum.inl (Ω j l) = -rename Sum.inl (Ω l j)
    rw [hΩ2 j l, map_neg]
  · exact toPoly_ofPoly _ _ (hH j)
  · ext1 j
    apply toPoly_inj
    show toPoly (yPart (ofPoly (s - e j) _)) = _
    rw [toPoly_yPart, toPoly_ofPoly _ _ (hH j), E_sum, hΩ3 j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [E_rename_inl_mul, ← toPoly_yPart]
    rfl

lemma koszul_mem_Jpiece (t : ℕ) (k₀ : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)))
    (hk₀ : k₀ ∈ koszul (yParts (fun j => powHom (a j) (D j))) (t : ℤ)) :
    k₀ i ∈ Jpiece d D t (yParts a) i := by
  obtain ⟨Ω, hΩ1, hΩ2, hΩ3⟩ := hk₀
  have hii : Ω i i = 0 := by
    have := hΩ2 i i
    have h2 : (2 : ℝ) • Ω i i = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  set s : ℤ := (t : ℤ) - (d i : ℤ) * (D i : ℤ)
  have hu : ∀ l, IsH (s - modDeg d D i l) (if l = i then 0 else Ω i l) := by
    intro l
    split_ifs with hl
    · exact IsH_zero _
    · exact ((mem_homSpace_iff _ _).1 (hΩ1 i l)).of_eq (by rw [modDeg_ne d D i hl])
  refine LinearMap.mem_range.2
    ⟨WithLp.toLp 2 fun l => ofPoly (s - modDeg d D i l) (if l = i then 0 else Ω i l), ?_⟩
  apply toPoly_inj
  rw [toPoly_mulMap, hΩ3 i]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ * toPoly (ofPoly _ _) = _
  rw [toPoly_ofPoly _ _ (hu l), toPoly_modGen d D i _ (IsH_toPoly _)]
  split_ifs with hl
  · subst hl; rw [hii, mul_zero, zero_mul]
  · rw [show yParts (fun j => powHom (a j) (D j)) l = yPart (powHom (a l) (D l)) from rfl,
      toPoly_yPart, toPoly_powHom, E0_pow]
    simp only [yParts, toPoly_yPart]
    ring

end Fam

end ApproxSyzygies.Smoothed.Dev.L44
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

section Eq

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable {m : ℕ} (d D : Fin m → ℕ) (i : Fin m) (t : ℕ)

lemma zero_mem_koszul {σ : Type} [Fintype σ] [DecidableEq σ] {e : Fin m → ℤ} (p : ∀ j, Hom σ (e j))
    (s : ℤ) : (0 : Tup σ (fun j => s - e j)) ∈ koszul p s :=
  ⟨fun _ _ => 0, fun _ _ => zero_mem _, fun _ _ => by simp, fun j => by
    simp [toPoly_zero]⟩

lemma gradeTup_sub'' (r : ℕ) {e : Fin m → ℤ} (x y : Tup (Y ⊕ Z) e) :
    gradeTup r (x - y) = gradeTup r x - gradeTup r y := by
  ext1 j; rw [PiLp.sub_apply, gradeTup_apply, gradeTup_apply, gradeTup_apply, PiLp.sub_apply,
    grade_sub]

lemma gradeSeg_zero (r : ℕ) {e : ℤ} : gradeSeg r (0 : Hom (Y ⊕ Z) e) = 0 := by
  unfold gradeSeg
  ext1 r'
  simp only [WithLp.ofLp_toLp, grade_zero']
  rfl

/-- `J_i` from `b̃`. -/
noncomputable def QJ (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) :
    Submodule ℝ (Hom Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ))) :=
  idealDeg (yParts b) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))

/-- The projection `Π^⊥_{J_i}` on the `z`-monomials of degree `R = d_i D_i`. -/
noncomputable def PP (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) :
    Hom (Y ⊕ Z) (t : ℤ) →ₗ[ℝ] Hom (Y ⊕ Z) (t : ℤ) :=
  Pproj t (d i * D i) (QJ d D i t b)

lemma PP_kill (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j))
    (x : Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)) :
    PP d D i t b (mulMap (fun j => grade 0 (b j)) (t : ℤ) x) = 0 := by
  rw [mulMap_eq_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [grade_zero_eq, toPoly_liftY]
  apply Pproj_mul_mem
  · exact ((IsH_rename_inl (IsH_toPoly _)).mul (IsH_toPoly _)).of_eq (by ring)
  · intro α hα
    set s : ℤ := (t : ℤ) - (d i : ℤ) * (D i : ℤ)
    have hE : IsH (s - modDeg d D i j) (E α (toPoly (x j))) :=
      (IsH_E (IsH_toPoly (x j)) α).of_eq (by rw [hα]; push_cast; ring)
    refine ⟨WithLp.toLp 2 fun l => ofPoly (s - modDeg d D i l)
      (if l = j then E α (toPoly (x j)) else 0), ?_⟩
    rw [← ofPoly_toPoly (mulMap _ _ _), toPoly_mulMap]
    apply congrArg
    rw [Finset.sum_eq_single j]
    · show toPoly (yPart (b j)) * toPoly (ofPoly _ _) = _
      rw [if_pos rfl, toPoly_ofPoly _ _ hE]
    · intro l _ hl
      show _ * toPoly (ofPoly _ _) = _
      rw [if_neg hl, ofPoly_zero', toPoly_zero, mul_zero]
    · simp

/-- The map `A_i(u) = Π^⊥_{J_i} ∑_{r < R} b̃[R - r]ᵀ H_r(ũ)`. -/
noncomputable def AA
    (H : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      (Tup Y (fun j => (t : ℤ) - modDeg d D i j) →L[ℝ] Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) :
    Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →ₗ[ℝ] Hom (Y ⊕ Z) (t : ℤ) :=
  ∑ s ∈ Finset.range (d i * D i), PP d D i t b ∘ₗ
    mulMap (fun j => grade (d i * D i - s) (b j)) (t : ℤ) ∘ₗ (H s b).toLinearMap ∘ₗ
      tildeL d D i t b

/-- The right-hand side of (16). -/
noncomputable def BB
    (F : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
        Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) (f : Hom (Y ⊕ Z) (t : ℤ)) : Hom (Y ⊕ Z) (t : ℤ) :=
  PP d D i t b f - ∑ s ∈ Finset.range (d i * D i),
    PP d D i t b (mulMap (fun j => grade (d i * D i - s) (b j)) (t : ℤ) (F s b (gradeSeg s f)))

lemma BB_zero
    (F : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
        Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) : BB d D i t F b 0 = 0 := by
  unfold BB
  simp only [gradeSeg_zero, map_zero, Finset.sum_const_zero, sub_zero]

variable (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ))

/-- Equation (16). -/
lemma eq16 (hd : 1 ≤ d i) (hD : 1 ≤ D i)
    (F : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
        Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (H : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      (Tup Y (fun j => (t : ℤ) - modDeg d D i j) →L[ℝ] Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (hid : ∀ (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j))
        (h₀ : Tup Y (fun j => (t : ℤ) - modDeg d D i j)),
        h₀ - yPartTup h ∈ koszul (yParts (btil d D i a v)) (t : ℤ) →
        ∃ k ∈ koszul (btil d D i a v) (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
          ∀ r, r ≤ d i * D i - 1 →
            gradeTup r h = gradeTup r k + F r (btil d D i a v)
              (gradeSeg r (mulMap (btil d D i a v) (t : ℤ) h)) + H r (btil d D i a v) h₀)
    (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) :
    ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
        toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) +
      AA d D i t H (btil d D i a v) (yPartTup h) =
    BB d D i t F (btil d D i a v) (mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h) := by
  set b := btil d D i a v with hb
  set R := d i * D i with hR
  set f := mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h with hf
  obtain ⟨k, hk, -, hrows⟩ := hid (htil d D i a v t h) (yPartTup (htil d D i a v t h))
    (by rw [sub_self]; exact zero_mem_koszul _ _)
  set w := htil d D i a v t h - k with hw
  -- the `v^{D_i} g_i` term
  set W : MvPolynomial Z ℝ := toPoly v ^ D i with hW
  have hWH : IsH ((R : ℕ) : ℤ) W := (IsH_pow (IsH_toPoly v) (D i)).of_eq (by rw [hR]; push_cast; ring)
  have hV : toPoly (liftZ (Y := Y) v) ^ D i = rename Sum.inr W := by rw [toPoly_liftZ, map_pow]
  have hG : IsH (t : ℤ) (rename Sum.inr W * toPoly (h i)) := by
    rw [← hV]; exact IsH_vpow_mul d D i v rfl _
  set Vt := ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
        toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) with hVt
  have hPX : PP d D i t b (ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i * toPoly (h i))) = Vt := by
    rw [hV, PP, Pproj_rinr _ _ _ hWH _ hG, hVt, hV, toPoly_liftY]
    apply congrArg; apply congrArg; apply congrArg; apply congrArg
    show _ = (Jpiece d D t (yParts a) i)ᗮ.starProjection (yPart (h i))
    rw [Jpiece_eq d D i a v t hd, yPart_eq]
    rfl
  have e1 : PP d D i t b (mulMap b (t : ℤ) w) = PP d D i t b f - Vt := by
    rw [hw, map_sub, mulMap_koszul hk, sub_zero, mulMap_htil d D i a v hD, map_sub, hPX]
  -- decomposition by rows
  have hrow : ∀ s ∈ Finset.range R, gradeTup s w =
      F s b (gradeSeg s f) + H s b (tildeL d D i t b (yPartTup h)) := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hw, gradeTup_sub'', hrows s (by omega), gradeSeg_htil d D i a v hD t h s hs,
      yPartTup_htil d D i a v hd hD t h]
    abel
  have e2 : PP d D i t b (mulMap b (t : ℤ) w) =
      ∑ s ∈ Finset.range R, PP d D i t b (mulMap (fun j => grade (R - s) (b j)) (t : ℤ)
        (F s b (gradeSeg s f))) + AA d D i t H b (yPartTup h) := by
    rw [PP, ← Pproj_grade, grade_mulMap, map_sum, Finset.sum_range_succ, Nat.sub_self]
    rw [show Pproj t (d i * D i) (QJ d D i t b) (mulMap (fun j => grade 0 (b j)) (t : ℤ)
      (gradeTup R w)) = 0 from PP_kill d D i t b _, add_zero]
    rw [AA, LinearMap.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hrow s hs, map_add, map_add]
    rfl
  have e3 : AA d D i t H b (yPartTup h) = (PP d D i t b f - Vt) -
      ∑ s ∈ Finset.range R, PP d D i t b (mulMap (fun j => grade (R - s) (b j)) (t : ℤ)
        (F s b (gradeSeg s f))) := by
    rw [← e1, e2]; abel
  rw [e3, BB]
  abel

lemma AA_koszul (hd : 1 ≤ d i) (hD : 1 ≤ D i)
    (F : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
        Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (H : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      (Tup Y (fun j => (t : ℤ) - modDeg d D i j) →L[ℝ] Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (hid : ∀ (h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j))
        (h₀ : Tup Y (fun j => (t : ℤ) - modDeg d D i j)),
        h₀ - yPartTup h ∈ koszul (yParts (btil d D i a v)) (t : ℤ) →
        ∃ k ∈ koszul (btil d D i a v) (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
          ∀ r, r ≤ d i * D i - 1 →
            gradeTup r h = gradeTup r k + F r (btil d D i a v)
              (gradeSeg r (mulMap (btil d D i a v) (t : ℤ) h)) + H r (btil d D i a v) h₀)
    (k₀ : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)))
    (hk₀ : k₀ ∈ koszul (yParts (fun j => powHom (a j) (D j))) (t : ℤ)) :
    AA d D i t H (btil d D i a v) k₀ = 0 := by
  obtain ⟨k, hk, hk0⟩ := lift_koszul (fun j => powHom (a j) (D j)) (t : ℤ) k₀ hk₀
  have := eq16 d D i t a v hd hD F H hid k
  rw [mulMap_koszul hk, BB_zero, hk0] at this
  have hg : gVec d D t (yParts a) k₀ i = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (koszul_mem_Jpiece d D i a t k₀ hk₀)
  rw [hg, toPoly_liftY, toPoly_zero, map_zero, mul_zero, ofPoly_zero', zero_add] at this
  exact this

end Eq

end ApproxSyzygies.Smoothed.Dev.L44
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

/-- Lemma 4.3 for a degree family `e'` equal to `fun j => (e j : ℤ)` (not definitionally). -/
lemma l43' (T : ℕ) {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} (e : Fin m → ℕ) (e' : Fin m → ℤ) (hee : e' = fun j => (e j : ℤ))
    (he : ∀ i, 1 ≤ e i) (t : ℕ) (htT : t ≤ T) (R : ℕ) (hR : R ≤ t) :
    ∃ F : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e' i)) →
        ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
          Tup (Y ⊕ Z) (fun i => (t : ℤ) - e' i)),
    ∃ H : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e' i)) →
        (Tup Y (fun i => (t : ℤ) - e' i) →L[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - e' i)),
      ∀ p : ∀ i, Hom (Y ⊕ Z) (e' i), KernelCond (yParts p) t →
        (∀ r, r ≤ R →
          ‖F r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1)) ∧
          ‖H r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))) ∧
        ∀ (h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - e' i)) (h₀ : Tup Y (fun i => (t : ℤ) - e' i)),
          h₀ - yPartTup h ∈ koszul (yParts p) (t : ℤ) →
          ∃ k ∈ koszul p (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
            ∀ r, r ≤ R →
              gradeTup r h = gradeTup r k + F r p (gradeSeg r (mulMap p (t : ℤ) h)) + H r p h₀ := by
  subst hee
  obtain ⟨F, H, -, hFH⟩ := ApproxSyzygies.Smoothed.lemma_4_3 T (Y := Y) (Z := Z) e he t htT R hR
  exact ⟨F, H, hFH⟩

lemma bound43 (T : ℕ) (τ' τ β y : ℝ) (hτ' : 0 ≤ τ') (hτ : τ' ≤ τ) (hβ : 0 ≤ β) (n : ℤ)
    (hn : n ≤ T)
    (hy : y ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * τ' *
      max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * τ' * β) ^ n)
        (β * (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * τ' * β) ^ n)) :
    y ≤ 2 * ((2 : ℝ) ^ T * (1 + τ) * (1 + β)) ^ (T + 1) := by
  set c := (2 : ℝ) ^ ((T : ℝ) / 2) with hc
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) (by positivity)
  have hcT : c ≤ (2 : ℝ) ^ T := by
    rw [hc, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (0 : ℝ) ≤ T := by positivity
      linarith)
  have h2T : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  set X := 1 + c * τ' * β with hX
  have hX1 : 1 ≤ X := by have : 0 ≤ c * τ' * β := by positivity
                         linarith
  have hXn : X ^ n ≤ X ^ T := by
    rw [← zpow_natCast]; exact zpow_le_zpow_right₀ hX1 hn
  set G := (2 : ℝ) ^ T * (1 + τ) * (1 + β) with hG
  have hτ0 : 0 ≤ τ := hτ'.trans hτ
  have hcτ : c * τ' ≤ (2 : ℝ) ^ T * (1 + τ) := by
    calc c * τ' ≤ (2 : ℝ) ^ T * τ := mul_le_mul hcT hτ hτ' (by positivity)
      _ ≤ _ := by nlinarith
  have hG1 : 1 ≤ G := by
    have : 1 ≤ (1 + τ) * (1 + β) := by nlinarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ T * ((1 + τ) * (1 + β)) := mul_le_mul h2T this zero_le_one (by positivity)
      _ = G := by ring
  have hXG : X ≤ G := by
    have h1 : c * τ' * β ≤ (2 : ℝ) ^ T * (1 + τ) * β := mul_le_mul_of_nonneg_right hcτ hβ
    have h2 : (2 : ℝ) ^ T * (1 + τ) * (1 + β) = (2 : ℝ) ^ T * (1 + τ) + (2 : ℝ) ^ T * (1 + τ) * β :=
      by ring
    have h3 : 1 ≤ (2 : ℝ) ^ T * (1 + τ) := by nlinarith
    rw [hX, hG, h2]; linarith
  have hXT0 : 0 ≤ X ^ T := by positivity
  have hmax : max (X ^ n) (β * X ^ n) ≤ (1 + β) * X ^ T := by
    have hXn0 : 0 ≤ X ^ n := zpow_nonneg (by linarith) n
    apply max_le
    · nlinarith
    · nlinarith
  have hcτβ : c * τ' * (1 + β) ≤ G := by
    rw [hG]; exact mul_le_mul_of_nonneg_right hcτ (by linarith)
  have hXTG : X ^ T ≤ G ^ T := pow_le_pow_left₀ (by linarith) hXG T
  calc y ≤ 1 + c * τ' * max (X ^ n) (β * X ^ n) := hy
    _ ≤ 1 + c * τ' * ((1 + β) * X ^ T) := by
        have : 0 ≤ c * τ' := by positivity
        nlinarith
    _ = 1 + (c * τ' * (1 + β)) * X ^ T := by ring
    _ ≤ 1 + G * G ^ T := by
        have : 0 ≤ c * τ' * (1 + β) := by positivity
        nlinarith
    _ ≤ 2 * G ^ (T + 1) := by
        have h5 : 1 ≤ G ^ T * G := by rw [← pow_succ]; exact one_le_pow₀ hG1
        rw [pow_succ, mul_comm G (G ^ T)]; linarith

lemma final_ineq1 (T : ℕ) (G : ℝ) (hG : 1 ≤ G) :
    ((T : ℝ) * G * (2 * G ^ (T + 1)) * G ^ T) * (1 + G * (G ^ T * G)) ≤
      (2 * (T : ℝ) + 1) ^ 2 * G ^ (3 * T + 4) := by
  have p1 : G ^ (2 * T + 2) ≤ G ^ (3 * T + 4) := pow_le_pow_right₀ hG (by omega)
  have p0 : 0 ≤ G ^ (3 * T + 4) := by positivity
  have hT : (0 : ℝ) ≤ T := by positivity
  calc ((T : ℝ) * G * (2 * G ^ (T + 1)) * G ^ T) * (1 + G * (G ^ T * G))
      = 2 * T * G ^ (2 * T + 2) + 2 * T * G ^ (3 * T + 4) := by ring
    _ ≤ 2 * T * G ^ (3 * T + 4) + 2 * T * G ^ (3 * T + 4) := by gcongr
    _ ≤ (2 * (T : ℝ) + 1) ^ 2 * G ^ (3 * T + 4) := by
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 4 * (T:ℝ) ^ 2 + 1) p0]

lemma final_ineq2 (T : ℕ) (G : ℝ) (hG : 1 ≤ G) :
    (1 + (T : ℝ) * G * (2 * G ^ (T + 1)) * T) + ((T : ℝ) * G * (2 * G ^ (T + 1)) * G ^ T) * G ≤
      (2 * (T : ℝ) + 1) ^ 2 * G ^ (3 * T + 4) := by
  have p1 : G ^ (T + 2) ≤ G ^ (3 * T + 4) := pow_le_pow_right₀ hG (by omega)
  have p2 : G ^ (2 * T + 3) ≤ G ^ (3 * T + 4) := pow_le_pow_right₀ hG (by omega)
  have p3 : 1 ≤ G ^ (3 * T + 4) := one_le_pow₀ hG
  have hT : (0 : ℝ) ≤ T := by positivity
  calc (1 + (T : ℝ) * G * (2 * G ^ (T + 1)) * T) + ((T : ℝ) * G * (2 * G ^ (T + 1)) * G ^ T) * G
      = 1 + 2 * T ^ 2 * G ^ (T + 2) + 2 * T * G ^ (2 * T + 3) := by ring
    _ ≤ G ^ (3 * T + 4) + 2 * T ^ 2 * G ^ (3 * T + 4) + 2 * T * G ^ (3 * T + 4) := by gcongr
    _ ≤ (2 * (T : ℝ) + 1) ^ 2 * G ^ (3 * T + 4) := by nlinarith

lemma tupNorm_grade_leZ {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} {e : Fin m → ℤ} (p : ∀ j, Hom (Y ⊕ Z) (e j)) (k : ℕ) :
    tupNorm (fun j => grade k (p j)) ≤ tupNorm p := by
  have := norm_tup_le_of (WithLp.toLp 2 (fun j => grade k (p j)) : Tup (Y ⊕ Z) e)
    (WithLp.toLp 2 p : Tup (Y ⊕ Z) e) 1 zero_le_one (fun j => by
      simpa using norm_grade_le k (p j))
  unfold tupNorm; simpa using this

lemma tauOf_nonneg' {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} {e : Fin m → ℤ}
    (p0 : ∀ i, Hom Y (e i)) (t : ℕ) : 0 ≤ tauOf p0 t :=
  Real.iSup_nonneg fun _ => pinvNorm_nonneg _

lemma G_facts (T : ℕ) (τ β : ℝ) (hτ : 0 ≤ τ) (hβ : 0 ≤ β) :
    1 + β ≤ (2 : ℝ) ^ T * (1 + τ) * (1 + β) ∧ 1 + τ ≤ (2 : ℝ) ^ T * (1 + τ) * (1 + β) := by
  have h2T : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  constructor
  · have : 1 ≤ (2 : ℝ) ^ T * (1 + τ) := by nlinarith
    nlinarith
  · have : 1 ≤ (2 : ℝ) ^ T * (1 + β) := by nlinarith
    nlinarith

lemma pi_nonneg (T : ℕ) (x0 x1 : ℝ) (h0 : 0 ≤ x0) (h1 : 0 ≤ x1) :
    0 ≤ (2 * (T : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ T * (1 + x0) * (1 + x1)) ^ (3 * T + 4) := by
  have : 0 ≤ (2 : ℝ) ^ T * (1 + x0) * (1 + x1) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  positivity

lemma eval_pi (K c x0 x1 : ℝ) (N : ℕ) :
    eval ![x0, x1] (C K * (C c * (1 + X 0) * (1 + X 1)) ^ N : MvPolynomial (Fin 2) ℝ) =
      K * (c * (1 + x0) * (1 + x1)) ^ N := by
  simp

section Bounds

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable {m : ℕ} (d D : Fin m → ℕ) (i : Fin m) (t : ℕ)

lemma PP_le (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) (x : Hom (Y ⊕ Z) (t : ℤ)) :
    ‖PP d D i t b x‖ ≤ ‖x‖ :=
  norm_Pproj_le t (d i * D i) (by push_cast; ring) _ x

lemma mulMap_grade_le (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) (k : ℕ)
    (x : Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)) :
    ‖mulMap (fun j => grade k (b j)) (t : ℤ) x‖ ≤ tupNorm b * ‖x‖ :=
  (norm_mulMap_leZ (modDeg_nonneg d D i) _ _ x).trans
    (mul_le_mul_of_nonneg_right (tupNorm_grade_leZ b _) (norm_nonneg _))

lemma AA_bound
    (H : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      (Tup Y (fun j => (t : ℤ) - modDeg d D i j) →L[ℝ] Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) (hD : 1 ≤ D i) {T : ℕ} (hRT : d i * D i ≤ T)
    (G M : ℝ) (hG0 : 0 ≤ G) (hM0 : 0 ≤ M) (hβG : tupNorm b ≤ G)
    (hGT : (1 + tupNorm b) ^ (D i - 1) ≤ G ^ T) (hH : ∀ s, s < d i * D i → ‖H s b‖ ≤ M)
    (w : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))) :
    ‖AA d D i t H b w‖ ≤ (T : ℝ) * G * M * G ^ T * ‖w‖ := by
  rw [AA, LinearMap.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hw0 := norm_nonneg w
  have hterm : ∀ s ∈ Finset.range (d i * D i),
      ‖(PP d D i t b ∘ₗ mulMap (fun j => grade (d i * D i - s) (b j)) (t : ℤ) ∘ₗ
          (H s b).toLinearMap ∘ₗ tildeL d D i t b) w‖ ≤ G * M * G ^ T * ‖w‖ := by
    intro s hs
    rw [Finset.mem_range] at hs
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    have h1 := hH s hs
    have h2 := norm_tildeL_le d D i hD t b w
    have h3 := (H s b).le_opNorm (tildeL d D i t b w)
    have h4 := PP_le d D i t b (mulMap (fun j => grade (d i * D i - s) (b j)) (t : ℤ)
      (H s b (tildeL d D i t b w)))
    have h5 := mulMap_grade_le d D i t b (d i * D i - s) (H s b (tildeL d D i t b w))
    have hT0 := norm_nonneg (tildeL d D i t b w)
    have h6 : ‖tildeL d D i t b w‖ ≤ G ^ T * ‖w‖ := h2.trans (mul_le_mul_of_nonneg_right hGT hw0)
    have h7 : ‖H s b (tildeL d D i t b w)‖ ≤ M * (G ^ T * ‖w‖) :=
      h3.trans (mul_le_mul h1 h6 hT0 hM0)
    calc _ ≤ tupNorm b * ‖H s b (tildeL d D i t b w)‖ := h4.trans h5
      _ ≤ G * (M * (G ^ T * ‖w‖)) := mul_le_mul hβG h7 (norm_nonneg _) hG0
      _ = G * M * G ^ T * ‖w‖ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : ((d i * D i : ℕ) : ℝ) ≤ T := by exact_mod_cast hRT
  have h2 : 0 ≤ G * M * G ^ T * ‖w‖ := by positivity
  calc ((d i * D i : ℕ) : ℝ) * (G * M * G ^ T * ‖w‖) ≤ (T : ℝ) * (G * M * G ^ T * ‖w‖) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

lemma BB_bound
    (F : (r : ℕ) → (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
      ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
        Tup (Y ⊕ Z) (fun j => (t : ℤ) - modDeg d D i j)))
    (b : ∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) {T : ℕ} (hRT : d i * D i ≤ T)
    (G M : ℝ) (hG0 : 0 ≤ G) (hM0 : 0 ≤ M) (hβG : tupNorm b ≤ G)
    (hF : ∀ s, s < d i * D i → ‖F s b‖ ≤ M) (f : Hom (Y ⊕ Z) (t : ℤ)) :
    ‖BB d D i t F b f‖ ≤ (1 + (T : ℝ) * G * M * T) * ‖f‖ := by
  rw [BB]
  refine (norm_sub_le _ _).trans ?_
  have hf0 := norm_nonneg f
  have hterm : ∀ s ∈ Finset.range (d i * D i),
      ‖PP d D i t b (mulMap (fun j => grade (d i * D i - s) (b j)) (t : ℤ)
        (F s b (gradeSeg s f)))‖ ≤ G * M * T * ‖f‖ := by
    intro s hs
    rw [Finset.mem_range] at hs
    have h1 := hF s hs
    have h2 := norm_gradeSeg_le s f
    have h3 := (F s b).le_opNorm (gradeSeg s f)
    have h4 := PP_le d D i t b (mulMap (fun j => grade (d i * D i - s) (b j)) (t : ℤ)
      (F s b (gradeSeg s f)))
    have h5 := mulMap_grade_le d D i t b (d i * D i - s) (F s b (gradeSeg s f))
    have hsT : (s : ℝ) + 1 ≤ T := by
      have : s + 1 ≤ T := by omega
      exact_mod_cast this
    have h6 : ‖gradeSeg s f‖ ≤ T * ‖f‖ := h2.trans (mul_le_mul_of_nonneg_right hsT hf0)
    have h7 : ‖F s b (gradeSeg s f)‖ ≤ M * (T * ‖f‖) :=
      h3.trans (mul_le_mul h1 h6 (norm_nonneg _) hM0)
    calc _ ≤ tupNorm b * ‖F s b (gradeSeg s f)‖ := h4.trans h5
      _ ≤ G * (M * (T * ‖f‖)) := mul_le_mul hβG h7 (norm_nonneg _) hG0
      _ = G * M * T * ‖f‖ := by ring
  have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have h1 : ((d i * D i : ℕ) : ℝ) ≤ T := by exact_mod_cast hRT
  have h2 : 0 ≤ G * M * T * ‖f‖ := by positivity
  have h3 : ((d i * D i : ℕ) : ℝ) * (G * M * T * ‖f‖) ≤ (T : ℝ) * (G * M * T * ‖f‖) :=
    mul_le_mul_of_nonneg_right h1 h2
  calc ‖PP d D i t b f‖ + ‖∑ s ∈ Finset.range (d i * D i), PP d D i t b (mulMap
        (fun j => grade (d i * D i - s) (b j)) (t : ℤ) (F s b (gradeSeg s f)))‖
      ≤ ‖f‖ + (T : ℝ) * (G * M * T * ‖f‖) :=
        add_le_add (PP_le d D i t b f) (hs.trans h3)
    _ = _ := by ring

end Bounds

end ApproxSyzygies.Smoothed.Dev.L44

namespace ApproxSyzygies.Smoothed

open ApproxSyzygies.Smoothed.Dev.L44 ApproxSyzygies.Smoothed.Dev.L43 in
theorem chk_lemma_4_4 (T : ℕ) :
    ∃ π : MvPolynomial (Fin 2) ℝ,
      ∀ {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}
        (d D : Fin m → ℕ), (∀ j, 1 ≤ d j) → (∀ j, 1 ≤ D j) →
        ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ i : Fin m,
        ∃ Cmap : (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
            (Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →L[ℝ] Hom (Y ⊕ Z) (t : ℤ)),
        ∀ (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ)),
          KernelCond (yParts fun j => powHom (a j) (D j)) t →
          KernelCond (yParts (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)) t →
          ‖Cmap (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)‖ ≤
              eval ![max (tauOf (yParts fun j => powHom (a j) (D j)) t)
                      (tauOf (yParts (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)) t),
                    tupNorm (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)] π ∧
            ∀ h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)),
              ‖ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
                    toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) +
                  Cmap (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)
                    (gVec d D t (yParts a) (yPartTup h))‖ ≤
                eval ![max (tauOf (yParts fun j => powHom (a j) (D j)) t)
                        (tauOf (yParts (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)) t),
                      tupNorm (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)] π *
                  ‖mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h‖ := by
  refine ⟨C ((2 * (T : ℝ) + 1) ^ 2) * (C ((2 : ℝ) ^ T) * (1 + X 0) * (1 + X 1)) ^ (3 * T + 4), ?_⟩
  intro Y Z _ _ _ _ m d D hd hD t ht1 htT i
  simp only [eval_pi]
  by_cases hRt : d i * D i ≤ t
  swap
  · -- `R > t`: `g_i = 0`
    refine ⟨fun _ => 0, ?_⟩
    intro a v _ _
    refine ⟨norm_zero.trans_le (pi_nonneg T _ _ (le_max_of_le_left (tauOf_nonneg' _ t))
      (tupNorm_nonneg' _)), fun h => ?_⟩
    have hneg : (t : ℤ) - (d i : ℤ) * (D i : ℤ) < 0 := by
      have : t < d i * D i := not_le.1 hRt
      have : (t : ℤ) < ((d i * D i : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at this; linarith
    rw [hom_eq_zero_of_neg hneg (gVec d D t (yParts a) (yPartTup h) i), toPoly_liftY, toPoly_zero,
      map_zero, mul_zero, ofPoly_zero', zero_apply, add_zero, norm_zero]
    exact mul_nonneg (pi_nonneg T _ _ (le_max_of_le_left (tauOf_nonneg' _ t))
      (tupNorm_nonneg' _)) (norm_nonneg _)
  -- main case `1 ≤ R ≤ t`
  set R := d i * D i with hR
  have hR1 : 1 ≤ R := by
    have := Nat.mul_le_mul (hd i) (hD i); simpa using this
  have hRT : R ≤ T := le_trans hRt htT
  have hDR : D i ≤ R := Nat.le_mul_of_pos_left _ (hd i)
  obtain ⟨L₁, L₂, hL⟩ := ApproxSyzygies.Smoothed.lemma_4_2 (Y := Y) d D hd hD t ht1
  set e : Fin m → ℕ := fun j => if j = i then d j else d j * D j with he_def
  have hee : modDeg d D i = fun j => (e j : ℤ) := by
    funext j; simp only [modDeg, he_def]; split_ifs <;> push_cast <;> rfl
  have he : ∀ j, 1 ≤ e j := by
    intro j; simp only [he_def]; split_ifs
    · exact hd j
    · have := Nat.mul_le_mul (hd j) (hD j); simpa using this
  obtain ⟨F, H, hFH⟩ := l43' T (Y := Y) (Z := Z) e (modDeg d D i) hee he t htT (R - 1) (by omega)
  refine ⟨fun b => LinearMap.toContinuousLinearMap
    (AA d D i t H b ∘ₗ (L₁ (b0fun d D i b)).toLinearMap), ?_⟩
  intro a v hK1 hK2
  rw [show modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a = btil d D i a v from rfl]
    at hK2 ⊢
  simp only [b0fun_btil d D i a v (hd i)]
  set b := btil d D i a v with hb
  set pw : ∀ j, Hom (Y ⊕ Z) ((d j : ℤ) * (D j : ℤ)) := fun j => powHom (a j) (D j) with hpw
  obtain ⟨hFHb, hid⟩ := hFH b hK2
  have hK1' : (LinearMap.ker (mulMap (yParts pw) ((t : ℤ) - 1)) :
      Set (Tup Y (fun i => (t : ℤ) - 1 - (d i : ℤ) * (D i : ℤ)))) = koszul (yParts pw) ((t : ℤ) - 1) := by
    have := hK1 (t - 1) (by omega)
    have e1 : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
    rw [e1] at this
    exact this
  obtain ⟨hL1, hL2, hLh⟩ := hL Z a hK1'
  -- the constants
  set τb := tauOf (yParts pw) t with hτb
  set τt := tauOf (yParts b) t with hτt
  set τ := max τb τt with hτ
  set β := tupNorm b with hβ
  set G := (2 : ℝ) ^ T * (1 + τ) * (1 + β) with hG
  have hτb0 : 0 ≤ τb := tauOf_nonneg' _ t
  have hτt0 : 0 ≤ τt := tauOf_nonneg' _ t
  have hτ0 : 0 ≤ τ := le_max_of_le_left hτb0
  have hβ0 : 0 ≤ β := tupNorm_nonneg' b
  have h2T : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  obtain ⟨hβG, hτG⟩ := G_facts T τ β hτ0 hβ0
  have hG1 : 1 ≤ G := by linarith only [hβG, hβ0]
  have hG0 : 0 ≤ G := by linarith only [hG1]
  set M := 2 * G ^ (T + 1) with hM
  have hFb : ∀ s, s ≤ R - 1 → ‖F s b‖ ≤ M ∧ ‖H s b‖ ≤ M := by
    intro s hs
    obtain ⟨h1, h2⟩ := hFHb s hs
    have hn : (((R - 1 : ℕ) : ℤ) - 1) ≤ (T : ℤ) := by omega
    exact ⟨bound43 T τt τ β _ hτt0 (le_max_right _ _) hβ0 _ hn h1,
      bound43 T τt τ β _ hτt0 (le_max_right _ _) hβ0 _ hn h2⟩
  have hGT : (1 + β) ^ (D i - 1) ≤ G ^ T :=
    (pow_le_pow_left₀ (by linarith only [hβ0]) hβG _).trans (pow_le_pow_right₀ hG1 (by omega))
  set CA := (T : ℝ) * G * M * G ^ T with hCA
  have hM0 : 0 ≤ M := mul_nonneg zero_le_two (pow_nonneg hG0 _)
  have hβG' : β ≤ G := by linarith only [hβG]
  have hA : ∀ w, ‖AA d D i t H b w‖ ≤ CA * ‖w‖ := fun w =>
    AA_bound d D i t H b (hD i) hRT G M hG0 hM0 hβG' hGT (fun s hs => (hFb s (by omega)).2) w
  set CB := 1 + (T : ℝ) * G * M * T with hCB
  have hB : ∀ f, ‖BB d D i t F b f‖ ≤ CB * ‖f‖ := fun f =>
    BB_bound d D i t F b hRT G M hG0 hM0 hβG' (fun s hs => (hFb s (by omega)).1) f
  have hb0 : tupNorm (yParts pw) ≤ G ^ T * G := by
    rw [← b0fun_btil d D i a v (hd i)]
    refine (norm_b0fun_le d D i (hD i) b).trans ?_
    exact mul_le_mul hGT (by linarith only [hβG]) hβ0 (pow_nonneg hG0 _)
  have hL1' : ‖L₁ (yParts pw)‖ ≤ 1 + G * (G ^ T * G) := by
    refine hL1.trans ?_
    have h1 : τb ≤ G := (le_max_left _ _).trans (by linarith only [hτG])
    have h2 : 0 ≤ tupNorm (yParts pw) := tupNorm_nonneg' _
    exact (add_le_add_iff_left 1).2 (mul_le_mul h1 hb0 h2 hG0)
  have hL2' : ‖L₂ (yParts pw)‖ ≤ G := hL2.trans ((le_max_left _ _).trans (by linarith only [hτG]))
  have hCA0 : 0 ≤ CA :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg T) hG0) hM0) (pow_nonneg hG0 _)
  refine ⟨?_, fun h => ?_⟩
  · -- the operator norm of `C_i`
    refine ContinuousLinearMap.opNorm_le_bound _ (pi_nonneg T _ _ hτ0 hβ0) fun x => ?_
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe]
    refine (hA _).trans ?_
    have h1 := (L₁ (yParts pw)).le_opNorm x
    calc CA * ‖L₁ (yParts pw) x‖ ≤ CA * ((1 + G * (G ^ T * G)) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right hL1' (norm_nonneg _))) hCA0
      _ = (CA * (1 + G * (G ^ T * G))) * ‖x‖ := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [hCA, hM]; exact final_ineq1 T G hG1
  · -- the main estimate
    obtain ⟨k₀, hk₀, hdec⟩ := hLh h
    have h16 := eq16 d D i t a v (hd i) (hD i) F H hid h
    have hk := AA_koszul d D i t a v (hd i) (hD i) F H hid k₀ hk₀
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe]
    set f := mulMap pw (t : ℤ) h with hf
    set g := gVec d D t (yParts a) (yPartTup h) with hg
    set Vt := ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
        toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) with hVt
    have key : Vt + AA d D i t H b (L₁ (yParts pw) g) =
        BB d D i t F b f - AA d D i t H b (L₂ (yParts pw) (yPart f)) := by
      rw [← h16, hdec, map_add, map_add, hk]; abel
    rw [key]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hB f
    have h2 := hA (L₂ (yParts pw) (yPart f))
    have h3 := (L₂ (yParts pw)).le_opNorm (yPart f)
    have h4 : ‖yPart f‖ ≤ ‖f‖ := norm_yPart_le f
    have hf0 := norm_nonneg f
    calc ‖BB d D i t F b f‖ + ‖AA d D i t H b (L₂ (yParts pw) (yPart f))‖
        ≤ CB * ‖f‖ + CA * (G * ‖f‖) := by
          refine add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left ?_ hCA0))
          exact h3.trans (mul_le_mul hL2' h4 (norm_nonneg _) hG0)
      _ = (CB + CA * G) * ‖f‖ := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hf0
          rw [hCB, hCA, hM]; exact final_ineq2 T G hG1

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_lemma_4_4 := @ApproxSyzygies.Smoothed.chk_lemma_4_4
