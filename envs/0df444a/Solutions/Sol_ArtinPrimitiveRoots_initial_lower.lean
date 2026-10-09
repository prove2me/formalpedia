-- Prove2me | solution 1 for ArtinPrimitiveRoots.initial_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:16.983573+00:00
-- url     : https://prove2.me/submissions/78170e94-3d2f-43e7-a994-90c41fc2b4b1

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_block_sieve
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution

namespace ArtinPrimitiveRoots.P21initial_lower

open Real Filter Topology MeasureTheory

theorem singularSeries_pos (M : ℕ) : 0 < singularSeries M := by
  unfold singularSeries
  have hp3 : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, (3 : ℝ) ≤ p.1 := fun p => by
    exact_mod_cast p.2.2
  have hg : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    apply Summable.neg
    have hs : Summable (fun n : ℕ => 9 / 4 * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
    have hs' := hs.comp_injective (Subtype.val_injective (p := fun p : ℕ => p.Prime ∧ 2 < p))
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hs'
    · have := hp3 p
      positivity
    · have h3 := hp3 p
      simp only [Function.comp]
      rw [div_le_iff₀ (by nlinarith)]
      field_simp
      nlinarith
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, 0 < 1 + -(1 / ((p.1 : ℝ) - 1) ^ 2) := by
    intro p
    have h3 := hp3 p
    have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    linarith
  have hprod : 0 < ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    have := Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable hg)
    simp only [← sub_eq_add_neg] at this
    rw [← this]
    exact Real.exp_pos _
  apply mul_pos (mul_pos two_pos hprod)
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
  apply inv_pos.mpr
  have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma prod_ordProj_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h : ℕ) :
    (∏ p ∈ s, p ^ h.factorization p) ∣ h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq]
    have hq' : q.Prime := hs q (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (Nat.ordProj_dvd h q) ih'
    apply Nat.Coprime.prod_right
    intro p hp
    have hp' : p.Prime := hs p (Finset.mem_insert_of_mem hp)
    exact Nat.coprime_pow_primes _ _ hq' hp' (fun e => hq (e ▸ hp))

lemma groupPrimes_prime (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∀ p ∈ groupPrimes x a, p.Prime := by
  intro p hp
  simp only [groupPrimes, primeGroup, Finset.mem_biUnion, Finset.mem_filter] at hp
  obtain ⟨i, -, -, h, -⟩ := hp
  exact h

lemma groupPart_dvd (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : groupPart x a h ∣ h :=
  prod_ordProj_dvd _ (groupPrimes_prime x a) h

lemma groupPart_pos (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 < groupPart x a h := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (groupPrimes_prime x a p hp).pos _

lemma mem_groupPrimes_of_mem_primeFactors (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h ℓ : ℕ)
    (hℓ : ℓ ∈ (groupPart x a h).primeFactors) : ℓ ∈ groupPrimes x a := by
  rw [Nat.mem_primeFactors] at hℓ
  obtain ⟨hℓp, hdvd, -⟩ := hℓ
  unfold groupPart at hdvd
  obtain ⟨p, hp, hdp⟩ := (Prime.dvd_finsetProd_iff hℓp.prime _).mp hdvd
  have hp' := groupPrimes_prime x a p hp
  have := (Nat.prime_dvd_prime_iff_eq hℓp hp').mp (hℓp.dvd_of_dvd_pow hdp)
  rw [this]; exact hp

lemma groupReciprocalSum_nonneg (x a : ℝ) : 0 ≤ groupReciprocalSum x a := by
  unfold groupReciprocalSum
  apply Finset.sum_nonneg
  intro p _
  positivity

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 ≤ mark (1 / 2) x a h := by
  unfold mark
  apply mul_nonneg (zpow_nonneg (by norm_num) _)
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (groupReciprocalSum_nonneg _ _)

lemma predecessorIndicator_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) :
    0 ≤ predecessorIndicator x a c h := by
  unfold predecessorIndicator; split_ifs <;> norm_num

lemma constructionWeight_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ)
    {K : ℕ} (a : Fin K → ℝ) (d : ℕ) : 0 ≤ constructionWeight M c u Ψ x a d := by
  unfold constructionWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (hΨ0 _) (predecessorIndicator_nonneg _ _ _ _))
      (mark_nonneg _ _ _)
  · exact le_rfl

lemma constructionWeight_support (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (d : ℕ)
    (hd : constructionWeight M c u Ψ x a d ≠ 0) :
    2 ≤ d ∧ (d : ℤ) ≡ u [ZMOD M] ∧ x < d ∧ (d : ℝ) < 2 * x ∧
      ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ (d - 1) / groupPart x a (d - 1) = c * Q := by
  unfold constructionWeight at hd
  split_ifs at hd with h
  · refine ⟨h.1, h.2, ?_⟩
    have hΨ : Ψ (d / x) ≠ 0 := fun e => hd (by rw [e]; ring)
    have hF : predecessorIndicator x a c (d - 1) ≠ 0 := fun e => hd (by rw [e]; ring)
    have hmem := hΨs (subset_tsupport _ hΨ)
    rw [Set.mem_Ioo, lt_div_iff₀ hx, div_lt_iff₀ hx] at hmem
    refine ⟨by linarith [hmem.1], by linarith [hmem.2], ?_⟩
    unfold predecessorIndicator at hF
    split_ifs at hF with hQ
    · exact hQ
    · exact absurd rfl hF
  · exact absurd rfl hd

lemma weight_eq_zero_of_ge (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (d : ℕ) (hd : ⌈2 * x⌉₊ ≤ d) :
    constructionWeight M c u Ψ x a d = 0 := by
  by_contra hne
  have := (constructionWeight_support M c u Ψ hΨs x hx a d hne).2.2.2.1
  have h2 : (⌈2 * x⌉₊ : ℝ) ≤ d := by exact_mod_cast hd
  have h3 := Nat.le_ceil (2 * x)
  linarith

lemma summable_weight (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun d : ℕ => if P d then constructionWeight M c u Ψ x a d else 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊)
  intro d hd
  simp only [Finset.mem_range, not_lt] at hd
  rw [weight_eq_zero_of_ge M c u Ψ hΨs x hx a d hd]
  simp

lemma totalMass_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) : 0 ≤ totalMass M c u Ψ x a :=
  tsum_nonneg fun d => constructionWeight_nonneg M c u Ψ hΨ0 x a d

lemma mertensProduct_pos (y : ℝ) : 0 < mertensProduct y := by
  unfold mertensProduct
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter] at hp
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma primeGroup_subset (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (i : Fin K) :
    primeGroup x (a i) ⊆ groupPrimes x a := by
  intro p hp
  simp only [groupPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hp⟩

lemma not_dvd_c_of_gt_two (c p : ℕ) (hc : c = 2 ∨ c = 4) (hp : p.Prime) (hp2 : 2 < p) :
    ¬ p ∣ c := by
  intro h
  have h2 : p ∣ 2 := by
    rcases hc with rfl | rfl
    · exact h
    · exact hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h)
  have := Nat.le_of_dvd (by norm_num) h2
  omega

lemma dvd_crQ_iff (c r Q p : ℕ) (hc : c = 2 ∨ c = 4) (hp : p.Prime) (hp2 : 2 < p)
    (hQ : Q.Prime) (hpQ : p ≠ Q) : p ∣ c * r * Q ↔ p ∣ r := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact absurd h2 (not_dvd_c_of_gt_two c p hc hp hp2)
      · exact h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hQ).mp h1) hpQ
  · intro h
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h c) Q

/-- Hypothesis on the scale: group primes exceed `2` and lie below `x^{0.9}`. -/
def GroupPrimesSmall (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : Prop :=
  ∀ p ∈ groupPrimes x a, 2 < p ∧ (p : ℝ) < x ^ (0.9 : ℝ)

lemma groupPart_crQ (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (hG : GroupPrimesSmall x a)
    (c r Q : ℕ) (hc : c = 2 ∨ c = 4) (hr : IsGroupInteger x a r) (hQ : Q.Prime)
    (hQx : x ^ (0.9 : ℝ) < Q) : groupPart x a (c * r * Q) = r := by
  have hr0 : r ≠ 0 := hr.1.ne'
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  unfold groupPart
  have hfac : ∀ p ∈ groupPrimes x a, (c * r * Q).factorization p = r.factorization p := by
    intro p hp
    have hpp := groupPrimes_prime x a p hp
    obtain ⟨hp2, hpx⟩ := hG p hp
    have hpQ : p ≠ Q := by
      intro h; rw [h] at hpx; linarith
    rw [Nat.factorization_mul (mul_ne_zero hc0 hr0) hQ.ne_zero,
      Nat.factorization_mul hc0 hr0]
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd (not_dvd_c_of_gt_two c p hc hpp hp2),
      hQ.factorization, Finsupp.single_apply, if_neg (Ne.symm hpQ)]
    ring
  rw [Finset.prod_congr rfl (fun p hp => by rw [hfac p hp])]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hr0]
  symm
  apply Finset.prod_subset hr.2
  intro p _ hp
  rw [Nat.factorization_eq_zero_of_not_dvd, pow_zero]
  intro hd
  exact hp (Nat.mem_primeFactors.mpr ⟨groupPrimes_prime x a p (by assumption), hd, hr0⟩)

lemma mark_crQ (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (hG : GroupPrimesSmall x a)
    (c r Q : ℕ) (hc : c = 2 ∨ c = 4) (hQ : Q.Prime) (hQx : x ^ (0.9 : ℝ) < Q) :
    mark (1 / 2) x a (c * r * Q) = mark (1 / 2) x a r := by
  have hω : ∀ i, groupOmega x (a i) (c * r * Q) = groupOmega x (a i) r := by
    intro i
    unfold groupOmega
    congr 1
    apply Finset.filter_congr
    intro p hp
    have hpG := primeGroup_subset x a i hp
    have hpp := groupPrimes_prime x a p hpG
    obtain ⟨hp2, hpx⟩ := hG p hpG
    have hpQ : p ≠ Q := by
      intro h; rw [h] at hpx; linarith
    exact dvd_crQ_iff c r Q p hc hpp hp2 hQ hpQ
  unfold mark markOmega
  simp only [hω]

/-- The structure of a supported `d`. -/
lemma support_structure (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (hG : GroupPrimesSmall x a)
    (hc : c = 2 ∨ c = 4) (d : ℕ) (hd : constructionWeight M c u Ψ x a d ≠ 0) :
    IsGroupInteger x a (groupPart x a (d - 1)) ∧
      ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ d = c * groupPart x a (d - 1) * Q + 1 ∧
      (d : ℤ) ≡ u [ZMOD M] ∧
      constructionWeight M c u Ψ x a d = Ψ (d / x) * mark (1 / 2) x a (groupPart x a (d - 1)) := by
  obtain ⟨hd2, hdu, -, -, Q, hQ, hQx, hdiv⟩ := constructionWeight_support M c u Ψ hΨs x hx a d hd
  set r := groupPart x a (d - 1) with hr
  have hgi : IsGroupInteger x a r :=
    ⟨groupPart_pos x a (d - 1), fun p hp => mem_groupPrimes_of_mem_primeFactors x a _ p hp⟩
  have hd1 : d - 1 = c * r * Q := by
    have := Nat.div_mul_cancel (groupPart_dvd x a (d - 1))
    rw [hdiv] at this
    exact this.symm.trans (by ring)
  refine ⟨hgi, Q, hQ, hQx, by omega, hdu, ?_⟩
  unfold constructionWeight
  rw [if_pos ⟨hd2, hdu⟩]
  have hF : predecessorIndicator x a c (d - 1) = 1 := by
    unfold predecessorIndicator
    rw [if_pos ⟨Q, hQ, hQx, hdiv⟩]
  rw [hF, hd1, mark_crQ x a hG c r Q hc hQ hQx]
  ring

open Classical in
lemma predecessorMassDvd_eq_sum (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) (r ℓ : ℕ) (hc : 1 ≤ c) (hr : 1 ≤ r) :
    predecessorMassDvd M c u Ψ x r ℓ =
      ∑ Q ∈ Finset.range ⌈2 * x⌉₊, (if Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
        ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1 then
          Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) := by
  unfold predecessorMassDvd
  refine (tsum_subtype (s := {Q : ℕ | Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1})
    (f := fun Q : ℕ => Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x))).trans ?_
  rw [tsum_eq_sum (s := Finset.range ⌈2 * x⌉₊)]
  · apply Finset.sum_congr rfl
    intro Q _
    simp only [Set.indicator, Set.mem_setOf_eq]
  · intro Q hQ
    simp only [Finset.mem_range, not_lt] at hQ
    simp only [Set.indicator]
    split_ifs
    · apply Function.notMem_support.mp
      intro hs
      have hmem := hΨs (subset_tsupport _ hs)
      have h1 : (2 * x) ≤ (Q : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hQ)
      have h2 : (Q : ℝ) ≤ c * r * Q := by
        have : 1 ≤ c * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have : Q ≤ c * r * Q := Nat.le_mul_of_pos_left Q (by omega)
        exact_mod_cast this
      have h3 : ((c * r * Q + 1 : ℕ) : ℝ) / x ≥ 2 := by
        rw [ge_iff_le, le_div_iff₀ hx]; push_cast; push_cast at h2; linarith
      linarith [hmem.2]
    · rfl

lemma predecessorMass_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ)
    (r : ℕ) : 0 ≤ predecessorMass M c u Ψ x r :=
  tsum_nonneg fun Q => hΨ0 _

open Classical in
/-- Grouping supported `d` by `r = (d-1)_𝒫`: `∑_{d} w(d) ≤ ∑_r 𝒲(r) A_r`. -/
lemma sum_weight_le_marks (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ)
    (hG : GroupPrimesSmall x a) (hc : c = 2 ∨ c = 4) (Dset T : Finset ℕ)
    (hD : ∀ d ∈ Dset, constructionWeight M c u Ψ x a d ≠ 0)
    (hT : ∀ d ∈ Dset, groupPart x a (d - 1) ∈ T) :
    ∑ d ∈ Dset, constructionWeight M c u Ψ x a d ≤
      ∑ r ∈ T, mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  rw [← Finset.sum_fiberwise_of_maps_to hT]
  apply Finset.sum_le_sum
  intro r _
  set F := Dset.filter (fun d => groupPart x a (d - 1) = r) with hF
  by_cases hFne : F.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hFne, Finset.sum_empty]
    exact mul_nonneg (mark_nonneg _ _ _) (predecessorMass_nonneg M c u Ψ hΨ0 x r)
  obtain ⟨d₀, hd₀⟩ := hFne
  have hr1 : 1 ≤ r := by
    rw [hF, Finset.mem_filter] at hd₀
    rw [← hd₀.2]; exact groupPart_pos x a _
  have hstr : ∀ d ∈ F, ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ d = c * r * Q + 1 ∧
      (d : ℤ) ≡ u [ZMOD M] ∧
      constructionWeight M c u Ψ x a d = Ψ (d / x) * mark (1 / 2) x a r := by
    intro d hd
    rw [hF, Finset.mem_filter] at hd
    obtain ⟨-, Q, h1, h2, h3, h4, h5⟩ := support_structure M c u Ψ hΨs x hx a hG hc d (hD d hd.1)
    rw [hd.2] at h3 h5
    exact ⟨Q, h1, h2, h3, h4, h5⟩
  set q : ℕ → ℕ := fun d => (d - 1) / (c * r) with hq
  have hcr : 0 < c * r := by positivity
  have hqd : ∀ d ∈ F, d = c * r * q d + 1 := by
    intro d hd
    obtain ⟨Q, -, -, h3, -⟩ := hstr d hd
    have : q d = Q := by
      simp only [hq]; rw [h3, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hcr]
    rw [this]; exact h3
  have hinj : Set.InjOn q (F : Set ℕ) := by
    intro d₁ h₁ d₂ h₂ h
    rw [hqd d₁ h₁, hqd d₂ h₂, h]
  rw [predecessorMass, predecessorMassDvd_eq_sum M c u Ψ hΨs x hx r 1 hc1 hr1]
  calc ∑ d ∈ F, constructionWeight M c u Ψ x a d
      = mark (1 / 2) x a r * ∑ d ∈ F, Ψ (d / x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨Q, -, -, -, -, h5⟩ := hstr d hd
        rw [h5]; ring
    _ ≤ mark (1 / 2) x a r * ∑ Q ∈ Finset.range ⌈2 * x⌉₊, (if Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
        ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ 1 ∣ c * r * Q + 1 then
          Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) := by
        apply mul_le_mul_of_nonneg_left _ (mark_nonneg _ _ _)
        calc ∑ d ∈ F, Ψ (d / x) = ∑ Q ∈ F.image q, (if Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
              ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ 1 ∣ c * r * Q + 1 then
                Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) := by
              rw [Finset.sum_image hinj]
              apply Finset.sum_congr rfl
              intro d hd
              obtain ⟨Q, h1, h2, h3, h4, -⟩ := hstr d hd
              have hqQ : q d = Q := by
                simp only [hq]; rw [h3, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hcr]
              rw [hqQ, ← h3, if_pos ⟨h1, h2, h4, one_dvd _⟩]
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro Q hQ
                rw [Finset.mem_image] at hQ
                obtain ⟨d, hd, rfl⟩ := hQ
                rw [Finset.mem_range]
                have hw := hD d (Finset.mem_filter.mp hd).1
                have h2x := (constructionWeight_support M c u Ψ hΨs x hx a d hw).2.2.2.1
                have hle : q d < d := by
                  have := hqd d hd
                  have : q d ≤ c * r * q d := Nat.le_mul_of_pos_left _ hcr
                  omega
                have : (d : ℝ) < ⌈2 * x⌉₊ := lt_of_lt_of_le h2x (Nat.le_ceil _)
                have : d < ⌈2 * x⌉₊ := by exact_mod_cast this
                omega
              · intro Q _ _
                split_ifs
                · exact hΨ0 _
                · exact le_rfl

lemma weight_crQ (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (hG : GroupPrimesSmall x a) (hc : c = 2 ∨ c = 4) (r Q : ℕ) (hr : IsGroupInteger x a r)
    (hQ : Q.Prime) (hQx : x ^ (0.9 : ℝ) < Q) (hu : ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) :
    constructionWeight M c u Ψ x a (c * r * Q + 1) =
      mark (1 / 2) x a r * Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) := by
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have hpos : 1 ≤ c * r * Q := Nat.one_le_iff_ne_zero.mpr
    (by have := hr.1; have := hQ.pos; positivity)
  unfold constructionWeight
  rw [if_pos ⟨by omega, hu⟩]
  simp only [Nat.add_sub_cancel]
  have hF : predecessorIndicator x a c (c * r * Q) = 1 := by
    unfold predecessorIndicator
    rw [if_pos]
    refine ⟨Q, hQ, hQx, ?_⟩
    rw [groupPart_crQ x a hG c r Q hc hr hQ hQx,
      show c * r * Q = r * (c * Q) by ring, Nat.mul_div_cancel_left _ hr.1]
  rw [hF, mark_crQ x a hG c r Q hc hQ hQx]
  push_cast
  ring

lemma isRough_crQ (x b : ℝ) (c r Q : ℕ) (hc : c = 2 ∨ c = 4) (Pset : Finset ℕ)
    (hP : ∀ p : ℕ, p.Prime → 2 < p → (p : ℝ) ≤ x ^ b → p ∈ Pset)
    (h : ∀ p ∈ Pset, ¬ p ∣ c * r * Q + 1) (hxb : 0 ≤ x ^ b) :
    IsRough (x ^ b) (c * r * Q + 1) := by
  refine ⟨by omega, fun p hp => ?_⟩
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_ge 2 p with h2 | h2
  · exact h p (hP p hpp h2 hle) hpd
  · have hp2 : p = 2 := le_antisymm h2 hpp.two_le
    subst hp2
    have : 2 ∣ c * r * Q := by
      rcases hc with rfl | rfl
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl 2) r) Q
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by norm_num : 2 ∣ 4) r) Q
    omega

open Classical in
/-- The sieved masses at small `r` are part of `S_b` (§12.3). -/
lemma sieved_le_Sb (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ)
    (hG : GroupPrimesSmall x a) (hc : c = 2 ∨ c = 4) (b : ℝ) (Rset Pset : Finset ℕ)
    (hR : ∀ r ∈ Rset, IsGroupInteger x a r)
    (hP : ∀ p : ℕ, p.Prime → 2 < p → (p : ℝ) ≤ x ^ b → p ∈ Pset) :
    ∑ r ∈ Rset, mark (1 / 2) x a r *
        ∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ Pset, ¬ p ∣ c * r * Q + 1),
          Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) ≤
      ∑' d : ℕ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) := by
  set N := ⌈2 * x⌉₊
  set pred : ℕ → ℕ → Prop := fun r Q => (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧ ∀ p ∈ Pset, ¬ p ∣ c * r * Q + 1 with hpred
  set S := (Rset ×ˢ Finset.range N).filter (fun rq => pred rq.1 rq.2) with hS
  set φ : ℕ × ℕ → ℕ := fun rq => c * rq.1 * rq.2 + 1 with hφ
  have hc0 : 0 < c := by rcases hc with rfl | rfl <;> norm_num
  have hinj : Set.InjOn φ (S : Set (ℕ × ℕ)) := by
    intro p₁ h₁ p₂ h₂ h
    simp only [hS, Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at h₁ h₂
    simp only [hφ] at h
    have e : c * p₁.1 * p₁.2 = c * p₂.1 * p₂.2 := by omega
    have hr : p₁.1 = p₂.1 := by
      rw [← groupPart_crQ x a hG c p₁.1 p₁.2 hc (hR _ h₁.1.1) h₁.2.1.1 h₁.2.1.2.1,
        ← groupPart_crQ x a hG c p₂.1 p₂.2 hc (hR _ h₂.1.1) h₂.2.1.1 h₂.2.1.2.1, e]
    have hq : p₁.2 = p₂.2 := by
      rw [hr] at e
      have hpos : 0 < c * p₂.1 := Nat.mul_pos hc0 (hR _ h₂.1.1).1
      exact Nat.eq_of_mul_eq_mul_left hpos e
    exact Prod.ext hr hq
  have hwt : ∀ rq ∈ S, constructionWeight M c u Ψ x a (φ rq) =
      mark (1 / 2) x a rq.1 * Ψ (((c * rq.1 * rq.2 + 1 : ℕ) : ℝ) / x) := by
    intro rq h
    simp only [hS, Finset.mem_filter, Finset.mem_product] at h
    exact weight_crQ M c u Ψ x a hG hc rq.1 rq.2 (hR _ h.1.1) h.2.1.1 h.2.1.2.1 h.2.1.2.2
  have hrough : ∀ rq ∈ S, IsRough (x ^ b) (φ rq) := by
    intro rq h
    simp only [hS, Finset.mem_filter, Finset.mem_product] at h
    exact isRough_crQ x b c rq.1 rq.2 hc Pset hP h.2.2 (Real.rpow_nonneg hx.le _)
  calc _ = ∑ rq ∈ S, constructionWeight M c u Ψ x a (φ rq) := by
        rw [hS, Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.filter_filter, Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Q hQ
        split_ifs with h
        · rw [weight_crQ M c u Ψ x a hG hc r Q (hR r hr) h.1.1 h.1.2.1 h.1.2.2]
        · ring
    _ = ∑ d ∈ S.image φ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro rq h
        rw [if_pos (hrough rq h)]
    _ ≤ _ := by
        apply (summable_weight M c u Ψ hΨs x hx a _).sum_le_tsum
        intro d _
        split_ifs
        · exact constructionWeight_nonneg M c u Ψ hΨ0 x a d
        · exact le_rfl

lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp
    exact (hs p hp).prime.squarefree

lemma odd_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) : Odd (∏ p ∈ s, p) := by
  rw [Nat.odd_iff]
  have : ¬ 2 ∣ ∏ p ∈ s, p := by
    intro h
    obtain ⟨p, hp, hdp⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hs p hp).1).mp hdp
    have := (hs p hp).2
    omega
  omega

lemma forall_dvd_iff_dvd (d n : ℕ) (hd : Squarefree d) :
    (∀ p ∈ d.primeFactors, p ∣ n) ↔ d ∣ n := by
  constructor
  · intro h
    rw [← Nat.prod_primeFactors_of_squarefree hd]
    exact Finset.prod_primes_dvd n (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) h
  · intro h p hp
    exact Nat.dvd_trans (Nat.dvd_of_mem_primeFactors hp) h

lemma localDensity_prod (M r : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    localDensity M r (∏ p ∈ s, p) = ∏ p ∈ s, localDensity M r p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localDensity]
  | insert q s hq ih =>
    have hq' : q.Prime := hs q (Finset.mem_insert_self _ _)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hq, Finset.prod_insert hq, ← ih hs']
    have hcop : Nat.Coprime q (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hq' (hs' p hp)).mpr (fun e => hq (e ▸ hp))
    unfold localDensity
    by_cases h1 : Nat.Coprime q (M * r)
    · by_cases h2 : Nat.Coprime (∏ p ∈ s, p) (M * r)
      · rw [if_pos (Nat.Coprime.mul h1 h2), if_pos h1, if_pos h2, Nat.totient_mul hcop]
        push_cast
        rw [one_div_mul_one_div]
      · rw [if_neg (fun h => h2 (Nat.coprime_mul_iff_left.mp h).2), if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 (Nat.coprime_mul_iff_left.mp h).1), if_neg h1, zero_mul]

lemma localDensity_squarefree (M r d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, localDensity M r p = localDensity M r d := by
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  rw [localDensity_prod M r _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]

lemma localDensity_nonneg (M r ℓ : ℕ) : 0 ≤ localDensity M r ℓ := by
  unfold localDensity; split_ifs <;> positivity

lemma localDensity_le_half (M r p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    localDensity M r p ≤ 1 / 2 := by
  unfold localDensity
  split_ifs
  · rw [Nat.totient_prime hp]
    have : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      have : 2 ≤ p - 1 := by omega
      exact_mod_cast this
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · norm_num

lemma localDensity_le_two_div (M r p : ℕ) (hp : p.Prime) :
    localDensity M r p ≤ 2 / p := by
  unfold localDensity
  split_ifs
  · rw [Nat.totient_prime hp]
    have h2 := hp.two_le
    have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · positivity

open Classical in
/-- The block-sieve lower bound at one `r`, with the remainders expressed as `E_r(ℓ)`. -/
lemma sieve_r_lower (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) (r : ℕ) (hc : 1 ≤ c) (hr : 1 ≤ r) (Pset : Finset ℕ)
    (hP : ∀ p ∈ Pset, p.Prime ∧ 2 < p) (H : ℕ) (B z D : ℝ)
    (hzD : z ^ (4 * H + 2) ≤ D)
    (hBS : |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ Pset, ¬ p ∣ c * r * Q + 1), Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
        predecessorMass M c u Ψ x r * ∏ p ∈ Pset, (1 - localDensity M r p)| ≤
      B * (predecessorMass M c u Ψ x r * ∏ p ∈ Pset, (1 - localDensity M r p)) *
          exp (-(H : ℝ)) +
        B * ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
          |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1),
              Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
            predecessorMass M c u Ψ x r * ∏ p ∈ d.primeFactors, localDensity M r p|)
    (hX : 0 ≤ predecessorMass M c u Ψ x r)
    (hPprod : 0 ≤ ∏ p ∈ Pset, (1 - localDensity M r p)) :
    predecessorMass M c u Ψ x r * (∏ p ∈ Pset, (1 - localDensity M r p)) *
        (1 - max B 0 * exp (-(H : ℝ))) -
      max B 0 * ∑ ℓ ∈ (Finset.range (⌊D⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
        |massRemainder M c u Ψ x r ℓ| ≤
    ∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ Pset, ¬ p ∣ c * r * Q + 1), Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) := by
  set Dv := (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)) with hDv
  have hsq : Squarefree (∏ p ∈ Pset, p) := squarefree_prod_primes Pset (fun p hp => (hP p hp).1)
  have hodd : Odd (∏ p ∈ Pset, p) := odd_prod_primes Pset hP
  have hE : ∀ d ∈ Dv,
      ∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1),
              Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
            predecessorMass M c u Ψ x r * ∏ p ∈ d.primeFactors, localDensity M r p =
        massRemainder M c u Ψ x r d := by
    intro d hd
    rw [hDv, Finset.mem_filter, Nat.mem_divisors] at hd
    have hdsq : Squarefree d := hsq.squarefree_of_dvd hd.1.1
    unfold massRemainder
    rw [localDensity_squarefree M r d hdsq, predecessorMassDvd_eq_sum M c u Ψ hΨs x hx r d hc hr,
      Finset.filter_filter, Finset.sum_filter]
    congr 1
    · apply Finset.sum_congr rfl
      intro Q _
      congr 1
      apply propext
      rw [forall_dvd_iff_dvd d _ hdsq]
      tauto
    · ring
  have hsub : Dv ⊆ (Finset.range (⌊D⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) := by
    intro d hd
    rw [hDv, Finset.mem_filter, Nat.mem_divisors] at hd
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor (le_trans hd.2 hzD)), ?_, hsq.squarefree_of_dvd hd.1.1⟩
    exact Odd.of_dvd_nat hodd hd.1.1
  have hsum : ∑ d ∈ Dv, |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧
          x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1),
              Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
            predecessorMass M c u Ψ x r * ∏ p ∈ d.primeFactors, localDensity M r p| ≤
      ∑ ℓ ∈ (Finset.range (⌊D⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
        |massRemainder M c u Ψ x r ℓ| := by
    rw [Finset.sum_congr rfl (fun d hd => by rw [hE d hd])]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  have hB : B * (predecessorMass M c u Ψ x r * ∏ p ∈ Pset, (1 - localDensity M r p)) *
          exp (-(H : ℝ)) ≤ max B 0 * (predecessorMass M c u Ψ x r *
            ∏ p ∈ Pset, (1 - localDensity M r p)) * exp (-(H : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hX hPprod)
  have hB2 : B * ∑ d ∈ Dv, |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧
          x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1),
              Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
            predecessorMass M c u Ψ x r * ∏ p ∈ d.primeFactors, localDensity M r p| ≤
      max B 0 * ∑ ℓ ∈ (Finset.range (⌊D⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
        |massRemainder M c u Ψ x r ℓ| := by
    calc _ ≤ max B 0 * ∑ d ∈ Dv, |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧
          x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1),
              Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
            predecessorMass M c u Ψ x r * ∏ p ∈ d.primeFactors, localDensity M r p| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (le_max_right _ _)
  have := (abs_le.mp hBS).1
  have e : predecessorMass M c u Ψ x r * (∏ p ∈ Pset, (1 - localDensity M r p)) *
        (1 - max B 0 * exp (-(H : ℝ))) = predecessorMass M c u Ψ x r *
          ∏ p ∈ Pset, (1 - localDensity M r p) - max B 0 * (predecessorMass M c u Ψ x r *
            ∏ p ∈ Pset, (1 - localDensity M r p)) * exp (-(H : ℝ)) := by ring
  rw [e]
  linarith

lemma tprod_le_prod_of_le_one {ι : Type*} (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (hm : Multipliable f) (s : Finset ι) : ∏' i, f i ≤ ∏ i ∈ s, f i := by
  classical
  have h := hm.hasProd
  apply le_of_tendsto h
  have : ∀ t : Finset ι, s ⊆ t → ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
    intro t hst
    rw [← Finset.prod_sdiff hst]
    have h1 : ∏ i ∈ t \ s, f i ≤ 1 := Finset.prod_le_one (fun i _ => hf0 i) (fun i _ => hf1 i)
    have h2 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i _ => hf0 i
    nlinarith
  exact Filter.eventually_atTop.mpr ⟨s, this⟩

lemma singular_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)) := by
  have hp3 : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, (3 : ℝ) ≤ p.1 := fun p => by
    exact_mod_cast p.2.2
  have hg : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    apply Summable.neg
    have hs : Summable (fun n : ℕ => 9 / 4 * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
    have hs' := hs.comp_injective (Subtype.val_injective (p := fun p : ℕ => p.Prime ∧ 2 < p))
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hs'
    · have := hp3 p
      positivity
    · have h3 := hp3 p
      simp only [Function.comp]
      rw [div_le_iff₀ (by nlinarith)]
      field_simp
      nlinarith
  have := Real.multipliable_one_add_of_summable hg
  simpa only [← sub_eq_add_neg] using this

/-- `𝔖_M V(y) ≤ ∏_{2 < p ≤ y} (1 - g_r(p))` once `y ≥ M`. -/
lemma singular_le_prod (M r : ℕ) (hM : 0 < M) (y : ℝ) (hy : (M : ℝ) ≤ y) (hy2 : 2 ≤ y) :
    singularSeries M * mertensProduct y ≤
      ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p),
        (1 - localDensity M r p) := by
  classical
  set Pset := (Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p) with hPset
  have hPp : ∀ p ∈ Pset, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
  have hP3 : ∀ p ∈ Pset, (3 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hPp p hp).2
  set h : ℕ → ℝ := fun p => if p ∣ M then 1 else 1 - 1 / ((p : ℝ) - 1) with hh
  -- step (a)
  have ha : ∏ p ∈ Pset, h p ≤ ∏ p ∈ Pset, (1 - localDensity M r p) := by
    apply Finset.prod_le_prod
    · intro p hp
      have := hP3 p hp
      simp only [hh]; split_ifs
      · norm_num
      · have : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
    · intro p hp
      have hpp := (hPp p hp).1
      simp only [hh]
      unfold localDensity
      split_ifs with h1 h2
      · exact absurd (Nat.dvd_trans h1 (dvd_mul_right M r))
          ((Nat.Prime.coprime_iff_not_dvd hpp).mp h2)
      · norm_num
      · rw [Nat.totient_prime hpp]
        have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          rw [Nat.cast_sub hpp.one_le]; simp
        rw [this]
      · have := hP3 p hp
        have : 0 ≤ 1 / ((p : ℝ) - 1) := by
          apply div_nonneg zero_le_one; linarith
        linarith
  refine le_trans ?_ ha
  -- step (b)
  set f : {p : ℕ // p.Prime ∧ 2 < p} → ℝ := fun p => 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 with hf
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
    simp only [hf]
    have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith)]; nlinarith
    linarith
  have hf1 : ∀ p, f p ≤ 1 := by
    intro p
    have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
    simp only [hf]
    have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 2 := by positivity
    linarith
  set Ps : Finset {p : ℕ // p.Prime ∧ 2 < p} := Pset.subtype (fun p => p.Prime ∧ 2 < p)
    with hPs
  have hT := tprod_le_prod_of_le_one f hf0 hf1 singular_multipliable Ps
  have hPsprod : ∏ p ∈ Ps, f p = ∏ p ∈ Pset, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    simp only [hf, hPs]
    rw [Finset.prod_subtype_eq_prod_filter (fun n : ℕ => 1 - 1 / ((n : ℝ) - 1) ^ 2)]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext p; simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, hPp p h⟩
  rw [hPsprod] at hT
  have hT0 : 0 ≤ ∏' p, f p := tprod_nonneg hf0
  -- the Mertens product
  have hV : mertensProduct y = (1 - 1 / 2) * ∏ p ∈ Pset, (1 - 1 / (p : ℝ)) := by
    unfold mertensProduct
    have hsplit : (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime =
        insert 2 Pset := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range, hPset]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge 2 p with h | h
        · exact Or.inr ⟨h1, h2, h⟩
        · exact Or.inl (le_antisymm h h2.two_le)
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · refine ⟨?_, Nat.prime_two⟩
          have : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy2)
          omega
        · exact ⟨h1, h2⟩
    rw [hsplit, Finset.prod_insert]
    · norm_num
    · simp [hPset]
  -- factors dividing `M`
  have hMfac : M.primeFactors.filter (2 < ·) = Pset.filter (· ∣ M) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, hPset, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp, hd, -⟩, h2⟩
      refine ⟨⟨?_, hp, h2⟩, hd⟩
      have : p ≤ M := Nat.le_of_dvd hM hd
      have : p ≤ ⌊y⌋₊ := Nat.le_floor (le_trans (by exact_mod_cast this) hy)
      omega
    · rintro ⟨⟨-, hp, h2⟩, hd⟩
      exact ⟨⟨hp, hd, hM.ne'⟩, h2⟩
  have hfac : ∀ p ∈ Pset, (1 - 1 / ((p : ℝ) - 1) ^ 2) * (1 - 1 / (p : ℝ)) =
      1 - 1 / ((p : ℝ) - 1) := by
    intro p hp
    have := hP3 p hp
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hh_split : ∏ p ∈ Pset, h p =
      ∏ p ∈ Pset.filter (fun p => ¬ p ∣ M), (1 - 1 / ((p : ℝ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Pset (· ∣ M) h]
    have e1 : ∏ p ∈ Pset.filter (· ∣ M), h p = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      simp only [hh, if_pos (Finset.mem_filter.mp hp).2]
    rw [e1, one_mul]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [hh, if_neg (Finset.mem_filter.mp hp).2]
  have hall : ∏ p ∈ Pset, (1 - 1 / ((p : ℝ) - 1)) =
      (∏ p ∈ Pset.filter (· ∣ M), (1 - 1 / ((p : ℝ) - 1))) *
        ∏ p ∈ Pset.filter (fun p => ¬ p ∣ M), (1 - 1 / ((p : ℝ) - 1)) :=
    (Finset.prod_filter_mul_prod_filter_not Pset (· ∣ M) _).symm
  have hPiM : (∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) *
      ∏ p ∈ Pset.filter (· ∣ M), (1 - 1 / ((p : ℝ) - 1)) = 1 := by
    rw [hMfac, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have := hP3 p (Finset.mem_filter.mp hp).1
    have : 1 - 1 / ((p : ℝ) - 1) ≠ 0 := by
      have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      linarith
    field_simp
  have hPiM0 : 0 ≤ ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    simp only [Finset.mem_filter] at hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    apply inv_nonneg.mpr; linarith
  have hV0 : 0 ≤ ∏ p ∈ Pset, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have := hP3 p hp
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  unfold singularSeries
  rw [hV, hh_split]
  calc 2 * (∏' p, f p) * (∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) *
        ((1 - 1 / 2) * ∏ p ∈ Pset, (1 - 1 / (p : ℝ)))
      = (∏' p, f p) * (∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) *
          ∏ p ∈ Pset, (1 - 1 / (p : ℝ)) := by ring
    _ ≤ (∏ p ∈ Pset, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
          (∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) *
          ∏ p ∈ Pset, (1 - 1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hV0
        exact mul_le_mul_of_nonneg_right hT hPiM0
    _ = (∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) *
          ∏ p ∈ Pset, ((1 - 1 / ((p : ℝ) - 1) ^ 2) * (1 - 1 / (p : ℝ))) := by
        rw [Finset.prod_mul_distrib]; ring
    _ = (∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) *
          ∏ p ∈ Pset, (1 - 1 / ((p : ℝ) - 1)) := by
        rw [Finset.prod_congr rfl hfac]
    _ = ∏ p ∈ Pset.filter (fun p => ¬ p ∣ M), (1 - 1 / ((p : ℝ) - 1)) := by
        rw [hall, ← mul_assoc, hPiM, one_mul]

/-- A uniform bound `∑_{v < p ≤ v²} 1/p ≤ C₀` for all `v > 1`. -/
lemma block_sum_bound : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ v : ℝ, 1 < v →
    ∑ p ∈ (Finset.range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) / p ≤
      C₀ := by
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  obtain ⟨V₀, hV₀⟩ := Filter.eventually_atTop.mp
    (hm.eventually (gt_mem_nhds (show log (2 / 1) < log (2 / 1) + 1 by linarith)))
  refine ⟨max (log (2 / 1) + 1) ((⌊(max V₀ 1) ^ 2⌋₊ : ℝ) + 1), le_trans (by positivity)
    (le_max_right _ _), fun v hv => ?_⟩
  by_cases hvV : V₀ ≤ v
  · have := hV₀ v hvV
    simp only [Real.rpow_one] at this
    have e : v ^ (2 : ℝ) = v ^ 2 := by exact_mod_cast Real.rpow_natCast v 2
    rw [e] at this
    exact le_trans this.le (le_max_left _ _)
  · push_neg at hvV
    refine le_trans ?_ (le_max_right _ _)
    calc ∑ p ∈ (Finset.range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) / p
        ≤ ∑ p ∈ (Finset.range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le
          rw [div_le_one (by linarith)]; exact this
      _ ≤ ((⌊v ^ 2⌋₊ + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)
      _ ≤ (⌊(max V₀ 1) ^ 2⌋₊ : ℝ) + 1 := by
          push_cast
          have : ⌊v ^ 2⌋₊ ≤ ⌊(max V₀ 1) ^ 2⌋₊ := by
            apply Nat.floor_le_floor
            have : v ≤ max V₀ 1 := le_trans hvV.le (le_max_left _ _)
            nlinarith
          have : (⌊v ^ 2⌋₊ : ℝ) ≤ ⌊(max V₀ 1) ^ 2⌋₊ := by exact_mod_cast this
          linarith

/-- The block-sum hypothesis of the block sieve for `g_r`. -/
lemma block_sum_g (C₀ : ℝ) (hC₀ : ∀ v : ℝ, 1 < v →
    ∑ p ∈ (Finset.range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) / p ≤ C₀)
    (M r : ℕ) (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (v : ℝ) (hv : 1 < v) :
    ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), localDensity M r p ≤ 2 * C₀ := by
  calc ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), localDensity M r p
      ≤ ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), 2 * ((1 : ℝ) / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have := localDensity_le_two_div M r p (hP p (Finset.mem_filter.mp hp).1)
        rw [mul_one_div]; exact this
    _ ≤ ∑ p ∈ (Finset.range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p),
          2 * ((1 : ℝ) / p) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter] at hp ⊢
          refine ⟨?_, hP p hp.1, hp.2.1⟩
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (Nat.le_floor hp.2.2)
        · intro p _ _; positivity
    _ = 2 * ∑ p ∈ (Finset.range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p),
          (1 : ℝ) / p := by rw [Finset.mul_sum]
    _ ≤ 2 * C₀ := by linarith [hC₀ v hv]

/-- Eventually every group prime lies in `(2, x^{0.9})`. -/
lemma eventually_groupPrimesSmall {K : ℕ} (a : Fin K → ℝ)
    (ha' : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) : ∀ᶠ x : ℝ in atTop, GroupPrimesSmall x a := by
  have hL := Real.tendsto_log_atTop
  have h1 : Tendsto (fun x : ℝ => log x ^ (0.1 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hL
  have h2 : Tendsto (fun x : ℝ => log x ^ (-(0.8 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp hL
  filter_upwards [h1.eventually_gt_atTop 1, h2.eventually (gt_mem_nhds (by norm_num :
    (0 : ℝ) < 0.45)), hL.eventually_gt_atTop 1, eventually_gt_atTop 0] with x hx1 hx2 hLx hx0
  intro p hp
  simp only [groupPrimes, primeGroup, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨i, hle, -, hge⟩ := hp
  obtain ⟨ha1, ha2⟩ := ha' i
  have hL0 : 0 < log x := by linarith
  have hLa : log x ^ (0.1 : ℝ) ≤ log x ^ a i :=
    Real.rpow_le_rpow_of_exponent_le hLx.le ha1.le
  constructor
  · have : (2 : ℝ) < p := by
      refine lt_of_lt_of_le ?_ hge
      calc (2 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
        _ ≤ exp (log x ^ a i) := Real.exp_le_exp.mpr (by linarith)
    exact_mod_cast this
  · have hp : (p : ℝ) ≤ exp (2 * log x ^ a i) :=
      le_trans (by exact_mod_cast Nat.le_of_lt_succ hle) (Nat.floor_le (by positivity))
    refine lt_of_le_of_lt hp ?_
    rw [Real.rpow_def_of_pos hx0, Real.exp_lt_exp]
    have h02 : log x ^ a i ≤ log x ^ (0.2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLx.le ha2.le
    have hsplit : log x ^ (0.2 : ℝ) = log x ^ (-(0.8 : ℝ)) * log x := by
      rw [← Real.rpow_add_one hL0.ne']; norm_num
    have : 2 * log x ^ (0.2 : ℝ) < 0.9 * log x := by
      rw [hsplit]; nlinarith
    nlinarith

/-- Mertens at `y = x^b`: eventually `V(x^b) ≥ (1 - η) e^{-γ}/(bL)`. -/
lemma eventually_mertens_xb (b η : ℝ) (hb : 0 < b) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, (1 - η) * exp (-eulerMascheroniConstant) / (b * log x) ≤
      mertensProduct (x ^ b) := by
  have hγ : 0 < exp (-eulerMascheroniConstant) := Real.exp_pos _
  have hlim := mertens_product.comp (tendsto_rpow_atTop hb)
  have h1 := hlim.eventually (lt_mem_nhds (show (1 - η) * exp (-eulerMascheroniConstant) <
    exp (-eulerMascheroniConstant) by nlinarith))
  filter_upwards [h1, Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop 0]
    with x hx hL hx0
  simp only [Function.comp] at hx
  rw [Real.log_rpow hx0] at hx
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma Psi_eq_zero_of_ge (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (y : ℝ) (hy : 2 ≤ y) :
    Ψ y = 0 := by
  by_contra h
  have := hΨs (subset_tsupport _ h)
  linarith [this.2]

lemma predecessorMass_eq_zero_of_ge (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (x : ℝ) (hx : 0 < x) (hc : 1 ≤ c) (r : ℕ)
    (hr : ⌈2 * x⌉₊ ≤ r) : predecessorMass M c u Ψ x r = 0 := by
  have hr1 : 1 ≤ r := le_trans (Nat.one_le_iff_ne_zero.mpr
    (by have := Nat.ceil_pos.mpr (by linarith : (0 : ℝ) < 2 * x); omega)) hr
  rw [predecessorMass, predecessorMassDvd_eq_sum M c u Ψ hΨs x hx r 1 hc hr1]
  apply Finset.sum_eq_zero
  intro Q _
  split_ifs with h
  · apply Psi_eq_zero_of_ge Ψ hΨs
    rw [le_div_iff₀ hx]
    have hQ1 := h.1.one_le
    have : r ≤ c * r * Q := by
      calc r = 1 * r * 1 := by ring
        _ ≤ c * r * Q := Nat.mul_le_mul (Nat.mul_le_mul_right r hc) hQ1
    have h1 : (2 * x) ≤ (r : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hr)
    have h2 : (r : ℝ) ≤ c * r * Q := by exact_mod_cast this
    push_cast; linarith
  · rfl

open Classical in
/-- `X₀ ≤ ∑_{r ≤ x^ε} 𝒲(r) A_r + ∑_{r > x^ε} 𝒲(r) A_r`. -/
lemma mass_split (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ)
    (hG : GroupPrimesSmall x a) (hc : c = 2 ∨ c = 4) (ε : ℝ) :
    totalMass M c u Ψ x a ≤
      ∑ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
          mark (1 / 2) x a r * predecessorMass M c u Ψ x r +
        ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
          mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  set N := ⌈2 * x⌉₊
  set w := constructionWeight M c u Ψ x a with hw
  set g : ℕ → ℕ := fun d => groupPart x a (d - 1)
  set F : ℕ → ℝ := fun r => mark (1 / 2) x a r * predecessorMass M c u Ψ x r with hF
  have hX : totalMass M c u Ψ x a = ∑ d ∈ (Finset.range N).filter (fun d => w d ≠ 0), w d := by
    unfold totalMass
    rw [tsum_eq_sum (s := Finset.range N)]
    · rw [Finset.sum_filter_ne_zero]
    · intro d hd
      simp only [Finset.mem_range, not_lt] at hd
      exact weight_eq_zero_of_ge M c u Ψ hΨs x hx a d hd
  rw [hX, ← Finset.sum_filter_add_sum_filter_not _ (fun d => g d ≤ ⌊x ^ ε⌋₊)]
  apply add_le_add
  · apply sum_weight_le_marks M c u Ψ hΨs hΨ0 x hx a hG hc
    · intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
    · intro d hd
      rw [Finset.mem_filter] at hd
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hd.2,
        (support_structure M c u Ψ hΨs x hx a hG hc d (Finset.mem_filter.mp hd.1).2).1⟩
  · set T2 := (Finset.range N).filter (fun r => IsGroupInteger x a r ∧ x ^ ε < r) with hT2
    refine le_trans (sum_weight_le_marks M c u Ψ hΨs hΨ0 x hx a hG hc _ T2 ?_ ?_) ?_
    · intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hd1, hd2⟩ := hd
      rw [Finset.mem_filter, Finset.mem_range] at hd1
      have hgi := (support_structure M c u Ψ hΨs x hx a hG hc d hd1.2).1
      rw [hT2, Finset.mem_filter, Finset.mem_range]
      have hle : g d ≤ d - 1 := by
        have hd2' := (constructionWeight_support M c u Ψ hΨs x hx a d hd1.2).1
        exact Nat.le_of_dvd (by omega) (groupPart_dvd x a (d - 1))
      refine ⟨lt_of_le_of_lt hle (lt_of_le_of_lt (Nat.sub_le d 1) hd1.1), hgi, ?_⟩
      push_neg at hd2
      have := Nat.lt_floor_add_one (x ^ ε)
      have : ((⌊x ^ ε⌋₊ + 1 : ℕ) : ℝ) ≤ g d := by exact_mod_cast hd2
      push_cast at this
      linarith
    · have hF0 : ∀ r, 0 ≤ F r := fun r =>
        mul_nonneg (mark_nonneg _ _ _) (predecessorMass_nonneg M c u Ψ hΨ0 x r)
      have hsum : Summable (fun r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r} => F r.1) := by
        apply summable_of_ne_finset_zero
          (s := (Finset.range N).subtype (fun r => IsGroupInteger x a r ∧ x ^ ε < r))
        intro r hr
        simp only [Finset.mem_subtype, Finset.mem_range, not_lt] at hr
        simp only [hF, predecessorMass_eq_zero_of_ge M c u Ψ hΨs x hx hc1 r.1 hr, mul_zero]
      calc ∑ r ∈ T2, mark (1 / 2) x a r * predecessorMass M c u Ψ x r
          = ∑ r ∈ (Finset.range N).subtype (fun r => IsGroupInteger x a r ∧ x ^ ε < r),
              F r.1 := by
            rw [Finset.sum_subtype_eq_sum_filter]
        _ ≤ ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, F r.1 :=
            hsum.sum_le_tsum _ (fun r _ => hF0 r.1)

open Classical in
/-- The lower bound for `S_b` at a fixed `x`, summed over `r ≤ x^ε` (§12.3). -/
lemma Sb_lower_core (M c : ℕ) (u : ℤ) (hM : 0 < M) (Ψ : ℝ → ℝ)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 0 < x) {K : ℕ}
    (a : Fin K → ℝ) (hG : GroupPrimesSmall x a) (hc : c = 2 ∨ c = 4) (b ε : ℝ)
    (hxbM : (M : ℝ) ≤ x ^ b) (hxb2 : 2 ≤ x ^ b) (H : ℕ) (B D : ℝ)
    (hzD : (x ^ b) ^ (4 * H + 2) ≤ D) (hδ : 0 ≤ 1 - max B 0 * exp (-(H : ℝ)))
    (hBSr : ∀ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
      |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ (Finset.range (⌊x ^ b⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p),
              ¬ p ∣ c * r * Q + 1), Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
        predecessorMass M c u Ψ x r * ∏ p ∈ (Finset.range (⌊x ^ b⌋₊ + 1)).filter
          (fun p => p.Prime ∧ 2 < p), (1 - localDensity M r p)| ≤
      B * (predecessorMass M c u Ψ x r * ∏ p ∈ (Finset.range (⌊x ^ b⌋₊ + 1)).filter
          (fun p => p.Prime ∧ 2 < p), (1 - localDensity M r p)) * exp (-(H : ℝ)) +
        B * ∑ d ∈ (∏ p ∈ (Finset.range (⌊x ^ b⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p),
            p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x ^ b) ^ (4 * H + 2)),
          |∑ Q ∈ ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
            ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])).filter
            (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1),
              Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) -
            predecessorMass M c u Ψ x r * ∏ p ∈ d.primeFactors, localDensity M r p|) :
    (1 - max B 0 * exp (-(H : ℝ))) * (singularSeries M * mertensProduct (x ^ b)) *
        ∑ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
          mark (1 / 2) x a r * predecessorMass M c u Ψ x r -
      max B 0 * ∑ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
          mark (1 / 2) x a r * ∑ ℓ ∈ (Finset.range (⌊D⌋₊ + 1)).filter
            (fun ℓ => Odd ℓ ∧ Squarefree ℓ), |massRemainder M c u Ψ x r ℓ| ≤
      ∑' d : ℕ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) := by
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  set R := (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a) with hR
  set Pset := (Finset.range (⌊x ^ b⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p) with hPset
  have hP : ∀ p ∈ Pset, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
  have hPin : ∀ p : ℕ, p.Prime → 2 < p → (p : ℝ) ≤ x ^ b → p ∈ Pset := by
    intro p hp h2 hle
    rw [hPset, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hp, h2⟩
  have hSV : 0 ≤ singularSeries M * mertensProduct (x ^ b) :=
    mul_nonneg (singularSeries_pos M).le (mertensProduct_pos _).le
  refine le_trans ?_ (sieved_le_Sb M c u Ψ hΨs hΨ0 x hx a hG hc b R Pset
    (fun r hr => (Finset.mem_filter.mp hr).2) hPin)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro r hr
  have hgi : IsGroupInteger x a r := (Finset.mem_filter.mp hr).2
  have hX := predecessorMass_nonneg M c u Ψ hΨ0 x r
  have hprod_ge := singular_le_prod M r hM (x ^ b) hxbM hxb2
  have hprod0 : 0 ≤ ∏ p ∈ Pset, (1 - localDensity M r p) := le_trans hSV hprod_ge
  have hsieve := sieve_r_lower M c u Ψ hΨs x hx r hc1 hgi.1 Pset hP H B (x ^ b) D hzD
    (hBSr r hr) hX hprod0
  have hm := mark_nonneg x a r
  have h1 : (1 - max B 0 * exp (-(H : ℝ))) * (singularSeries M * mertensProduct (x ^ b)) *
      (mark (1 / 2) x a r * predecessorMass M c u Ψ x r) ≤
      mark (1 / 2) x a r * (predecessorMass M c u Ψ x r *
        (∏ p ∈ Pset, (1 - localDensity M r p)) * (1 - max B 0 * exp (-(H : ℝ)))) := by
    have : (1 - max B 0 * exp (-(H : ℝ))) * (singularSeries M * mertensProduct (x ^ b)) ≤
        (1 - max B 0 * exp (-(H : ℝ))) * ∏ p ∈ Pset, (1 - localDensity M r p) :=
      mul_le_mul_of_nonneg_left hprod_ge hδ
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hm hX)
    linarith
  have h2 := mul_le_mul_of_nonneg_left hsieve hm
  nlinarith

lemma eventually_tail_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (e : ℝ) (he : 0.8 ≤ e) :
    ∀ᶠ x : ℝ in atTop, exp (-ε * log x ^ e) * log x ≤ δ := by
  have h1 : Tendsto (fun t : ℝ => t ^ (1.25 : ℝ) * exp (-ε * t)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1.25 ε hε
  have h2 : Tendsto (fun x : ℝ => log x ^ (0.8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [(h1.comp h2).eventually (gt_mem_nhds hδ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  simp only [Function.comp] at hx
  have hL0 : 0 ≤ log x := by linarith
  have hpow : (log x ^ (0.8 : ℝ)) ^ (1.25 : ℝ) = log x := by
    rw [← Real.rpow_mul hL0]; norm_num
  rw [hpow] at hx
  have hle : log x ^ (0.8 : ℝ) ≤ log x ^ e := Real.rpow_le_rpow_of_exponent_le hL he
  have : exp (-ε * log x ^ e) ≤ exp (-ε * log x ^ (0.8 : ℝ)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  nlinarith [Real.exp_pos (-ε * log x ^ e)]

lemma initial_arith (S X L E V A₀ T δ δs η η₁ BR Sb : ℝ) (hS : 0 < S) (hX : 0 ≤ X)
    (hL : 0 < L) (hE : 0 < E) (hη : 0 < η) (hη₁0 : 0 < η₁) (hη₁h : η₁ ≤ 1 / 2)
    (hη₁E : 2 * η₁ * E ≤ η / 2) (hV : (1 - η₁) * E / L ≤ V) (hA : X - T ≤ A₀)
    (hT : T ≤ η₁ * X) (hδ : δ ≤ δs) (hδs : δs ≤ 1 / 2) (hδs0 : 0 ≤ δs)
    (hR : BR ≤ η / 2 * (S * X / L)) (hcore : (1 - δ) * (S * V) * A₀ - BR ≤ Sb) :
    S * X / L * (E * (1 - δs) - η) ≤ Sb := by
  have hA' : (1 - η₁) * X ≤ A₀ := by nlinarith
  have hV0 : 0 ≤ (1 - η₁) * E / L := by
    apply div_nonneg _ hL.le; nlinarith
  have hA0 : 0 ≤ (1 - η₁) * X := by nlinarith
  have h1 : (1 - δs) * (S * ((1 - η₁) * E / L)) * ((1 - η₁) * X) ≤ (1 - δ) * (S * V) * A₀ := by
    apply mul_le_mul _ hA' hA0 (by nlinarith [mul_nonneg hS.le (le_trans hV0 hV)])
    apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hV hS.le)
      (mul_nonneg hS.le hV0) (by linarith)
  have h2 : (1 - δs) * (S * ((1 - η₁) * E / L)) * ((1 - η₁) * X) =
      S * X / L * (E * ((1 - δs) * (1 - η₁) ^ 2)) := by
    field_simp
  have h3 : E * (1 - δs) - η / 2 ≤ E * ((1 - δs) * (1 - η₁) ^ 2) := by
    have : (1 - δs) * (1 - η₁) ^ 2 ≥ (1 - δs) - 2 * η₁ := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - δs) (sq_nonneg η₁),
        mul_nonneg hη₁0.le hδs0]
    nlinarith
  have hSXL : 0 ≤ S * X / L := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hSXL
  nlinarith

set_option maxHeartbeats 4000000 in
open Classical in
/-- The initial lower bound (12.22), from the block sieve with `z = x^b`, `H = 2⌊1/(40b)⌋`. -/
theorem initial_lower :
    ∃ C_s b₁ : ℝ, 0 < C_s ∧ 0 < b₁ ∧
    ∀ (M c : ℕ) (u : ℤ), 0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → IsCoprime u M →
      (c : ℤ) ∣ u - 1 → IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
    ∀ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ Set.Ioo 1 2 →
      (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) → 0 < ∫ y, Ψ y →
    ∀ b : ℝ, 0 < b → b < b₁ →
    ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      singularSeries M * totalMass M c u Ψ x a / log x *
          (exp (-eulerMascheroniConstant) / b * (1 - C_s * exp (-(1 / 20) / b)) - η) ≤
        ∑' d : ℕ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := block_sum_bound
  obtain ⟨⟨H₀, B, hBS⟩, -⟩ := block_sieve.{0, 0} (1 / 2) (2 * C₀) (by norm_num)
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set C_s := B' * exp 2 + 1 with hCs
  have hCs1 : 1 ≤ C_s := by have : 0 ≤ B' * exp 2 := by positivity
                            linarith
  have hlog2C : 0 < log (2 * C_s) + 1 := by
    have : 0 ≤ log (2 * C_s) := Real.log_nonneg (by linarith)
    linarith
  set b₂ := 1 / (20 * (log (2 * C_s) + 1)) with hb₂
  refine ⟨C_s, min (min (1 / (40 * ((H₀ : ℝ) + 1))) 0.01) b₂, by positivity,
    lt_min (lt_min (by positivity) (by norm_num)) (by positivity), ?_⟩
  intro M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi b hb hbb K hK1 a ha ha' η hη
  have hbH : b < 1 / (40 * ((H₀ : ℝ) + 1)) :=
    lt_of_lt_of_le hbb (le_trans (min_le_left _ _) (min_le_left _ _))
  have hb01 : b < 0.01 := lt_of_lt_of_le hbb (le_trans (min_le_left _ _) (min_le_right _ _))
  have hbb2 : b < b₂ := lt_of_lt_of_le hbb (min_le_right _ _)
  set H : ℕ := 2 * ⌊1 / (40 * b)⌋₊ with hHdef
  have hHeven : Even H := even_two_mul _
  have hfl : (H₀ : ℝ) + 1 < 1 / (40 * b) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hbH
    linarith
  have hH₀ : H₀ ≤ H := by
    have : H₀ ≤ ⌊1 / (40 * b)⌋₊ := Nat.le_floor (by linarith)
    omega
  have hHlow : 1 / (20 * b) - 2 ≤ (H : ℝ) := by
    have := Nat.lt_floor_add_one (1 / (40 * b))
    have e : (H : ℝ) = 2 * (⌊1 / (40 * b)⌋₊ : ℝ) := by rw [hHdef]; push_cast; ring
    have e2 : 1 / (20 * b) = 2 * (1 / (40 * b)) := by field_simp; norm_num
    rw [e, e2]; linarith
  have hHup : (H : ℝ) ≤ 1 / (20 * b) := by
    have := Nat.floor_le (show (0 : ℝ) ≤ 1 / (40 * b) by positivity)
    have e : (H : ℝ) = 2 * (⌊1 / (40 * b)⌋₊ : ℝ) := by rw [hHdef]; push_cast; ring
    have e2 : 1 / (20 * b) = 2 * (1 / (40 * b)) := by field_simp; norm_num
    rw [e, e2]; linarith
  have hexp_eq : -(1 / 20) / b = -(1 / (20 * b)) := by field_simp
  have hδs : C_s * exp (-(1 / 20) / b) ≤ 1 / 2 := by
    rw [hexp_eq]
    have h1 : log (2 * C_s) < 1 / (20 * b) := by
      rw [hb₂, lt_div_iff₀ (by positivity)] at hbb2
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have h3 : 2 * C_s ≤ exp (1 / (20 * b)) := by
      rw [← Real.exp_log (show 0 < 2 * C_s by positivity)]
      exact Real.exp_le_exp.mpr h1.le
    have h2 : exp (-(1 / (20 * b))) ≤ 1 / (2 * C_s) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) h3
    calc C_s * exp (-(1 / (20 * b))) ≤ C_s * (1 / (2 * C_s)) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 1 / 2 := by field_simp
  have hδ : B' * exp (-(H : ℝ)) ≤ C_s * exp (-(1 / 20) / b) := by
    rw [hexp_eq]
    have : exp (-(H : ℝ)) ≤ exp 2 * exp (-(1 / (20 * b))) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    calc B' * exp (-(H : ℝ)) ≤ B' * (exp 2 * exp (-(1 / (20 * b)))) :=
          mul_le_mul_of_nonneg_left this hB'0
      _ = (B' * exp 2) * exp (-(1 / (20 * b))) := by ring
      _ ≤ C_s * exp (-(1 / (20 * b))) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  -- the inputs
  obtain ⟨hwfd1, c₁, c₂, hc₁, hc₂, hwfd2⟩ :=
    weighted_family_distribution M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  obtain ⟨Cbv, x₁, hbv⟩ := (hwfd1 c u hc hu hcu hcop K hK1 a ha ha').1 0.005 0.001
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num)
  obtain ⟨x₂, hx₂⟩ := hwfd2 c u hc hu hcu hcop K hK1 a ha ha'
  obtain ⟨CJ, hCJ⟩ := harmonic_mass M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK1
  obtain ⟨x₃, hx₃⟩ := hCJ a ha ha' 0.001 (by norm_num)
  have hS := singularSeries_pos M
  set E := exp (-eulerMascheroniConstant) / b with hE
  have hE0 : 0 < E := by positivity
  set η₁ := min (1 / 2) (η / (4 * E)) with hη₁
  have hη₁0 : 0 < η₁ := lt_min (by norm_num) (by positivity)
  have hη₁h : η₁ ≤ 1 / 2 := min_le_left _ _
  have hη₁E : 2 * η₁ * E ≤ η / 2 := by
    have : η₁ ≤ η / (4 * E) := min_le_right _ _
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * E)
    have e : η / (4 * E) * (2 * E) = η / 2 := by field_simp; ring
    nlinarith
  have haK := ha' ⟨K - 1, by omega⟩
  have hev : ∀ᶠ x : ℝ in atTop, x₁ ≤ x ∧ x₂ ≤ x ∧ x₃ ≤ x ∧ GroupPrimesSmall x a ∧
      (1 - η₁) * exp (-eulerMascheroniConstant) / (b * log x) ≤ mertensProduct (x ^ b) ∧
      ((M : ℝ) + 2) ≤ x ^ b ∧
      exp (-0.001 * log x ^ (1 - a ⟨K - 1, by omega⟩)) * log x ≤ η₁ * c₁ / (max CJ 0 + 1) ∧
      2 * B' * max Cbv 0 / (η * singularSeries M * c₁) + 1 ≤ log x ∧ 1 < x :=
    (eventually_ge_atTop x₁).and ((eventually_ge_atTop x₂).and ((eventually_ge_atTop x₃).and
      ((eventually_groupPrimesSmall a ha').and ((eventually_mertens_xb b η₁ hb hη₁0).and
      (((tendsto_rpow_atTop hb).eventually_ge_atTop _).and
      ((eventually_tail_small 0.001 _ (by norm_num) (by positivity) _ (by linarith [haK.2])).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop _).and (eventually_gt_atTop 1))))))))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨hx1, hx2, hx3, hG, hV, hxbM, htail, hLbig, hx1'⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx1'
  set X₀ := totalMass M c u Ψ x a with hX₀
  have hX0 : 0 ≤ X₀ := totalMass_nonneg M c u Ψ hΨ0 x a
  obtain ⟨-, -, hJ, -, -, htail2⟩ := hx₃ x hx3
  have hXlow := (hx₂ x hx2).1
  have hbvx := hbv x hx1
  have hz2 : (2 : ℝ) ≤ x ^ b := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hzM : (M : ℝ) ≤ x ^ b := by linarith
  set D := x ^ (1 / 2 - (0.005 : ℝ) / 2) with hD
  have hzD : (x ^ b) ^ (4 * H + 2) ≤ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1'.le
    push_cast
    have : b * (4 * (H : ℝ) + 2) ≤ b * (4 * (1 / (20 * b)) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hb.le
    have e : b * (4 * (1 / (20 * b)) + 2) = 1 / 5 + 2 * b := by field_simp; ring
    linarith
  have hδ0 : 0 ≤ B' * exp (-(H : ℝ)) := by positivity
  have hδ' : 0 ≤ 1 - max B 0 * exp (-(H : ℝ)) := by linarith
  set Pset := (Finset.range (⌊x ^ b⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p) with hPset
  have hPz : ∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ x ^ b := by
    intro p hp
    rw [hPset, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2.1, le_trans (by exact_mod_cast Nat.le_of_lt_succ hp.1)
      (Nat.floor_le (by positivity))⟩
  have hcore := Sb_lower_core M c u hM Ψ hΨs hΨ0 x hx0 a hG hc b 0.001 hzM hz2 H B D hzD hδ'
    (by
      intro r hr
      have key := hBS H hH₀ hHeven
        ((Finset.range ⌈2 * x⌉₊).filter (fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
              ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]))
        (fun Q => Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x)) (fun Q _ => hΨ0 _) (x ^ b) hz2 Pset hPz
        (fun p Q => p ∣ c * r * Q + 1) (predecessorMass M c u Ψ x r)
        (predecessorMass_nonneg M c u Ψ hΨ0 x r) (localDensity M r)
        (fun p hp => ⟨localDensity_nonneg M r p, by
          have := localDensity_le_half M r p (Finset.mem_filter.mp hp).2.1
            (Finset.mem_filter.mp hp).2.2
          linarith⟩)
        (fun v hv => block_sum_g C₀ hC₀ M r Pset (fun p hp => (hPz p hp).1) v hv)
      dsimp only at key
      convert key using 5)
  have hsplit := mass_split M c u Ψ hΨs hΨ0 x hx0 a hG hc 0.001
  set A₀ := ∑ r ∈ (Finset.range (⌊x ^ (0.001 : ℝ)⌋₊ + 1)).filter (IsGroupInteger x a),
    mark (1 / 2) x a r * predecessorMass M c u Ψ x r with hA₀
  set T := ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ (0.001 : ℝ) < r},
    mark (1 / 2) x a r * predecessorMass M c u Ψ x r with hTdef
  set Rem := ∑ r ∈ (Finset.range (⌊x ^ (0.001 : ℝ)⌋₊ + 1)).filter (IsGroupInteger x a),
    mark (1 / 2) x a r * ∑ ℓ ∈ (Finset.range (⌊D⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
      |massRemainder M c u Ψ x r ℓ| with hRem
  have hRem0 : 0 ≤ Rem := Finset.sum_nonneg fun r _ =>
    mul_nonneg (mark_nonneg _ _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  set J₀ := harmonicMass x a
  have hcx : c₁ * x / log x ≤ X₀ := by
    refine le_trans ?_ hXlow
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hc₁.le
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith
  -- the tail
  set e := exp (-0.001 * log x ^ (1 - a ⟨K - 1, by omega⟩)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hT : T ≤ η₁ * X₀ := by
    have h1 : T ≤ (max CJ 0 + 1) * (x * e) := by
      refine le_trans htail2 ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [le_max_left CJ 0]
    have h2 : (max CJ 0 + 1) * (e * log x) ≤ η₁ * c₁ := by
      have hpos : 0 < max CJ 0 + 1 := by linarith [le_max_right CJ 0]
      rw [le_div_iff₀ hpos] at htail
      linarith
    have h3 : (max CJ 0 + 1) * (x * e) ≤ η₁ * (c₁ * x / log x) := by
      rw [mul_div_assoc', le_div_iff₀ hL]
      nlinarith
    have h4 : η₁ * (c₁ * x / log x) ≤ η₁ * X₀ := mul_le_mul_of_nonneg_left hcx hη₁0.le
    linarith
  -- the remainders
  have hR : max B 0 * Rem ≤ η / 2 * (singularSeries M * X₀ / log x) := by
    have h1 : Rem ≤ max Cbv 0 * (x * J₀ * log x ^ (-3 : ℝ)) := by
      refine le_trans hbvx ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hL3 : log x ^ (-3 : ℝ) = 1 / log x ^ 3 := by
      rw [Real.rpow_neg hL.le, one_div]
      congr 1
      exact_mod_cast Real.rpow_natCast (log x) 3
    rw [hL3] at h1
    have hpos : 0 < η * singularSeries M * c₁ := by positivity
    have h2 : 2 * B' * max Cbv 0 ≤ η * singularSeries M * c₁ * log x := by
      have := hLbig
      rw [← sub_nonneg] at this
      have h' : 2 * B' * max Cbv 0 / (η * singularSeries M * c₁) ≤ log x := by linarith
      rw [div_le_iff₀ hpos] at h'
      linarith
    have hJ0 : 0 ≤ J₀ := by linarith
    calc max B 0 * Rem ≤ B' * (max Cbv 0 * (x * J₀ * (1 / log x ^ 3))) :=
          mul_le_mul_of_nonneg_left h1 hB'0
      _ = (2 * B' * max Cbv 0) * (x * J₀ / log x ^ 3) / 2 := by ring
      _ ≤ (η * singularSeries M * c₁ * log x) * (x * J₀ / log x ^ 3) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = η / 2 * (singularSeries M * (c₁ * (x * J₀ / log x)) / log x) := by
          field_simp
      _ ≤ η / 2 * (singularSeries M * X₀ / log x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ hL.le
          exact mul_le_mul_of_nonneg_left hXlow hS.le
  have hV' : (1 - η₁) * E / log x ≤ mertensProduct (x ^ b) := by
    refine le_trans (le_of_eq ?_) hV
    rw [hE]; field_simp
  exact initial_arith (singularSeries M) X₀ (log x) E (mertensProduct (x ^ b)) A₀ T
    (B' * exp (-(H : ℝ))) (C_s * exp (-(1 / 20) / b)) η η₁ (max B 0 * Rem) _ hS hX0 hL hE0 hη
    hη₁0 hη₁h hη₁E hV' (by linarith) hT hδ hδs (by positivity) hR hcore

end ArtinPrimitiveRoots.P21initial_lower

open ArtinPrimitiveRoots ArtinPrimitiveRoots.P21initial_lower Real in
open Classical in
theorem solution :
    ∃ C_s b₁ : ℝ, 0 < C_s ∧ 0 < b₁ ∧
    ∀ (M c : ℕ) (u : ℤ), 0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → IsCoprime u M →
      (c : ℤ) ∣ u - 1 → IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
    ∀ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ Set.Ioo 1 2 →
      (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) → 0 < ∫ y, Ψ y →
    ∀ b : ℝ, 0 < b → b < b₁ →
    ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      singularSeries M * totalMass M c u Ψ x a / log x *
          (exp (-eulerMascheroniConstant) / b * (1 - C_s * exp (-(1 / 20) / b)) - η) ≤
        ∑' d : ℕ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) :=
  ArtinPrimitiveRoots.P21initial_lower.initial_lower
