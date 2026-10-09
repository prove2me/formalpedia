-- Prove2me | solution 1 for ArtinPrimitiveRoots.mass_conditioned_on_divisor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:14:31.967979+00:00
-- url     : https://prove2.me/submissions/cfe57e5d-5af4-4d26-9469-817939925fc7

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_block_sieve
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution

/-!
# Lemma 12.4: the mass conditioned on a prime divisor
-/

namespace ArtinPrimitiveRoots.BinMass

open Real Finset Filter Topology
open scoped Classical

/-! ## Notation -/

/-- The odd primes up to `W`. -/
noncomputable def Pset (x : ℝ) : Finset ℕ :=
  (range (⌊sieveLevel x⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p)

/-- The sieve product `∏_{2 < p ≤ W} (1 - g_r(p))`. -/
noncomputable def Pr (M : ℕ) (x : ℝ) (r : ℕ) : ℝ :=
  ∏ p ∈ Pset x, (1 - localDensity M r p)

/-- The `W`-rough part of `A_r(n)`. -/
noncomputable def Sf (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r n : ℕ) : ℝ :=
  ∑ Q ∈ range (⌊2 * x⌋₊ + 1),
    if (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧
      n ∣ c * r * Q + 1 ∧ IsRough (sieveLevel x) (c * r * Q + 1))
    then Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0

/-- The hypothesis provided by the block sieve, specialised. -/
def BlockHyp (C₀ B : ℝ) (H : ℕ) : Prop :=
  ∀ (Aset : Finset ℕ) (ω : ℕ → ℝ), (∀ a ∈ Aset, 0 ≤ ω a) →
    ∀ (z : ℝ), 2 ≤ z → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) →
    ∀ bad : ℕ → ℕ → Prop, ∀ X' : ℝ, 0 ≤ X' → ∀ g : ℕ → ℝ,
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - 1 / 2) →
      (∀ v : ℝ, 1 < v → ∑ p ∈ P.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
      |∑ a ∈ Aset.filter (fun a => ∀ p ∈ P, ¬ bad p a), ω a - X' * ∏ p ∈ P, (1 - g p)| ≤
        B * (X' * ∏ p ∈ P, (1 - g p)) * exp (-(H : ℝ)) +
          B * ∑ d ∈ (∏ p ∈ P, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
            |∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a -
              X' * ∏ p ∈ d.primeFactors, g p|

lemma blockHyp_of (C₀ : ℝ) : ∃ H₀ : ℕ, ∃ B : ℝ, ∀ H : ℕ, H₀ ≤ H → Even H → BlockHyp C₀ B H := by
  obtain ⟨⟨H₀, B, h⟩, -⟩ := block_sieve.{0, 0} (1 / 2) C₀ (by norm_num)
  exact ⟨H₀, B, fun H hH he Aset ω hω z hz P hP bad X' hX' g hg hC => h H hH he Aset ω hω z hz P hP bad X' hX' g hg hC⟩

/-! ## Decomposition by group parts -/

lemma tsum_subtype_eq_sum (P : ℕ → Prop) (g : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ k ∉ s, g k = 0) [DecidablePred P] :
    ∑' Q : {Q : ℕ // P Q}, g Q = ∑ k ∈ s, if P k then g k else 0 := by
  rw [show (∑' Q : {Q : ℕ // P Q}, g Q) = ∑' Q : ({Q : ℕ | P Q} : Set ℕ), g Q from rfl,
    _root_.tsum_subtype]
  rw [tsum_eq_sum (s := s)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Set.indicator_apply]
  · intro k hk
    simp [Set.indicator_apply, hs k hk]

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 ≤ mark (1 / 2) x a h := by
  unfold mark
  apply mul_nonneg (zpow_nonneg (by norm_num) _)
  apply prod_nonneg
  intro i _
  apply div_nonneg (Nat.cast_nonneg _)
  unfold groupReciprocalSum
  exact sum_nonneg fun p _ => by positivity

lemma mem_groupPrimes_prime (x : ℝ) {K : ℕ} (a : Fin K → ℝ) {p : ℕ} (hp : p ∈ groupPrimes x a) :
    p.Prime := by
  unfold groupPrimes at hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hp
  exact (Finset.mem_filter.1 hi).2.1

lemma groupPart_dvd (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) (hh : h ≠ 0) :
    groupPart x a h ∣ h := by
  unfold groupPart
  rw [← prod_filter_of_ne (p := fun p => p ∈ h.primeFactors)]
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hh]
    rw [Finsupp.prod, Nat.support_factorization]
    exact prod_dvd_prod_of_subset _ _ _ (fun p hp => (Finset.mem_filter.1 hp).2)
  · intro p _ hne
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h0; rw [h0, pow_zero] at hne; exact hne rfl

lemma groupPart_pos (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 < groupPart x a h := by
  unfold groupPart
  exact prod_pos fun p hp => pow_pos (mem_groupPrimes_prime x a hp).pos _

lemma isGroupInteger_groupPart (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) :
    IsGroupInteger x a (groupPart x a h) := by
  refine ⟨groupPart_pos x a h, fun q hq => ?_⟩
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  unfold groupPart at hqd
  obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
  have := hqp.dvd_of_dvd_pow hqp'
  rw [(Nat.prime_dvd_prime_iff_eq hqp (mem_groupPrimes_prime x a hp)).1 this]
  exact hp

lemma mark_groupPart (q x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) (hh : h ≠ 0) :
    mark q x a (groupPart x a h) = mark q x a h := by
  have key : ∀ i, groupOmega x (a i) (groupPart x a h) = groupOmega x (a i) h := by
    intro i
    unfold groupOmega
    congr 1
    apply filter_congr
    intro p hp
    constructor
    · intro hd; exact hd.trans (groupPart_dvd x a h hh)
    · intro hd
      have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
      have hG : p ∈ groupPrimes x a := by
        unfold groupPrimes; exact Finset.mem_biUnion.2 ⟨i, mem_univ _, hp⟩
      have hpos := hpp.factorization_pos_of_dvd hh hd
      unfold groupPart
      exact (dvd_pow_self p hpos.ne').trans (dvd_prod_of_mem _ hG)
  unfold mark markOmega
  simp only [key]

lemma groupPart_mul_eq (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (r m : ℕ) (hr : IsGroupInteger x a r)
    (hm : m ≠ 0) (hmG : ∀ p ∈ groupPrimes x a, ¬ p ∣ m) : groupPart x a (r * m) = r := by
  have hr0 : r ≠ 0 := hr.1.ne'
  unfold groupPart
  rw [Nat.factorization_mul hr0 hm]
  have h1 : ∀ p ∈ groupPrimes x a, p ^ (r.factorization + m.factorization) p =
      p ^ r.factorization p := by
    intro p hp
    rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (hmG p hp), add_zero]
  rw [Finset.prod_congr rfl h1]
  rw [← Finset.prod_subset (s₁ := r.primeFactors) (fun p hp => hr.2 p hp)]
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hr0]
    rw [Finsupp.prod, Nat.support_factorization]
  · intro p _ hp
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]

lemma psi_ne_zero {Ψ : ℝ → ℝ} (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) {y : ℝ} (h : Ψ y ≠ 0) :
    1 < y ∧ y < 2 :=
  hΨs (subset_tsupport Ψ h)

lemma pmd_eq_sum (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) (r ℓ : ℕ) (hcr : 1 ≤ c * r) :
    predecessorMassDvd M c u Ψ x r ℓ = ∑ Q ∈ range (⌊2 * x⌋₊ + 1),
      if (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧
        ℓ ∣ c * r * Q + 1) then Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0 := by
  unfold predecessorMassDvd
  rw [tsum_subtype_eq_sum _ (fun Q : ℕ => Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x))]
  intro Q hQ
  by_contra hne
  have := (psi_ne_zero hΨs hne).2
  rw [Finset.mem_range, not_lt] at hQ
  have hQ' : 2 * x < Q := Nat.lt_of_floor_lt hQ
  have : (Q : ℝ) ≤ ((c * r * Q + 1 : ℕ) : ℝ) := by
    have : Q ≤ c * r * Q + 1 := by nlinarith
    exact_mod_cast this
  rw [div_lt_iff₀ hx] at *
  linarith

lemma decomp (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hc : c = 2 ∨ c = 4)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (x : ℝ) (hx : 1 < x) {K : ℕ} (a : Fin K → ℝ)
    (hG : ∀ p ∈ groupPrimes x a, 2 < p ∧ (p : ℝ) ≤ x ^ (0.9 : ℝ)) (T : ℕ → Prop)
    [DecidablePred T] :
    ∑' d : ℕ, (if T d then constructionWeight M c u Ψ x a d else 0) =
      ∑ r ∈ (range (⌊2 * x⌋₊ + 1)).filter (IsGroupInteger x a), mark (1 / 2) x a r *
        ∑ Q ∈ range (⌊2 * x⌋₊ + 1),
          if (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧
            T (c * r * Q + 1)) then Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0 := by
  have hx0 : 0 < x := by linarith
  have hc2 : 2 ≤ c := by rcases hc with h | h <;> omega
  set R := range (⌊2 * x⌋₊ + 1) with hR
  have hd_small : ∀ d : ℕ, Ψ (d / x) ≠ 0 → d ∈ R := by
    intro d hd
    have := (psi_ne_zero hΨs hd).2
    rw [div_lt_iff₀ hx0] at this
    rw [hR, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor (by linarith)
  have h1 : ∑' d : ℕ, (if T d then constructionWeight M c u Ψ x a d else 0) =
      ∑ d ∈ R, (if T d then constructionWeight M c u Ψ x a d else 0) := by
    refine tsum_eq_sum fun d hd => ?_
    unfold constructionWeight
    split_ifs
    · by_contra hne
      exact hd (hd_small d (fun h0 => hne (by rw [h0]; ring)))
    · rfl
    · rfl
  set P : ℕ → ℕ → Prop := fun r Q => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
    ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ T (c * r * Q + 1) with hP
  set F : ℕ × ℕ → ℝ := fun rQ => mark (1 / 2) x a rQ.1 *
    if P rQ.1 rQ.2 then Ψ (((c * rQ.1 * rQ.2 + 1 : ℕ) : ℝ) / x) else 0 with hF
  have h2 : ∑ r ∈ R.filter (IsGroupInteger x a), mark (1 / 2) x a r *
      (∑ Q ∈ R, if P r Q then Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) =
      ∑ rQ ∈ R.filter (IsGroupInteger x a) ×ˢ R, F rQ := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
  rw [h1]
  refine Eq.trans ?_ h2.symm
  have hgp : ∀ r Q : ℕ, IsGroupInteger x a r → Q.Prime → x ^ (0.9 : ℝ) < Q →
      groupPart x a (c * r * Q) = r := by
    intro r Q hr hQ hQx
    rw [show c * r * Q = r * (c * Q) by ring]
    refine groupPart_mul_eq x a r (c * Q) hr (Nat.mul_ne_zero (by omega) hQ.ne_zero)
      fun p hp hpd => ?_
    obtain ⟨hp2, hpx⟩ := hG p hp
    have hpp := mem_groupPrimes_prime x a hp
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with h | h
    · have hc4 : c ∣ 4 := by rcases hc with rfl | rfl <;> norm_num
      have : p ∣ 4 := h.trans hc4
      have : p ∣ 2 ^ 2 := by simpa using this
      have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow this)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hpp hQ).mp h
      subst this
      linarith
  symm
  refine Finset.sum_bij_ne_zero (fun rQ _ _ => c * rQ.1 * rQ.2 + 1) ?_ ?_ ?_ ?_
  · intro rQ _ hne
    have hite : (if P rQ.1 rQ.2 then Ψ (((c * rQ.1 * rQ.2 + 1 : ℕ) : ℝ) / x) else 0) ≠ 0 :=
      fun h => hne (by simp only [hF, h, mul_zero])
    have hp1 : P rQ.1 rQ.2 := by by_contra h; exact hite (if_neg h)
    rw [if_pos hp1] at hite
    exact hd_small _ hite
  · intro rQ h₁ hne rQ' h₁' hne' heq
    have hite : (if P rQ.1 rQ.2 then Ψ (((c * rQ.1 * rQ.2 + 1 : ℕ) : ℝ) / x) else 0) ≠ 0 :=
      fun h => hne (by simp only [hF, h, mul_zero])
    have hp1 : P rQ.1 rQ.2 := by by_contra h; exact hite (if_neg h)
    have hite' : (if P rQ'.1 rQ'.2 then Ψ (((c * rQ'.1 * rQ'.2 + 1 : ℕ) : ℝ) / x) else 0) ≠ 0 :=
      fun h => hne' (by simp only [hF, h, mul_zero])
    have hp2 : P rQ'.1 rQ'.2 := by by_contra h; exact hite' (if_neg h)
    simp only [Finset.mem_product, Finset.mem_filter] at h₁ h₁'
    have heq' : c * rQ.1 * rQ.2 = c * rQ'.1 * rQ'.2 := by simpa using heq
    have hr : rQ.1 = rQ'.1 := by
      rw [← hgp rQ.1 rQ.2 h₁.1.2 hp1.1 hp1.2.1, ← hgp rQ'.1 rQ'.2 h₁'.1.2 hp2.1 hp2.2.1, heq']
    have hpos : 0 < c * rQ.1 := Nat.mul_pos (by omega) h₁.1.2.1
    have hQ : rQ.2 = rQ'.2 := by
      rw [← hr] at heq'
      exact Nat.eq_of_mul_eq_mul_left hpos heq'
    exact Prod.ext hr hQ
  · intro d hd hne
    by_cases hT : T d
    swap
    · rw [if_neg hT] at hne; exact absurd rfl hne
    rw [if_pos hT] at hne
    unfold constructionWeight at hne
    by_cases hdc : 2 ≤ d ∧ (d : ℤ) ≡ u [ZMOD M]
    swap
    · rw [if_neg hdc] at hne; exact absurd rfl hne
    rw [if_pos hdc] at hne
    obtain ⟨hd2, hcong⟩ := hdc
    have hΨ : Ψ (d / x) ≠ 0 := fun h => hne (by rw [h]; ring)
    have hpi : predecessorIndicator x a c (d - 1) ≠ 0 := fun h => hne (by rw [h]; ring)
    have hmk : mark (1 / 2) x a (d - 1) ≠ 0 := fun h => hne (by rw [h]; ring)
    unfold predecessorIndicator at hpi
    by_cases hex : ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ (d - 1) / groupPart x a (d - 1) = c * Q
    swap
    · rw [if_neg hex] at hpi; exact absurd rfl hpi
    obtain ⟨Q, hQp, hQx, hQe⟩ := hex
    have hh0 : d - 1 ≠ 0 := by omega
    have hrd := groupPart_dvd x a (d - 1) hh0
    set r := groupPart x a (d - 1) with hr_def
    have hdec : d - 1 = c * r * Q := by
      rw [mul_comm c, mul_assoc, ← hQe, Nat.mul_div_cancel' hrd]
    have hdd : d = c * r * Q + 1 := by omega
    have hdR : d ≤ ⌊2 * x⌋₊ := by
      rw [hR, Finset.mem_range] at hd; omega
    refine ⟨(r, Q), ?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, hR, Finset.mem_range]
      have hr1 : 1 ≤ r := groupPart_pos x a (d - 1)
      have hQ1 : 1 ≤ Q := hQp.one_lt.le
      refine ⟨⟨?_, isGroupInteger_groupPart x a _⟩, ?_⟩
      · have := Nat.mul_le_mul (Nat.mul_le_mul hc2 (le_refl r)) hQ1
        omega
      · have := Nat.mul_le_mul (Nat.mul_le_mul hc2 hr1) (le_refl Q)
        omega
    · simp only [hF]
      rw [if_pos]
      · rw [hr_def, mark_groupPart _ x a _ hh0, ← hdd]
        exact mul_ne_zero hmk hΨ
      · refine ⟨hQp, hQx, ?_, ?_⟩
        · rw [← hdd]; exact hcong
        · rw [← hdd]; exact hT
    · simp [hdd]
  · intro rQ h₁ hne
    have hite : (if P rQ.1 rQ.2 then Ψ (((c * rQ.1 * rQ.2 + 1 : ℕ) : ℝ) / x) else 0) ≠ 0 :=
      fun h => hne (by simp only [hF, h, mul_zero])
    have hp1 : P rQ.1 rQ.2 := by by_contra h; exact hite (if_neg h)
    rw [if_pos hp1] at hite
    simp only [Finset.mem_product, Finset.mem_filter] at h₁
    have hr1 : 1 ≤ rQ.1 := h₁.1.2.1
    have hQ2 := hp1.1.two_le
    simp only [hF, if_pos hp1]
    rw [if_pos hp1.2.2.2]
    unfold constructionWeight
    have := Nat.mul_le_mul (Nat.mul_le_mul hc2 hr1) hQ2
    rw [if_pos ⟨by omega, hp1.2.2.1⟩]
    have hsub : c * rQ.1 * rQ.2 + 1 - 1 = c * rQ.1 * rQ.2 := by omega
    rw [hsub]
    have hg := hgp rQ.1 rQ.2 h₁.1.2 hp1.1 hp1.2.1
    have hpi : predecessorIndicator x a c (c * rQ.1 * rQ.2) = 1 := by
      unfold predecessorIndicator
      rw [if_pos]
      refine ⟨rQ.2, hp1.1, hp1.2.1, ?_⟩
      rw [hg, show c * rQ.1 * rQ.2 = rQ.1 * (c * rQ.2) by ring]
      exact Nat.mul_div_cancel_left _ (by omega)
    have hmk := mark_groupPart (1 / 2) x a (c * rQ.1 * rQ.2) (by positivity)
    rw [hg] at hmk
    rw [hpi, ← hmk]
    push_cast
    ring

lemma pmd_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (r ℓ : ℕ) :
    0 ≤ predecessorMassDvd M c u Ψ x r ℓ :=
  tsum_nonneg fun _ => hΨ0 _

lemma Sf_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (r n : ℕ) :
    0 ≤ Sf M c u Ψ x r n :=
  sum_nonneg fun _ _ => by split_ifs; exacts [hΨ0 _, le_rfl]

/-! ## Local densities and sieve products -/

lemma ld_mul (M r q m : ℕ) (h : Nat.Coprime q m) :
    localDensity M r (q * m) = localDensity M r q * localDensity M r m := by
  unfold localDensity
  by_cases hq : Nat.Coprime q (M * r)
  · by_cases hm : Nat.Coprime m (M * r)
    · rw [if_pos (Nat.Coprime.mul_left hq hm), if_pos hq, if_pos hm, Nat.totient_mul h, Nat.cast_mul,
        one_div_mul_one_div]
    · rw [if_neg (fun h' => hm (Nat.coprime_mul_iff_left.1 h').2), if_neg hm, mul_zero]
  · rw [if_neg (fun h' => hq (Nat.coprime_mul_iff_left.1 h').1), if_neg hq, zero_mul]

lemma ld_one (M r : ℕ) : localDensity M r 1 = 1 := by
  simp [localDensity]

lemma ld_prod_primes (M r : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    localDensity M r (∏ p ∈ S, p) = ∏ p ∈ S, localDensity M r p := by
  induction S using Finset.induction_on with
  | empty => simp [ld_one]
  | insert q S hqS ih =>
    have hq := hS q (mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    rw [prod_insert hqS, prod_insert hqS, ld_mul, ih hS']
    exact Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hq (hS' p hp)).2 (fun h => hqS (h ▸ hp))

lemma ld_sqfree (M r d : ℕ) (hd : Squarefree d) :
    localDensity M r d = ∏ p ∈ d.primeFactors, localDensity M r p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact ld_prod_primes M r _ fun p hp => Nat.prime_of_mem_primeFactors hp

lemma ld_prime (M r p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    0 ≤ localDensity M r p ∧ localDensity M r p ≤ 1 / 2 ∧ localDensity M r p ≤ 2 / p := by
  unfold localDensity
  split_ifs
  · rw [Nat.totient_prime hp]
    have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hc]
    refine ⟨by apply div_nonneg <;> linarith, ?_, ?_⟩
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    · rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · refine ⟨le_rfl, by norm_num, by positivity⟩

lemma mem_Pset {x : ℝ} {p : ℕ} (hp : p ∈ Pset x) : p.Prime ∧ 3 ≤ p := by
  unfold Pset at hp
  rw [mem_filter] at hp
  exact ⟨hp.2.1, hp.2.2⟩

lemma Pr_pos (M : ℕ) (x : ℝ) (r : ℕ) : 0 < Pr M x r := by
  unfold Pr
  refine prod_pos fun p hp => ?_
  obtain ⟨hpp, h3⟩ := mem_Pset hp
  have := (ld_prime M r p hpp h3).2.1
  linarith

lemma prod_one_sub_ge (A : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ A, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∑ p ∈ A, f p ≤ ∏ p ∈ A, (1 - f p) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert q A hqA ih =>
    have hq := hf q (mem_insert_self q A)
    have hA : ∀ p ∈ A, 0 ≤ f p ∧ f p ≤ 1 := fun p hp => hf p (mem_insert_of_mem hp)
    rw [sum_insert hqA, prod_insert hqA]
    have h1 := ih hA
    have h2 : 0 ≤ ∑ p ∈ A, f p := sum_nonneg fun p hp => (hA p hp).1
    have h3 : (1 - f q) * (1 - ∑ p ∈ A, f p) ≤ (1 - f q) * ∏ p ∈ A, (1 - f p) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith only [h3, h2, hq.1]

lemma Pr_bounds (M : ℕ) (x : ℝ) (r : ℕ) (hr : r ≠ 0) :
    Pr M x 1 ≤ Pr M x r ∧ Pr M x r * (1 - ∑ p ∈ r.primeFactors, 2 / (p : ℝ)) ≤ Pr M x 1 := by
  have hld : ∀ p ∈ Pset x, localDensity M r p =
      if p ∣ r then 0 else localDensity M 1 p := by
    intro p hp
    obtain ⟨hpp, -⟩ := mem_Pset hp
    by_cases h2 : p ∣ r
    · rw [if_pos h2]; unfold localDensity
      rw [if_neg]; intro h1
      exact (Nat.Prime.coprime_iff_not_dvd hpp).1
        (Nat.Coprime.coprime_dvd_right (dvd_mul_left r M) h1) h2
    · rw [if_neg h2]; unfold localDensity
      have : Nat.Coprime p (M * r) ↔ Nat.Coprime p (M * 1) := by
        rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
        exact ⟨fun h => ⟨h.1, Nat.coprime_one_right _⟩,
          fun h => ⟨h.1, (Nat.Prime.coprime_iff_not_dvd hpp).2 h2⟩⟩
      simp only [this]
  have hld1 : ∀ p ∈ Pset x, 0 ≤ localDensity M 1 p ∧ localDensity M 1 p ≤ 1 / 2 ∧
      localDensity M 1 p ≤ 2 / p := fun p hp =>
    ld_prime M 1 p (mem_Pset hp).1 (mem_Pset hp).2
  constructor
  · unfold Pr
    apply Finset.prod_le_prod
    · intro p hp; have := (hld1 p hp).2.1; linarith
    · intro p hp
      rw [hld p hp]
      split_ifs
      · linarith [(hld1 p hp).1]
      · exact le_rfl
  · have hsplit : ∀ g : ℕ → ℝ, ∏ p ∈ Pset x, g p =
        (∏ p ∈ (Pset x).filter (· ∣ r), g p) * ∏ p ∈ (Pset x).filter (fun p => ¬ p ∣ r), g p :=
      fun g => (prod_filter_mul_prod_filter_not (Pset x) (· ∣ r) g).symm
    have hPr : Pr M x r = ∏ p ∈ (Pset x).filter (fun p => ¬ p ∣ r), (1 - localDensity M 1 p) := by
      unfold Pr
      rw [hsplit]
      have e1 : ∏ p ∈ (Pset x).filter (· ∣ r), (1 - localDensity M r p) = 1 :=
        prod_eq_one fun p hp => by
          rw [hld p (mem_filter.1 hp).1, if_pos (mem_filter.1 hp).2]; simp
      have e2 : ∏ p ∈ (Pset x).filter (fun p => ¬ p ∣ r), (1 - localDensity M r p) =
          ∏ p ∈ (Pset x).filter (fun p => ¬ p ∣ r), (1 - localDensity M 1 p) :=
        prod_congr rfl fun p hp => by
          rw [hld p (mem_filter.1 hp).1, if_neg (mem_filter.1 hp).2]
      rw [e1, e2, one_mul]
    have hPr1 : Pr M x 1 = (∏ p ∈ (Pset x).filter (· ∣ r), (1 - localDensity M 1 p)) *
        Pr M x r := by
      rw [hPr]; unfold Pr; exact hsplit _
    have hA : 1 - ∑ p ∈ r.primeFactors, 2 / (p : ℝ) ≤
        ∏ p ∈ (Pset x).filter (· ∣ r), (1 - localDensity M 1 p) := by
      refine le_trans ?_ (prod_one_sub_ge _ _ fun p hp => ⟨(hld1 p (mem_filter.1 hp).1).1,
        by linarith [(hld1 p (mem_filter.1 hp).1).2.1]⟩)
      have : ∑ p ∈ (Pset x).filter (· ∣ r), localDensity M 1 p ≤
          ∑ p ∈ r.primeFactors, 2 / (p : ℝ) := by
        refine le_trans (sum_le_sum fun p hp => (hld1 p (mem_filter.1 hp).1).2.2) ?_
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_filter] at hp
          exact Nat.mem_primeFactors.2 ⟨(mem_Pset hp.1).1, hp.2, hr⟩
        · intro p _ _; positivity
      linarith
    rw [hPr1, mul_comm (∏ p ∈ _, _)]
    exact mul_le_mul_of_nonneg_left hA (Pr_pos M x r).le

lemma card_bound (S : Finset ℕ) (m : ℕ) (hm : m ≠ 0) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ m)
    (Y : ℝ) (hY : 0 ≤ Y) (hYp : ∀ p ∈ S, Y ≤ p) : Y ^ S.card ≤ m := by
  have hdvd : ∏ p ∈ S, p ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (hS p hp).1.prime) (fun p hp => (hS p hp).2)
  have hle : ∏ p ∈ S, p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
  calc Y ^ S.card = ∏ p ∈ S, Y := by rw [prod_const]
    _ ≤ ∏ p ∈ S, (p : ℝ) := prod_le_prod (fun _ _ => hY) hYp
    _ = ((∏ p ∈ S, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ m := by exact_mod_cast hle

lemma groupPrime_large (x : ℝ) (hx : 1 ≤ log x) {K : ℕ} (a : Fin K → ℝ)
    (ha : ∀ i, (0.1 : ℝ) < a i) (r : ℕ) (hr : IsGroupInteger x a r) :
    ∀ p ∈ r.primeFactors, exp (log x ^ (0.1 : ℝ)) ≤ p := by
  intro p hp
  have hG := hr.2 p hp
  unfold groupPrimes at hG
  rw [Finset.mem_biUnion] at hG
  obtain ⟨i, _, hi⟩ := hG
  unfold primeGroup at hi
  rw [Finset.mem_filter] at hi
  refine le_trans ?_ hi.2.2
  apply exp_le_exp.2
  exact rpow_le_rpow_of_exponent_le hx (ha i).le

lemma delta_small (x : ℝ) (hL : 1 ≤ log x) {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i)
    (r : ℕ) (hr : IsGroupInteger x a r) (hr2 : (r : ℝ) ≤ 2 * x) :
    ∑ p ∈ r.primeFactors, 2 / (p : ℝ) ≤ 2 * (log (2 * x) / log 2) / exp (log x ^ (0.1 : ℝ)) := by
  set T := exp (log x ^ (0.1 : ℝ))
  have hT : 0 < T := exp_pos _
  have hlarge := groupPrime_large x hL a ha r hr
  have h1 : ∑ p ∈ r.primeFactors, 2 / (p : ℝ) ≤ ∑ p ∈ r.primeFactors, 2 / T :=
    sum_le_sum fun p hp => div_le_div_of_nonneg_left (by norm_num) hT (hlarge p hp)
  rw [sum_const, nsmul_eq_mul] at h1
  have hr0 : r ≠ 0 := hr.1.ne'
  have hcard := card_bound r.primeFactors r hr0
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩) 2
    (by norm_num) (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
  have hx : 0 < 2 * x := lt_of_lt_of_le (by exact_mod_cast hr.1) hr2
  have hlog : (r.primeFactors.card : ℝ) * log 2 ≤ log (2 * x) := by
    rw [← log_pow]
    exact log_le_log (by positivity) (hcard.trans hr2)
  have hc : (r.primeFactors.card : ℝ) ≤ log (2 * x) / log 2 := by
    rw [le_div_iff₀ (log_pos one_lt_two)]; exact hlog
  calc ∑ p ∈ r.primeFactors, 2 / (p : ℝ) ≤ (r.primeFactors.card : ℝ) * (2 / T) := h1
    _ ≤ log (2 * x) / log 2 * (2 / T) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 * (log (2 * x) / log 2) / T := by ring

/-- The telescoping product. -/
lemma telescope (N : ℕ) (hN : 2 ≤ N) :
    ∏ k ∈ Finset.Ico 3 (N + 1), (1 - 1 / ((k : ℝ) - 1) ^ 2) = (N : ℝ) / (2 * ((N : ℝ) - 1)) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [prod_Ico_succ_top (by omega), ih]
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have e : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [e, show (N : ℝ) + 1 - 1 = N by ring]
    have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (N : ℝ) ≠ 0 := by linarith
    field_simp
    ring

lemma partial_ge_half (N : ℕ) :
    1 / 2 ≤ ∏ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hf : ∀ k : ℕ, 3 ≤ k → 0 ≤ 1 - 1 / ((k : ℝ) - 1) ^ 2 ∧ 1 - 1 / ((k : ℝ) - 1) ^ 2 ≤ 1 := by
    intro k hk
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have h4 : (4 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 := by nlinarith
    constructor
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · have : 0 ≤ 1 / ((k : ℝ) - 1) ^ 2 := by positivity
      linarith
  have hsub : (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p) ⊆ Finset.Ico 3 (N + 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    simp only [Finset.mem_Ico]; omega
  have hle : ∏ k ∈ Finset.Ico 3 (N + 1), (1 - 1 / ((k : ℝ) - 1) ^ 2) ≤
      ∏ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [← prod_sdiff hsub]
    have h0 : 0 ≤ ∏ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2) := prod_nonneg fun p hp => (hf p (by
          have := (mem_filter.1 hp).2.2; omega)).1
    have h1 : ∏ k ∈ Finset.Ico 3 (N + 1) \ (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p),
        (1 - 1 / ((k : ℝ) - 1) ^ 2) ≤ 1 := by
      apply prod_le_one
      · intro k hk
        exact (hf k (Finset.mem_Ico.1 (Finset.mem_sdiff.1 hk).1).1).1
      · intro k hk
        exact (hf k (Finset.mem_Ico.1 (Finset.mem_sdiff.1 hk).1).1).2
    nlinarith only [h0, h1]
  rcases Nat.lt_or_ge N 2 with h | h
  · have : (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p) = ∅ := by
      ext p; simp only [mem_filter, mem_range, Finset.notMem_empty, iff_false]; omega
    rw [this, prod_empty]; norm_num
  · refine le_trans ?_ hle
    rw [telescope N h]
    have hN : (2 : ℝ) ≤ N := by exact_mod_cast h
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith

/-! ## The singular series -/

lemma partial_tendsto : Tendsto (fun N : ℕ => ∏ p ∈ (range (N + 1)).filter
    (fun p => p.Prime ∧ 2 < p), (1 - 1 / ((p : ℝ) - 1) ^ 2)) atTop
    (𝓝 (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2))) := by
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ) - 1) ^ 2) := by
      rw [← summable_nat_add_iff 1]
      simp
    exact (h.comp_injective Subtype.val_injective).neg
  have hm : Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    simpa [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hsum
  have hp : Tendsto (fun s : Finset {p : ℕ // p.Prime ∧ 2 < p} =>
      ∏ b ∈ s, (1 - 1 / ((b.1 : ℝ) - 1) ^ 2)) atTop
      (𝓝 (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2))) := hm.hasProd
  have hmono : Tendsto (fun N : ℕ => (range (N + 1)).subtype (fun p => p.Prime ∧ 2 < p))
      atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro a b hab p
      simp only [mem_subtype, mem_range]; omega
    · intro p; exact ⟨p.1, by simp⟩
  refine (hp.comp hmono).congr fun N => ?_
  simp only [Function.comp_apply]
  rw [prod_subtype_eq_prod_filter (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2)]

lemma Tp_ge : 1 / 2 ≤ ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) :=
  ge_of_tendsto partial_tendsto (Eventually.of_forall partial_ge_half)

lemma PiM_pos (M : ℕ) : 0 < ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  refine prod_pos fun p hp => ?_
  have : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2
  have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have : 0 < 1 - 1 / ((p : ℝ) - 1) := by linarith
  positivity

lemma PiM_ge (M : ℕ) : 1 ≤ ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  rw [prod_inv_distrib]
  have hf : ∀ p ∈ M.primeFactors.filter (2 < ·), 0 < 1 - 1 / ((p : ℝ) - 1) ∧
      1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
    intro p hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2
    have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
    constructor <;> linarith
  apply one_le_inv₀ (prod_pos fun p hp => (hf p hp).1) |>.2
  exact prod_le_one (fun p hp => (hf p hp).1.le) (fun p hp => (hf p hp).2)

lemma singular_ge_one (M : ℕ) : 1 ≤ singularSeries M := by
  unfold singularSeries
  have h1 := Tp_ge
  have h2 := PiM_ge M
  have h3 : (1 : ℝ) ≤ 2 * ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    linarith
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ _ := mul_le_mul h3 h2 zero_le_one (by linarith)

lemma mertensProduct_pos (y : ℝ) : 0 < mertensProduct y := by
  unfold mertensProduct
  refine prod_pos fun p hp => ?_
  have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma VM_eq (M : ℕ) (hM : 0 < M) (x : ℝ) (hW2 : 2 ≤ ⌊sieveLevel x⌋₊)
    (hWM : M ≤ ⌊sieveLevel x⌋₊) :
    Pr M x 1 = mertensProduct (sieveLevel x) * (2 * (∏ p ∈ Pset x, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
      ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹) := by
  have hV : mertensProduct (sieveLevel x) = (1 - 1 / 2) * ∏ p ∈ Pset x, (1 - 1 / (p : ℝ)) := by
    unfold mertensProduct Pset
    have : (range (⌊sieveLevel x⌋₊ + 1)).filter Nat.Prime =
        insert 2 ((range (⌊sieveLevel x⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p)) := by
      ext p
      simp only [mem_filter, mem_range, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases (h2.two_le).lt_or_eq with h | h
        · exact Or.inr ⟨h1, h2, h⟩
        · exact Or.inl h.symm
      · rintro (h | ⟨h1, h2, _⟩)
        · subst h; exact ⟨by omega, Nat.prime_two⟩
        · exact ⟨h1, h2⟩
    rw [this, prod_insert (by simp)]
    norm_num
  have hpt : ∀ p ∈ Pset x, 1 - localDensity M 1 p = (1 - 1 / (p : ℝ)) *
      (1 - 1 / ((p : ℝ) - 1) ^ 2) * (if p ∣ M then (1 - 1 / ((p : ℝ) - 1))⁻¹ else 1) := by
    intro p hp
    obtain ⟨hpp, h3⟩ := mem_Pset hp
    have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    have hp2' : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      field_simp; ring
    unfold localDensity
    rw [mul_one]
    by_cases hd : p ∣ M
    · rw [if_neg (fun h => (Nat.Prime.coprime_iff_not_dvd hpp).1 h hd), if_pos hd, hp2']
      field_simp; ring
    · rw [if_pos ((Nat.Prime.coprime_iff_not_dvd hpp).2 hd), if_neg hd, Nat.totient_prime hpp, hc]
      field_simp; ring
  have hfilt : (Pset x).filter (· ∣ M) = M.primeFactors.filter (2 < ·) := by
    ext p
    simp only [Pset, mem_filter, mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp, h2⟩, hd⟩; exact ⟨⟨hp, hd, hM.ne'⟩, h2⟩
    · rintro ⟨⟨hp, hd, _⟩, h2⟩
      exact ⟨⟨by have := Nat.le_of_dvd hM hd; omega, hp, h2⟩, hd⟩
  unfold Pr
  rw [prod_congr rfl hpt, prod_mul_distrib, prod_mul_distrib, prod_ite, prod_const_one, mul_one,
    hfilt, hV]
  ring

lemma tendsto_W : Tendsto sieveLevel atTop atTop :=
  tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop)

lemma rho_tendsto (M : ℕ) (hM : 0 < M) :
    Tendsto (fun x => Pr M x 1 / (singularSeries M * mertensProduct (sieveLevel x)))
      atTop (𝓝 1) := by
  set Tp := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) with hTp
  have hT0 : 0 < Tp := lt_of_lt_of_le (by norm_num) Tp_ge
  have hW : Tendsto (fun x => ⌊sieveLevel x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp tendsto_W
  have h1 := (partial_tendsto.comp hW).div_const Tp
  rw [div_self hT0.ne'] at h1
  refine h1.congr' ?_
  filter_upwards [hW.eventually_ge_atTop (max M 2)] with x hx
  simp only [Function.comp_apply]
  rw [VM_eq M hM x (le_of_max_le_right hx) (le_of_max_le_left hx), singularSeries]
  have hV := mertensProduct_pos (sieveLevel x)
  have hPi := PiM_pos M
  rw [← hTp]
  unfold Pset
  generalize ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹ = P at hPi ⊢
  generalize mertensProduct (sieveLevel x) = V at hV ⊢
  field_simp

lemma telescope_sum (a : ℕ) (ha : 2 ≤ a) (m : ℕ) :
    ∑ k ∈ Finset.Ico a (a + m), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
      1 / ((a : ℝ) - 1) - 1 / (((a + m : ℕ) : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
    push_cast
    ring

lemma telescope_le (a b : ℕ) (ha : 2 ≤ a) :
    ∑ k ∈ Finset.Ico a b, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) ≤ 1 / ((a : ℝ) - 1) := by
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  rcases le_or_gt b a with h | h
  · rw [Finset.Ico_eq_empty_of_le h, sum_empty]; apply div_nonneg <;> linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [telescope_sum a ha m]
    have : (0 : ℝ) ≤ 1 / (((a + m : ℕ) : ℝ) - 1) := by
      push_cast
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      apply div_nonneg <;> linarith
    linarith

lemma sigma_tendsto (γ γ' : ℝ) (hγ : 0 < γ) (hγγ' : γ < γ') :
    Tendsto (fun x : ℝ => ∑ n ∈ (range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
      1 / ((n : ℝ) - 1)) atTop (𝓝 (log (γ' / γ))) := by
  have hm := mertens_prime_reciprocals γ γ' hγ hγγ'
  have hY : Tendsto (fun x : ℝ => ((⌊x ^ γ⌋₊ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hγ))
  have hY0 : Tendsto (fun x : ℝ => 1 / ((⌊x ^ γ⌋₊ : ℕ) : ℝ)) atTop (𝓝 0) := by
    exact hY.inv_tendsto_atTop.congr fun x => by simp [one_div]
  have hD : Tendsto (fun x : ℝ => ∑ n ∈ (range (⌊x ^ γ'⌋₊ + 1)).filter
      (fun n : ℕ => n.Prime ∧ x ^ γ < n), (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hY0 ?_ ?_
    · filter_upwards with x
      refine sum_nonneg fun n hn => ?_
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_filter.1 hn).2.1.two_le
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le <;> linarith
    · filter_upwards [hY.eventually_ge_atTop 1, eventually_ge_atTop (0 : ℝ)] with x hx hx0
      have hpos : 0 ≤ x ^ γ := rpow_nonneg hx0 _
      have h1 : 1 ≤ ⌊x ^ γ⌋₊ := by exact_mod_cast hx
      calc _ ≤ ∑ k ∈ Finset.Ico (⌊x ^ γ⌋₊ + 1) (⌊x ^ γ'⌋₊ + 1),
            (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro n hn
              simp only [mem_filter, mem_range] at hn
              simp only [Finset.mem_Ico]
              refine ⟨?_, hn.1⟩
              have := (Nat.floor_lt hpos).2 hn.2.2
              omega
            · intro k hk _
              have h2 : (2 : ℝ) ≤ k := by
                have := (Finset.mem_Ico.1 hk).1
                exact_mod_cast (show 2 ≤ k by omega)
              rw [sub_nonneg]
              apply one_div_le_one_div_of_le <;> linarith
        _ ≤ 1 / (((⌊x ^ γ⌋₊ + 1 : ℕ) : ℝ) - 1) := telescope_le _ _ (by omega)
        _ = 1 / ((⌊x ^ γ⌋₊ : ℕ) : ℝ) := by push_cast; ring_nf
  have := hm.add hD
  rw [add_zero] at this
  refine this.congr fun x => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-! ## The sieve for one pair -/

lemma prime_block_sum : ∃ C : ℝ, ∀ v : ℝ, 1 < v →
    ∑ p ∈ (range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) / p ≤ C := by
  have h := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hev := h.eventually (eventually_le_nhds (show log (2 / 1) < log (2 / 1) + 1 by linarith))
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  refine ⟨max (log (2 / 1) + 1) (∑ p ∈ range (⌊(max X 1) ^ 2⌋₊ + 1), (1 : ℝ) / p),
    fun v hv => ?_⟩
  by_cases hvX : X ≤ v
  · have := hX v hvX
    simp only [rpow_one, rpow_two] at this
    exact le_max_of_le_left this
  · apply le_max_of_le_right
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      have h1 : v ^ 2 ≤ (max X 1) ^ 2 := by
        have : v ≤ max X 1 := le_max_of_le_left (le_of_lt (not_le.1 hvX))
        exact pow_le_pow_left₀ (by linarith) this 2
      have := Nat.floor_mono h1
      omega
    · intro p _ _; positivity


lemma C0_exists : ∃ C₀ : ℝ, ∀ (M r : ℕ) (x v : ℝ), 1 < v →
    ∑ p ∈ (Pset x).filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), localDensity M r p ≤ C₀ := by
  obtain ⟨C, hC⟩ := prime_block_sum
  refine ⟨2 * C, fun M r x v hv => ?_⟩
  calc ∑ p ∈ (Pset x).filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), localDensity M r p
      ≤ ∑ p ∈ (Pset x).filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), 2 / (p : ℝ) :=
        sum_le_sum fun p hp => (ld_prime M r p (mem_Pset (mem_filter.1 hp).1).1
          (mem_Pset (mem_filter.1 hp).1).2).2.2
    _ ≤ ∑ p ∈ (range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), 2 / (p : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_filter] at hp ⊢
          refine ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hp.2.2)),
            (mem_Pset hp.1).1, hp.2.1⟩
        · intro p _ _; positivity
    _ = 2 * ∑ p ∈ (range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) / p := by
        rw [mul_sum]; exact sum_congr rfl fun p _ => by ring
    _ ≤ 2 * C := by linarith [hC v hv]

lemma sqfree_prodP (x : ℝ) : Squarefree (∏ p ∈ Pset x, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (mem_Pset hp).1.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_Pset hp).1 (mem_Pset hq).1).mpr hpq

lemma dvd_prodP (x : ℝ) {d : ℕ} (hd : d ∣ ∏ p ∈ Pset x, p) : ∀ p ∈ d.primeFactors, p ∈ Pset x := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1
    ((Nat.dvd_of_mem_primeFactors hp).trans hd)
  rwa [(Nat.prime_dvd_prime_iff_eq hpp (mem_Pset hq).1).1 hpq]

lemma Pset_le {x : ℝ} {p : ℕ} (hp : p ∈ Pset x) : (p : ℝ) ≤ sieveLevel x := by
  unfold Pset at hp
  rw [mem_filter, mem_range] at hp
  exact (Nat.le_floor_iff (show (0 : ℝ) ≤ sieveLevel x from (exp_pos _).le)).1 (by omega)

lemma rough_iff (x : ℝ) (m : ℕ) (hm : Odd m) :
    (∀ p ∈ Pset x, ¬ p ∣ m) ↔ IsRough (sieveLevel x) m := by
  constructor
  · intro h
    refine ⟨hm.pos, fun p hp => ?_⟩
    by_contra hle
    push Not at hle
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hpd)
    apply h p _ hpd
    unfold Pset
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hpp, by have := hpp.two_le; omega⟩
  · rintro ⟨hm0, h⟩ p hp hpd
    have := h p (Nat.mem_primeFactors.2 ⟨(mem_Pset hp).1, hpd, hm0.ne'⟩)
    linarith [Pset_le hp]

lemma ld_prime_eq (M r n : ℕ) (hn : n.Prime) (h : Nat.Coprime n (M * r)) :
    localDensity M r n = 1 / ((n : ℝ) - 1) := by
  unfold localDensity
  rw [if_pos h, Nat.totient_prime hn, Nat.cast_sub hn.one_le]
  simp

lemma block_rn (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hc : c = 2 ∨ c = 4) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (C₀ B : ℝ) (H : ℕ) (hBS : BlockHyp C₀ B H)
    (hC₀ : ∀ (M r : ℕ) (x v : ℝ), 1 < v →
      ∑ p ∈ (Pset x).filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), localDensity M r p ≤ C₀)
    (x : ℝ) (hx : 0 < x) (hW : 2 ≤ sieveLevel x) (r n : ℕ) (hr : 1 ≤ r) (hn : n.Prime)
    (hnW : sieveLevel x < n) (hnMr : Nat.Coprime n (M * r)) :
    |Sf M c u Ψ x r n - 1 / ((n : ℝ) - 1) * (predecessorMass M c u Ψ x r * Pr M x r)| ≤
      B * exp (-(H : ℝ)) * (1 / ((n : ℝ) - 1) * (predecessorMass M c u Ψ x r * Pr M x r)) +
        B * ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
            (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)),
          |massRemainder M c u Ψ x r (n * d)| := by
  have hc0 : 0 < c := by rcases hc with h | h <;> omega
  have hcr : 1 ≤ c * r := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hc0.ne' (by omega))
  set R := range (⌊2 * x⌋₊ + 1) with hR
  set A := predecessorMass M c u Ψ x r with hA_def
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => hΨ0 _
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  set X' := 1 / ((n : ℝ) - 1) * A with hX'
  have hX'0 : 0 ≤ X' := mul_nonneg (by apply div_nonneg <;> linarith) hA0
  set ω : ℕ → ℝ := fun Q => if (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
    ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ n ∣ c * r * Q + 1) then
      Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0 with hω
  have hω0 : ∀ Q ∈ R, 0 ≤ ω Q := fun Q _ => by
    simp only [hω]; split_ifs; exacts [hΨ0 _, le_rfl]
  have hodd : ∀ Q : ℕ, Odd (c * r * Q + 1) := fun Q => by
    rcases hc with rfl | rfl
    · exact ⟨r * Q, by ring⟩
    · exact ⟨2 * r * Q, by ring⟩
  have key := hBS R ω hω0 (sieveLevel x) hW (Pset x)
    (fun p hp => ⟨(mem_Pset hp).1, Pset_le hp⟩) (fun p Q => p ∣ c * r * Q + 1) X' hX'0
    (localDensity M r)
    (fun p hp => by
      have := ld_prime M r p (mem_Pset hp).1 (mem_Pset hp).2
      exact ⟨this.1, by linarith [this.2.1]⟩)
    (hC₀ M r x)
  have hS : ∑ Q ∈ R.filter (fun Q => ∀ p ∈ Pset x, ¬ p ∣ c * r * Q + 1), ω Q =
      Sf M c u Ψ x r n := by
    rw [sum_filter]
    unfold Sf
    refine sum_congr rfl fun Q _ => ?_
    have hRo := rough_iff x (c * r * Q + 1) (hodd Q)
    by_cases h1 : ∀ p ∈ Pset x, ¬ p ∣ c * r * Q + 1
    · rw [if_pos h1]
      have h2 := hRo.1 h1
      simp only [hω]
      by_cases h3 : (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧
          n ∣ c * r * Q + 1)
      · rw [if_pos h3, if_pos ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, h2⟩]
      · rw [if_neg h3, if_neg (fun h => h3 ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
    · rw [if_neg h1, if_neg (fun h => h1 (hRo.2 h.2.2.2.2))]
  have hE : ∀ d ∈ (∏ p ∈ Pset x, p).divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)),
      ∑ Q ∈ R.filter (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1), ω Q -
        X' * ∏ p ∈ d.primeFactors, localDensity M r p = massRemainder M c u Ψ x r (n * d) := by
    intro d hd
    have hdd : d ∣ ∏ p ∈ Pset x, p := Nat.dvd_of_mem_divisors (mem_filter.1 hd).1
    have hsq : Squarefree d := (sqfree_prodP x).squarefree_of_dvd hdd
    have hd0 : d ≠ 0 := hsq.ne_zero
    have hpf := dvd_prodP x hdd
    have hnd : ¬ n ∣ d := fun h => by
      have := Pset_le (hpf n (Nat.mem_primeFactors.2 ⟨hn, h, hd0⟩))
      linarith
    have hcop : Nat.Coprime n d := (Nat.Prime.coprime_iff_not_dvd hn).2 hnd
    have hdiv : ∀ m : ℕ, (∀ p ∈ d.primeFactors, p ∣ m) ↔ d ∣ m := by
      intro m
      constructor
      · intro h
        rw [← Nat.prod_primeFactors_of_squarefree hsq]
        exact Finset.prod_primes_dvd m (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) h
      · intro h p hp; exact (Nat.dvd_of_mem_primeFactors hp).trans h
    have hpmd : ∑ Q ∈ R.filter (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1), ω Q =
        predecessorMassDvd M c u Ψ x r (n * d) := by
      rw [pmd_eq_sum M c u Ψ hΨs x hx r (n * d) hcr, sum_filter]
      refine sum_congr rfl fun Q _ => ?_
      simp only [hω, hdiv]
      by_cases h1 : d ∣ c * r * Q + 1
      · rw [if_pos h1]
        by_cases h2 : (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧
            n ∣ c * r * Q + 1)
        · rw [if_pos h2, if_pos ⟨h2.1, h2.2.1, h2.2.2.1, hcop.mul_dvd_of_dvd_of_dvd h2.2.2.2 h1⟩]
        · rw [if_neg h2, if_neg (fun h => h2 ⟨h.1, h.2.1, h.2.2.1,
            (dvd_mul_right n d).trans h.2.2.2⟩)]
      · rw [if_neg h1, if_neg (fun h => h1 ((dvd_mul_left d n).trans h.2.2.2))]
    rw [hpmd, massRemainder, ld_mul M r n d hcop, ld_prime_eq M r n hn hnMr, ld_sqfree M r d hsq,
      hX']
    simp only [predecessorMass, hA_def]
    ring
  have e1 : X' * ∏ p ∈ Pset x, (1 - localDensity M r p) = 1 / ((n : ℝ) - 1) * (A * Pr M x r) := by
    rw [hX', Pr]; ring
  have hsum : ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)),
      |∑ Q ∈ R.filter (fun Q => ∀ p ∈ d.primeFactors, p ∣ c * r * Q + 1), ω Q -
        X' * ∏ p ∈ d.primeFactors, localDensity M r p| =
      ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)),
      |massRemainder M c u Ψ x r (n * d)| := sum_congr rfl fun d hd => by rw [hE d hd]
  beta_reduce at key
  have h1 : |Sf M c u Ψ x r n - X' * ∏ p ∈ Pset x, (1 - localDensity M r p)| ≤
      B * (X' * ∏ p ∈ Pset x, (1 - localDensity M r p)) * exp (-(H : ℝ)) +
        B * ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
            (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)),
          |massRemainder M c u Ψ x r (n * d)| := by
    rw [← hS, ← hsum]
    convert key using 4
    ext; simp
  rw [e1] at h1
  calc _ ≤ _ := h1
    _ = _ := by ring

/-! ## Remainders, counting, tails -/

lemma rem_agg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r : ℕ) (Nset : Finset ℕ) (H : ℕ)
    (Y₁ Y₂ : ℝ) (hW : 2 ≤ sieveLevel x)
    (hN : ∀ n ∈ Nset, n.Prime ∧ sieveLevel x < n ∧ (n : ℝ) ≤ Y₁)
    (hY : Y₁ * sieveLevel x ^ (4 * H + 2) ≤ Y₂) :
    ∑ n ∈ Nset, ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)), |massRemainder M c u Ψ x r (n * d)| ≤
      ∑ ℓ ∈ (range (⌊Y₂⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
        |massRemainder M c u Ψ x r ℓ| := by
  set D := (∏ p ∈ Pset x, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2))
    with hD_def
  have hD : ∀ d ∈ D, d ≠ 0 ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p ∈ Pset x) ∧
      (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2) := by
    intro d hd
    rw [hD_def, mem_filter] at hd
    have hdd : d ∣ ∏ p ∈ Pset x, p := Nat.dvd_of_mem_divisors hd.1
    have hsq : Squarefree d := (sqfree_prodP x).squarefree_of_dvd hdd
    exact ⟨hsq.ne_zero, hsq, dvd_prodP x hdd, hd.2⟩
  have hnd : ∀ n ∈ Nset, ∀ d ∈ D, ¬ n ∣ d := by
    intro n hn d hd h
    have := Pset_le ((hD d hd).2.2.1 n (Nat.mem_primeFactors.2 ⟨(hN n hn).1, h, (hD d hd).1⟩))
    linarith [(hN n hn).2.1]
  have hinj : ∀ a ∈ Nset ×ˢ D, ∀ b ∈ Nset ×ˢ D,
      (fun nd : ℕ × ℕ => nd.1 * nd.2) a = (fun nd : ℕ × ℕ => nd.1 * nd.2) b → a = b := by
    rintro ⟨n, d⟩ ha ⟨n', d'⟩ hb h
    rw [mem_product] at ha hb
    simp only at h
    have hn := (hN n ha.1).1
    have hn' := (hN n' hb.1).1
    have h1 : n ∣ n' * d' := h ▸ dvd_mul_right n d
    rcases hn.dvd_mul.1 h1 with h2 | h2
    · have e : n = n' := (Nat.prime_dvd_prime_iff_eq hn hn').1 h2
      subst e
      have := Nat.eq_of_mul_eq_mul_left hn.pos h
      rw [this]
    · exact absurd h2 (hnd n ha.1 d' hb.2)
  have himg := sum_image (f := fun ℓ => |massRemainder M c u Ψ x r ℓ|) hinj
  calc ∑ n ∈ Nset, ∑ d ∈ D, |massRemainder M c u Ψ x r (n * d)|
      = ∑ nd ∈ Nset ×ˢ D, |massRemainder M c u Ψ x r (nd.1 * nd.2)| := by rw [sum_product]
    _ = ∑ ℓ ∈ (Nset ×ˢ D).image (fun nd : ℕ × ℕ => nd.1 * nd.2),
          |massRemainder M c u Ψ x r ℓ| := himg.symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
      intro ℓ hℓ
      obtain ⟨⟨n, d⟩, hnd', rfl⟩ := mem_image.1 hℓ
      rw [mem_product] at hnd'
      obtain ⟨hnp, hnW, hnY⟩ := hN n hnd'.1
      obtain ⟨hd0, hsq, hpf, hdW⟩ := hD d hnd'.2
      simp only
      rw [mem_filter, mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), ?_, ?_⟩
      · push_cast
        have hY1 : 0 ≤ Y₁ := le_trans (Nat.cast_nonneg n) hnY
        exact le_trans (mul_le_mul hnY hdW (Nat.cast_nonneg d) hY1) hY
      · apply Nat.odd_mul.2
        constructor
        · exact hnp.odd_of_ne_two (by rintro rfl; norm_num at hnW; linarith)
        · apply Nat.not_even_iff_odd.1
          intro he
          have h2 := hpf 2 (Nat.mem_primeFactors.2 ⟨Nat.prime_two, even_iff_two_dvd.1 he, hd0⟩)
          have := (mem_Pset h2).2
          omega
      · exact Nat.squarefree_mul_iff.2 ⟨(Nat.Prime.coprime_iff_not_dvd hnp).2
          (hnd n hnd'.1 d hnd'.2), hnp.squarefree, hsq⟩

lemma count_n (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hc : c = 2 ∨ c = 4) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x γ γ' : ℝ) (hx : 2 ≤ x) (hγ : 0 < γ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ n ∈ (range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n), Sf M c u Ψ x r n ≤
      2 / γ * predecessorMass M c u Ψ x r := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hc0 : 0 < c := by rcases hc with h | h <;> omega
  set N := (range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n) with hN
  set R := range (⌊2 * x⌋₊ + 1)
  set g : ℕ → ℝ := fun Q => if (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
    ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) then Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0 with hg
  have hg0 : ∀ Q, 0 ≤ g Q := fun Q => by simp only [hg]; split_ifs; exacts [hΨ0 _, le_rfl]
  have hA : predecessorMass M c u Ψ x r = ∑ Q ∈ R, g Q := by
    rw [predecessorMass, pmd_eq_sum M c u Ψ hΨs x hx0 r 1
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hc0.ne' (by omega)))]
    refine sum_congr rfl fun Q _ => ?_
    simp only [hg, one_dvd, and_true]
  have hS : ∀ n, Sf M c u Ψ x r n ≤ ∑ Q ∈ R, if n ∣ c * r * Q + 1 then g Q else 0 := by
    intro n
    unfold Sf
    refine sum_le_sum fun Q _ => ?_
    by_cases h1 : (Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧
        n ∣ c * r * Q + 1 ∧ IsRough (sieveLevel x) (c * r * Q + 1))
    · rw [if_pos h1, if_pos h1.2.2.2.1]
      simp only [hg]
      rw [if_pos ⟨h1.1, h1.2.1, h1.2.2.1⟩]
    · rw [if_neg h1]
      split_ifs
      · exact hg0 Q
      · exact le_rfl
  have hcount : ∀ Q ∈ R, ((N.filter (· ∣ c * r * Q + 1)).card : ℝ) * g Q ≤ 2 / γ * g Q := by
    intro Q _
    by_cases hgQ : g Q = 0
    · rw [hgQ]; simp
    apply mul_le_mul_of_nonneg_right _ (hg0 Q)
    have hΨne : Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) ≠ 0 := by
      intro h; apply hgQ; simp only [hg]; split_ifs <;> [exact h; rfl]
    have hm2 : ((c * r * Q + 1 : ℕ) : ℝ) < 2 * x := by
      have := (psi_ne_zero hΨs hΨne).2
      rwa [div_lt_iff₀ hx0] at this
    have hb := card_bound (N.filter (· ∣ c * r * Q + 1)) (c * r * Q + 1) (by omega)
      (fun p hp => ⟨(mem_filter.1 (mem_filter.1 hp).1).2.1, (mem_filter.1 hp).2⟩) (x ^ γ)
      (by positivity) (fun p hp => (mem_filter.1 (mem_filter.1 hp).1).2.2.le)
    set k := (N.filter (· ∣ c * r * Q + 1)).card
    have h1 : x ^ (γ * k) < x ^ (2 : ℝ) := by
      rw [rpow_mul hx0.le, rpow_natCast, rpow_two]
      have : 2 * x ≤ x ^ 2 := by nlinarith
      linarith
    have h2 := (rpow_lt_rpow_left_iff hx1).1 h1
    rw [le_div_iff₀ hγ]
    linarith
  calc ∑ n ∈ N, Sf M c u Ψ x r n
      ≤ ∑ n ∈ N, ∑ Q ∈ R, (if n ∣ c * r * Q + 1 then g Q else 0) := sum_le_sum fun n _ => hS n
    _ = ∑ Q ∈ R, ∑ n ∈ N, (if n ∣ c * r * Q + 1 then g Q else 0) := sum_comm
    _ = ∑ Q ∈ R, ((N.filter (· ∣ c * r * Q + 1)).card : ℝ) * g Q := by
        refine sum_congr rfl fun Q _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ Q ∈ R, 2 / γ * g Q := sum_le_sum hcount
    _ = 2 / γ * predecessorMass M c u Ψ x r := by rw [hA, mul_sum]

lemma tail_le (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hc : c = 2 ∨ c = 4) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x ε : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) :
    ∑ r ∈ ((range (⌊2 * x⌋₊ + 1)).filter (IsGroupInteger x a)).filter (fun r : ℕ => x ^ ε < r),
        mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤
      ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
        mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
  have hc0 : 0 < c := by rcases hc with h | h <;> omega
  set f : ℕ → ℝ := fun r => mark (1 / 2) x a r * predecessorMass M c u Ψ x r with hf
  have hf0 : ∀ r, 0 ≤ f r := fun r =>
    mul_nonneg (mark_nonneg x a r) (tsum_nonneg fun _ => hΨ0 _)
  have hfz : ∀ r ∉ range (⌊2 * x⌋₊ + 1), f r = 0 := by
    intro r hr
    rw [mem_range, not_lt] at hr
    have hr' : 2 * x < r := Nat.lt_of_floor_lt hr
    have hr1 : 1 ≤ r := by
      by_contra h
      have : r = 0 := by omega
      subst this; simp at hr'; linarith
    simp only [hf]
    rw [predecessorMass, pmd_eq_sum M c u Ψ hΨs x hx r 1
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hc0.ne' (by omega)))]
    rw [sum_eq_zero, mul_zero]
    intro Q _
    split_ifs with h
    · by_contra hne
      have h2 := (psi_ne_zero hΨs hne).2
      rw [div_lt_iff₀ hx] at h2
      have : r ≤ c * r * Q + 1 := by
        have := h.1.two_le
        have h3 : 1 * r * 1 ≤ c * r * Q := Nat.mul_le_mul (Nat.mul_le_mul hc0 le_rfl) (by omega)
        omega
      have : (r : ℝ) ≤ ((c * r * Q + 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    · rfl
  have hsum : Summable f := summable_of_ne_finset_zero hfz
  have hsub := hsum.subtype {r : ℕ | IsGroupInteger x a r ∧ x ^ ε < r}
  set G := ((range (⌊2 * x⌋₊ + 1)).filter (IsGroupInteger x a)).filter (fun r : ℕ => x ^ ε < r)
  have e : ∑ r ∈ G, f r = ∑ r ∈ G.subtype (fun r => IsGroupInteger x a r ∧ x ^ ε < r), f r := by
    rw [sum_subtype_eq_sum_filter]
    congr 1
    symm
    apply filter_true_of_mem
    intro r hr
    simp only [G, mem_filter] at hr
    exact ⟨hr.1.2, hr.2⟩
  calc ∑ r ∈ G, f r = _ := e
    _ ≤ ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, f r :=
      hsub.sum_le_tsum _ (fun r _ => hf0 r)

/-! ## Asymptotic helpers -/

lemma mertens_bounds : ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ y, y₀ ≤ y →
    1 / (2 * log y) ≤ mertensProduct y ∧ mertensProduct y ≤ 1 / log y := by
  have h := mertens_product
  have hlt1 : exp (-eulerMascheroniConstant) < 1 :=
    Real.exp_lt_one_iff.2 (by linarith [one_half_lt_eulerMascheroniConstant])
  have hgt : 1 / 2 < exp (-eulerMascheroniConstant) := by
    have h23 : (2 : ℝ) / 3 < log 2 := by linarith [log_two_gt_d9]
    have : exp (2 / 3) < 2 := by
      calc exp (2 / 3) < exp (log 2) := exp_lt_exp.2 h23
        _ = 2 := exp_log (by norm_num)
    have h3 : exp (-(2 / 3)) < exp (-eulerMascheroniConstant) :=
      exp_lt_exp.2 (by linarith [eulerMascheroniConstant_lt_two_thirds])
    rw [exp_neg] at h3
    have : 1 / 2 < (exp (2 / 3))⁻¹ := by
      rw [one_div]; exact inv_strictAnti₀ (exp_pos _) this
    linarith
  have hev := (h.eventually (Ioo_mem_nhds hgt hlt1)).and (eventually_ge_atTop (2 : ℝ))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hev
  refine ⟨max y₀ 2, by linarith [le_max_right y₀ 2], fun y hy => ?_⟩
  obtain ⟨⟨hlo, hhi⟩, hy2⟩ := hy₀ y (le_of_max_le_left hy)
  have hlog : 0 < log y := log_pos (by linarith)
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ hlog]; linarith

lemma ev_exp_rpow (α C : ℝ) (hα : 0 < α) : ∀ᶠ L : ℝ in atTop, C * L ≤ exp (L ^ α) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ (n : ℝ) * α := by
    refine ⟨⌈1 / α⌉₊, ?_⟩
    have := Nat.le_ceil (1 / α)
    rw [div_le_iff₀ hα] at this
    linarith
  have hu := tendsto_rpow_atTop hα
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hu.eventually_ge_atTop (max 1 (|C| * (n + 1).factorial))] with L hL1 hL
  have hu0 : 0 ≤ L ^ α := by positivity
  have hLu : L ≤ (L ^ α) ^ n := by
    rw [← rpow_natCast, ← rpow_mul (by linarith)]
    calc L = L ^ (1 : ℝ) := (rpow_one L).symm
      _ ≤ L ^ (α * n) := rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hfac : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hC : |C| * (n + 1).factorial ≤ L ^ α := le_of_max_le_right hL
  have h1 : C * L ≤ |C| * (L ^ α) ^ n := by
    calc C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| * (L ^ α) ^ n := mul_le_mul_of_nonneg_left hLu (abs_nonneg C)
  have h2 : |C| * (L ^ α) ^ n ≤ (L ^ α) ^ (n + 1) / (n + 1).factorial := by
    rw [le_div_iff₀ hfac, pow_succ]
    have : 0 ≤ (L ^ α) ^ n := by positivity
    nlinarith
  exact h1.trans (h2.trans (pow_div_factorial_le_exp (L ^ α) hu0 (n + 1)))

lemma ev_rpow_le (β c : ℝ) (hβ : β < 1) (hc : 0 < c) : ∀ᶠ L : ℝ in atTop, L ^ β ≤ c * L := by
  have hu := tendsto_rpow_atTop (show 0 < 1 - β by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hu.eventually_ge_atTop (1 / c)] with L hL0 hL
  have e : L = L ^ β * L ^ (1 - β) := by
    rw [← rpow_add hL0]; simp
  have h0 : 0 ≤ L ^ β := by positivity
  calc L ^ β = L ^ β * 1 := (mul_one _).symm
    _ ≤ L ^ β * (c * L ^ (1 - β)) := by
        apply mul_le_mul_of_nonneg_left _ h0
        rw [div_le_iff₀ hc] at hL; linarith
    _ = c * (L ^ β * L ^ (1 - β)) := by ring
    _ = c * L := by rw [← e]


lemma ev_exp_big (ε C : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, C * L ^ 2 ≤ exp (ε * L ^ (0.8 : ℝ)) := by
  have hu := tendsto_rpow_atTop (show (0 : ℝ) < 0.4 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hu.eventually_ge_atTop (6 * |C| / ε ^ 3)]
    with L hL1 hL
  have hL0 : 0 < L := by linarith
  have hy0 : 0 ≤ ε * L ^ (0.8 : ℝ) := by positivity
  have hexp := pow_div_factorial_le_exp (ε * L ^ (0.8 : ℝ)) hy0 3
  have hpow : (ε * L ^ (0.8 : ℝ)) ^ 3 = ε ^ 3 * (L ^ (0.4 : ℝ) * L ^ 2) := by
    rw [mul_pow, ← rpow_natCast (L ^ (0.8 : ℝ)), ← rpow_mul hL0.le, ← rpow_natCast L 2,
      ← rpow_add hL0]
    norm_num
  rw [hpow] at hexp
  have hε3 : 0 < ε ^ 3 := by positivity
  rw [div_le_iff₀ hε3] at hL
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have h1 : C * L ^ 2 ≤ |C| * L ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) hL2
  have h2 : 6 * |C| * L ^ 2 ≤ L ^ (0.4 : ℝ) * ε ^ 3 * L ^ 2 := mul_le_mul_of_nonneg_right hL hL2
  have h3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at hexp
  rw [div_le_iff₀ (by norm_num)] at hexp
  nlinarith only [h1, h2, hexp]

lemma groupPrimes_bound (x : ℝ) (hx0 : 0 < x) (hL : 1 ≤ log x) (h02 : 2 * log x ^ (0.2 : ℝ) ≤ 0.9 * log x)
    {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) :
    ∀ p ∈ groupPrimes x a, 2 < p ∧ (p : ℝ) ≤ x ^ (0.9 : ℝ) := by
  intro p hp
  unfold groupPrimes at hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hp
  unfold primeGroup at hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hp1, hpp, hp2⟩ := hi
  have hLa : 1 ≤ log x ^ a i := one_le_rpow hL (by linarith [(ha i).1])
  constructor
  · have he : (2 : ℝ) < exp (log x ^ a i) :=
      lt_of_lt_of_le (by linarith [exp_one_gt_d9]) (exp_le_exp.2 hLa)
    exact_mod_cast he.trans_le hp2
  · have h1 : (p : ℝ) ≤ exp (2 * log x ^ a i) := by
      have : p ≤ ⌊exp (2 * log x ^ a i)⌋₊ := by omega
      exact (Nat.le_floor_iff (exp_pos _).le).1 this
    have h2 : log x ^ a i ≤ log x ^ (0.2 : ℝ) :=
      rpow_le_rpow_of_exponent_le hL (ha i).2.le
    rw [rpow_def_of_pos hx0]
    refine h1.trans (exp_le_exp.2 ?_)
    linarith

lemma double_sum_bound (N R : Finset ℕ) (m s t : ℕ → ℝ) (S E : ℕ → ℕ → ℝ) (β : ℝ)
    (hm : ∀ r ∈ R, 0 ≤ m r)
    (h : ∀ n ∈ N, ∀ r ∈ R, |S r n - s n * t r| ≤ β * (s n * t r) + E r n) :
    |∑ n ∈ N, ∑ r ∈ R, m r * S r n - (∑ n ∈ N, s n) * ∑ r ∈ R, m r * t r| ≤
      β * ((∑ n ∈ N, s n) * ∑ r ∈ R, m r * t r) + ∑ r ∈ R, m r * ∑ n ∈ N, E r n := by
  have e1 : (∑ n ∈ N, s n) * ∑ r ∈ R, m r * t r = ∑ n ∈ N, ∑ r ∈ R, m r * (s n * t r) := by
    rw [sum_mul_sum]; exact sum_congr rfl fun n _ => sum_congr rfl fun r _ => by ring
  have e2 : ∑ r ∈ R, m r * ∑ n ∈ N, E r n = ∑ n ∈ N, ∑ r ∈ R, m r * E r n := by
    rw [sum_comm]; exact sum_congr rfl fun r _ => by rw [mul_sum]
  have key : ∀ n ∈ N, |∑ r ∈ R, m r * S r n - ∑ r ∈ R, m r * (s n * t r)| ≤
      β * ∑ r ∈ R, m r * (s n * t r) + ∑ r ∈ R, m r * E r n := by
    intro n hn
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r hr => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg (hm r hr)]
    calc m r * |S r n - s n * t r| ≤ m r * (β * (s n * t r) + E r n) :=
          mul_le_mul_of_nonneg_left (h n hn r hr) (hm r hr)
      _ = β * (m r * (s n * t r)) + m r * E r n := by ring
  rw [e1, e2, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum key)

lemma final_numeric (lam η e Z Y σ ρ δ T1 T2 X : ℝ) (hlam : 0 ≤ lam) (hη : 0 < η)
    (he : e = min (1 / 4) (η / (6 * lam + 6))) (hZ : 0 < Z)
    (hσ : |σ - lam| ≤ e) (hρ : |ρ - 1| ≤ e) (hδ : 0 ≤ δ) (hδe : δ ≤ e)
    (hYlo : ρ * (1 - e) * Z ≤ Y) (hYhi : Y * (1 - δ) ≤ ρ * Z)
    (hT1 : |T1 - σ * Y| ≤ e * (σ * Y) + e * Z) (hσ0 : 0 ≤ σ) (hY0 : 0 ≤ Y)
    (hT2 : 0 ≤ T2) (hT2' : T2 ≤ e * Z) (hX : X = T1 + T2) :
    |X - Z * lam| ≤ η * Z := by
  have he0 : 0 < e := by rw [he]; exact lt_min (by norm_num) (div_pos hη (by linarith))
  have he4 : e ≤ 1 / 4 := he ▸ min_le_left _ _
  have heη : e * (6 * lam + 6) ≤ η := by
    have h6 : (0 : ℝ) < 6 * lam + 6 := by linarith
    calc e * (6 * lam + 6) ≤ η / (6 * lam + 6) * (6 * lam + 6) :=
          mul_le_mul_of_nonneg_right (he ▸ min_le_right _ _) h6.le
      _ = η := div_mul_cancel₀ _ h6.ne'
  obtain ⟨hρ1, hρ2⟩ := abs_sub_le_iff.1 hρ
  obtain ⟨hσ1, hσ2⟩ := abs_sub_le_iff.1 hσ
  have hYlo' : (1 - 2 * e) * Z ≤ Y := by
    have : (1 - e) * (1 - e) * Z ≤ ρ * (1 - e) * Z := by
      apply mul_le_mul_of_nonneg_right _ hZ.le
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith only [this, hYlo, mul_nonneg (mul_nonneg he0.le he0.le) hZ.le]
  have hYhi' : Y ≤ (1 + 4 * e) * Z := by
    have h1 : Y * (1 - e) ≤ (1 + e) * Z := by
      have : Y * (1 - e) ≤ Y * (1 - δ) := mul_le_mul_of_nonneg_left (by linarith) hY0
      have : ρ * Z ≤ (1 + e) * Z := mul_le_mul_of_nonneg_right (by linarith) hZ.le
      linarith
    have k1 : (1 + e) * Z ≤ (1 + 4 * e) * Z * (1 - e) := by
      linarith only [mul_nonneg (mul_nonneg he0.le (by linarith : (0 : ℝ) ≤ 2 - 4 * e)) hZ.le]
    exact le_of_mul_le_mul_right (h1.trans k1) (by linarith)
  have hYZ : |Y - Z| ≤ 4 * e * Z := abs_sub_le_iff.2 ⟨by linarith, by linarith only [hYlo', mul_pos he0 hZ]⟩
  have hA : |σ * Y - lam * Z| ≤ e * Y + lam * (4 * e * Z) := by
    have : σ * Y - lam * Z = (σ - lam) * Y + lam * (Y - Z) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hY0]; exact mul_le_mul_of_nonneg_right hσ hY0
    · rw [abs_mul, abs_of_nonneg hlam]; exact mul_le_mul_of_nonneg_left hYZ hlam
  have hB : e * (σ * Y) ≤ e * ((lam + 1) * (2 * Z)) := by
    apply mul_le_mul_of_nonneg_left _ he0.le
    apply mul_le_mul (by linarith) (by linarith only [hYhi', mul_le_mul_of_nonneg_right he4 hZ.le])
      hY0 (by linarith)
  have hC : e * Y ≤ e * (2 * Z) := mul_le_mul_of_nonneg_left (by linarith only [hYhi', mul_le_mul_of_nonneg_right he4 hZ.le]) he0.le
  have hfin : |X - Z * lam| ≤ e * (6 * lam + 6) * Z := by
    have : X - Z * lam = (T1 - σ * Y) + (σ * Y - lam * Z) + T2 := by rw [hX]; ring
    rw [this]
    have h1 := abs_add_le (T1 - σ * Y + (σ * Y - lam * Z)) T2
    have h2 := abs_add_le (T1 - σ * Y) (σ * Y - lam * Z)
    rw [abs_of_nonneg hT2] at h1
    linarith only [h1, h2, hT1, hA, hB, hC, hT2']
  calc |X - Z * lam| ≤ e * (6 * lam + 6) * Z := hfin
    _ ≤ η * Z := mul_le_mul_of_nonneg_right heη hZ.le

end ArtinPrimitiveRoots.BinMass

set_option maxHeartbeats 1000000 in
open ArtinPrimitiveRoots ArtinPrimitiveRoots.BinMass Real Finset Filter Topology Classical in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M)
    (hc : c = 2 ∨ c = 4) (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1)
    (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (K : ℕ) (hK : 1 ≤ K) (a : Fin K → ℝ) (ha : StrictMono a)
    (ha' : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2)
    (κ b : ℝ) (hκ : 0 < κ) (hκ' : κ < 0.01) (hb : 0 < b) (hb' : b < 0.01)
    (γ γ' : ℝ) (hbγ : b ≤ γ) (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
          ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
            constructionWeight M c u Ψ x a d else 0) -
        singularSeries M * totalMass M c u Ψ x a * mertensProduct (sieveLevel x) *
          log (γ' / γ)| ≤
      η * (singularSeries M * totalMass M c u Ψ x a * mertensProduct (sieveLevel x)) := by
  intro η hη
  have hγ : 0 < γ := lt_of_lt_of_le hb hbγ
  set lam := log (γ' / γ) with hlam_def
  have hlam : 0 ≤ lam := (log_pos ((one_lt_div hγ).2 hγγ')).le
  set e := min (1 / 4 : ℝ) (η / (6 * lam + 6)) with he_def
  have he : 0 < e := lt_min (by norm_num) (div_pos hη (by linarith))
  have he4 : e ≤ 1 / 4 := min_le_left _ _
  set ε := min κ γ / 2 with hε_def
  have hmin := lt_min hκ hγ
  have hε : 0 < ε := by simp only [hε_def]; linarith
  have hεκ : ε < κ := by have := min_le_left κ γ; simp only [hε_def]; linarith
  have hεγ : ε < γ := by have := min_le_right κ γ; simp only [hε_def]; linarith
  have hε1 : ε ≤ 1 := by norm_num at hκ'; linarith
  -- the block sieve
  obtain ⟨C₀, hC₀⟩ := C0_exists
  obtain ⟨H₀, B, hB⟩ := blockHyp_of C₀
  set H : ℕ := 2 * (H₀ + ⌈|B| / e⌉₊ + 1) with hH_def
  have hBS : BlockHyp C₀ B H := hB H (by omega) ⟨H₀ + ⌈|B| / e⌉₊ + 1, by omega⟩
  have hBH : B * exp (-(H : ℝ)) ≤ e := by
    have h1 : |B| / e ≤ (H : ℝ) := by
      have h := Nat.le_ceil (|B| / e)
      have : (H : ℝ) = 2 * ((H₀ : ℝ) + ⌈|B| / e⌉₊ + 1) := by simp [hH_def]
      have : (0 : ℝ) ≤ H₀ := Nat.cast_nonneg _
      linarith
    have h2 : (H : ℝ) + 1 ≤ exp H := add_one_le_exp _
    rw [div_le_iff₀ he] at h1
    rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
    have := le_abs_self B
    nlinarith only [h1, h2, this, he, mul_le_mul_of_nonneg_left h2 he.le]
  -- the published inputs
  obtain ⟨hWFD, c₁, c₂, hc₁, -, hlow⟩ :=
    weighted_family_distribution M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  obtain ⟨hWrem, -⟩ := hWFD c u hc hu hcu hcop K hK a ha ha'
  obtain ⟨Crem, xr, hrem⟩ := hWrem κ ε hκ hκ' hε hεκ 2 two_pos
  obtain ⟨xl, hxl⟩ := hlow c u hc hu hcu hcop K hK a ha ha'
  obtain ⟨Ch, hCh⟩ := harmonic_mass M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK
  obtain ⟨xh, hxh⟩ := hCh a ha ha' ε hε
  obtain ⟨y₀, hy₀1, hy₀⟩ := mertens_bounds
  have hρt := rho_tendsto M hM
  have hσt := sigma_tendsto γ γ' hγ hγγ'
  have haK2 : a ⟨K - 1, by omega⟩ < 0.2 := (ha' _).2
  have haK8 : (0.8 : ℝ) ≤ 1 - a ⟨K - 1, by omega⟩ := by norm_num at haK2 ⊢; linarith
  have hc0 : 0 < c := by rcases hc with h | h <;> omega
  -- facts in `L = log x`
  have hL24 := tendsto_rpow_atTop (show (0 : ℝ) < 0.24 by norm_num)
  have hLev : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 * L ^ (0.2 : ℝ) ≤ 0.9 * L ∧
      L ^ (0.24 : ℝ) ≤ b / 2 * L ∧ L ^ (0.24 : ℝ) ≤ κ / (2 * (4 * H + 2)) * L ∧
      L ^ (0.24 : ℝ) ≤ e * c₁ / (2 * |B| * |Crem| + 1) * L ∧
      log y₀ ≤ L ^ (0.24 : ℝ) ∧ log M ≤ L ^ (0.24 : ℝ) ∧ log 2 ≤ L ∧
      8 / e * L ≤ exp (L ^ (0.1 : ℝ)) ∧
      (2 / γ + 1) * |Ch| * 2 / (e * c₁) * L ^ 2 ≤ exp (ε * L ^ (0.8 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1, ev_rpow_le 0.2 0.45 (by norm_num) (by norm_num),
      ev_rpow_le 0.24 (b / 2) (by norm_num) (by positivity),
      ev_rpow_le 0.24 (κ / (2 * (4 * H + 2))) (by norm_num) (by positivity),
      ev_rpow_le 0.24 (e * c₁ / (2 * |B| * |Crem| + 1)) (by norm_num) (by positivity),
      hL24.eventually_ge_atTop (log y₀), hL24.eventually_ge_atTop (log M),
      eventually_ge_atTop (log 2), ev_exp_rpow 0.1 (8 / e) (by norm_num),
      ev_exp_big ε ((2 / γ + 1) * |Ch| * 2 / (e * c₁)) hε] with L h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1, by linarith, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hev : ∀ᶠ x : ℝ in atTop,
      |∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
          ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
            constructionWeight M c u Ψ x a d else 0) -
        singularSeries M * totalMass M c u Ψ x a * mertensProduct (sieveLevel x) *
          log (γ' / γ)| ≤
      η * (singularSeries M * totalMass M c u Ψ x a * mertensProduct (sieveLevel x)) := by
    filter_upwards [tendsto_log_atTop.eventually hLev,
      eventually_ge_atTop (max (max xr xl) (max xh 2)),
      (tendsto_order.1 hρt).1 (1 - e) (by linarith), (tendsto_order.1 hρt).2 (1 + e) (by linarith),
      (tendsto_order.1 hσt).1 (lam - e) (by linarith),
      (tendsto_order.1 hσt).2 (lam + e) (by linarith)] with x hL hx hρ1 hρ2 hσ1 hσ2
    obtain ⟨hL1, hL02, hLb, hLH, hLrem, hLy, hLM, hL2, hLδ, hLtail⟩ := hL
    have hxr : xr ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hxl' : xl ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxh' : xh ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    have hx0 : 0 < x := by linarith
    have hx1 : 1 < x := by linarith
    set L := log x with hL_def
    have hL0 : 0 < L := by linarith
    set w := L ^ (0.24 : ℝ) with hw
    have hW : sieveLevel x = exp w := rfl
    have hw1 : 1 ≤ w := one_le_rpow hL1 (by norm_num)
    have hwL : w ≤ L := by
      calc w ≤ L ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := rpow_one L
    have hW2 : 2 ≤ sieveLevel x := by
      rw [hW]
      exact le_trans (by linarith [exp_one_gt_d9]) (exp_le_exp.2 hw1)
    have hWy : y₀ ≤ sieveLevel x := by
      rw [hW]
      calc y₀ = exp (log y₀) := (exp_log (by linarith)).symm
        _ ≤ exp w := exp_le_exp.2 hLy
    have hWM : (M : ℝ) ≤ sieveLevel x := by
      rw [hW]
      calc (M : ℝ) = exp (log M) := (exp_log (by exact_mod_cast hM)).symm
        _ ≤ exp w := exp_le_exp.2 hLM
    have hxpow : ∀ t : ℝ, x ^ t = exp (t * L) := fun t => by
      rw [rpow_def_of_pos hx0, mul_comm]
    have hxγ : sieveLevel x < x ^ γ := by
      rw [hW, hxpow]
      apply exp_lt_exp.2
      linarith only [hLb, mul_pos (by linarith only [hbγ, hb] : (0 : ℝ) < γ - b / 2) hL0]
    have hxεγ : x ^ ε < x ^ γ := rpow_lt_rpow_of_exponent_lt hx1 hεγ
    have hG := groupPrimes_bound x hx0 hL1 hL02 a ha'
    -- harmonic mass, total mass, Mertens
    obtain ⟨-, -, hJ1, -, -, htail⟩ := hxh x hxh'
    obtain ⟨hX0lo, -⟩ := hxl x hxl'
    have hrem' := hrem x hxr
    set J := harmonicMass x a with hJ_def
    set X0 := totalMass M c u Ψ x a with hX0_def
    set V := mertensProduct (sieveLevel x) with hV_def
    have hV : 1 / (2 * w) ≤ V := by
      have := (hy₀ _ hWy).1
      rwa [hW, log_exp] at this
    have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
    set SM := singularSeries M with hSM_def
    have hSM := singular_ge_one M
    -- the index sets
    set G := (range (⌊2 * x⌋₊ + 1)).filter (IsGroupInteger x a) with hG_def
    set Gle := (range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a) with hGle_def
    set Gt := G.filter (fun r : ℕ => x ^ ε < r) with hGt_def
    set N := (range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n) with hN_def
    have hxε_le : x ^ ε ≤ 2 * x := by
      have : x ^ ε ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1.le hε1
      rw [rpow_one] at this; linarith
    have hGsplit : ∀ f : ℕ → ℝ, ∑ r ∈ G, f r = ∑ r ∈ Gle, f r + ∑ r ∈ Gt, f r := by
      intro f
      rw [← sum_filter_add_sum_filter_not G (fun r => r ≤ ⌊x ^ ε⌋₊)]
      congr 1
      · congr 1
        ext r
        simp only [hG_def, hGle_def, mem_filter, mem_range]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          have := Nat.floor_mono hxε_le
          exact ⟨⟨by omega, h2⟩, by omega⟩
      · congr 1
        ext r
        simp only [hGt_def, mem_filter, not_le]
        rw [Nat.floor_lt (by positivity)]
    have hmark : ∀ r, 0 ≤ mark (1 / 2) x a r := mark_nonneg x a
    have hA0 : ∀ r, 0 ≤ predecessorMass M c u Ψ x r := fun r => pmd_nonneg M c u Ψ hΨ0 x r 1
    have hLHS : ∀ n : ℕ, ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
        constructionWeight M c u Ψ x a d else 0) =
        ∑ r ∈ G, mark (1 / 2) x a r * Sf M c u Ψ x r n := fun n =>
      decomp M c u Ψ hc hΨs x hx1 a hG (fun d => n ∣ d ∧ IsRough (sieveLevel x) d)
    have hX0 : X0 = ∑ r ∈ G, mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
      have := decomp M c u Ψ hc hΨs x hx1 a hG (fun _ => True)
      simp only [if_true, and_true] at this
      rw [hX0_def, totalMass, this]
      refine sum_congr rfl fun r hr => ?_
      have hr1 : 1 ≤ r := (mem_filter.1 hr).2.1
      rw [predecessorMass, pmd_eq_sum M c u Ψ hΨs x hx0 r 1 (Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero hc0.ne' (by omega)))]
      simp only [one_dvd, and_true]
    have hN : ∀ n ∈ N, n.Prime ∧ x ^ γ < n ∧ (n : ℝ) ≤ x ^ γ' := by
      intro n hn
      simp only [hN_def, mem_filter, mem_range] at hn
      exact ⟨hn.2.1, hn.2.2, (Nat.le_floor_iff (by positivity)).1 (by omega)⟩
    -- the decomposition into `T1 + T2`
    set T1 := ∑ n ∈ N, ∑ r ∈ Gle, mark (1 / 2) x a r * Sf M c u Ψ x r n with hT1_def
    set T2 := ∑ n ∈ N, ∑ r ∈ Gt, mark (1 / 2) x a r * Sf M c u Ψ x r n with hT2_def
    have hX : ∑ n ∈ N, ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
        constructionWeight M c u Ψ x a d else 0) = T1 + T2 := by
      rw [hT1_def, hT2_def, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by rw [hLHS n, hGsplit]
    -- the tail
    set tailS := ∑ r ∈ Gt, mark (1 / 2) x a r * predecessorMass M c u Ψ x r with htailS_def
    have htailS0 : 0 ≤ tailS := sum_nonneg fun r _ => mul_nonneg (hmark r) (hA0 r)
    have htailS : tailS ≤ Ch * (x * exp (-ε * L ^ (1 - a ⟨K - 1, by omega⟩))) :=
      (tail_le M c u Ψ hc hΨs hΨ0 x ε hx0 a).trans htail
    have hZlo : c₁ * x * J / (2 * L * w) ≤ SM * X0 * V := by
      have h1 : c₁ * (x * J / L) ≤ X0 := hX0lo
      have hX00 : 0 ≤ X0 := le_trans (by have := hJ1; positivity) h1
      calc c₁ * x * J / (2 * L * w) = c₁ * (x * J / L) * (1 / (2 * w)) := by
            field_simp
        _ ≤ X0 * V := mul_le_mul h1 hV (by positivity) hX00
        _ = 1 * X0 * V := by ring
        _ ≤ SM * X0 * V := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSM hX00) hV0.le
    have htail_small : (2 / γ + 1) * (Ch * (x * exp (-ε * L ^ (1 - a ⟨K - 1, by omega⟩)))) ≤
        e * (c₁ * x / (2 * L * w)) := by
      have hE : exp (ε * L ^ (0.8 : ℝ)) ≤ exp (ε * L ^ (1 - a ⟨K - 1, by omega⟩)) := by
        apply exp_le_exp.2
        apply mul_le_mul_of_nonneg_left _ hε.le
        exact rpow_le_rpow_of_exponent_le hL1 haK8
      set E := exp (ε * L ^ (1 - a ⟨K - 1, by omega⟩))
      have hE0 : 0 < E := exp_pos _
      have h1 : (2 / γ + 1) * |Ch| * 2 * L ^ 2 ≤ e * c₁ * E := by
        have := hLtail.trans hE
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
        linarith only [this]
      rw [neg_mul, exp_neg]
      have hγ0 : 0 ≤ 2 / γ + 1 := by positivity
      calc (2 / γ + 1) * (Ch * (x * E⁻¹)) ≤ (2 / γ + 1) * (|Ch| * (x * E⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _)
              (by positivity)) hγ0
        _ = ((2 / γ + 1) * |Ch| * 2 * L * w) * x / (2 * L * w * E) := by
            field_simp
        _ ≤ (e * c₁ * E) * x / (2 * L * w * E) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ hx0.le
            refine le_trans ?_ h1
            have : (2 / γ + 1) * |Ch| * 2 * L * w ≤ (2 / γ + 1) * |Ch| * 2 * L * L :=
              mul_le_mul_of_nonneg_left hwL (by positivity)
            linarith only [this, h1]
        _ = e * (c₁ * x / (2 * L * w)) := by field_simp
    have hcxw : c₁ * x / (2 * L * w) ≤ c₁ * x * J / (2 * L * w) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ c₁ * x := by positivity
      exact le_mul_of_one_le_right this hJ1
    have htail_X0 : tailS ≤ e * X0 := by
      have h1 : c₁ * x / (2 * L * w) ≤ X0 := by
        calc c₁ * x / (2 * L * w) ≤ c₁ * x * J / (2 * L * w) := hcxw
          _ ≤ c₁ * x * J / L := by
              apply div_le_div_of_nonneg_left (by have := hJ1; positivity) hL0
              linarith only [mul_le_mul_of_nonneg_left (by linarith only [hw1] : 1 ≤ 2 * w) hL0.le]
          _ = c₁ * (x * J / L) := by ring
          _ ≤ X0 := hX0lo
      have h2 : tailS ≤ (2 / γ + 1) * (Ch * (x * exp (-ε * L ^ (1 - a ⟨K - 1, by omega⟩)))) := by
        have h0 : 0 ≤ 2 / γ := by positivity
        have hX : 0 ≤ Ch * (x * exp (-ε * L ^ (1 - a ⟨K - 1, by omega⟩))) := htailS0.trans htailS
        linarith only [htailS, mul_le_mul_of_nonneg_right h0 hX]
      linarith only [h2, htail_small, mul_le_mul_of_nonneg_left h1 he.le]
    -- the bound for `T2`
    have hT2 : 0 ≤ T2 ∧ T2 ≤ e * (SM * X0 * V) := by
      have hT2' : T2 = ∑ r ∈ Gt, mark (1 / 2) x a r * ∑ n ∈ N, Sf M c u Ψ x r n := by
        rw [hT2_def, sum_comm]
        exact sum_congr rfl fun r _ => by rw [mul_sum]
      constructor
      · rw [hT2']
        exact sum_nonneg fun r _ => mul_nonneg (hmark r)
          (sum_nonneg fun n _ => Sf_nonneg M c u Ψ hΨ0 x r n)
      · rw [hT2']
        calc ∑ r ∈ Gt, mark (1 / 2) x a r * ∑ n ∈ N, Sf M c u Ψ x r n
            ≤ ∑ r ∈ Gt, mark (1 / 2) x a r * (2 / γ * predecessorMass M c u Ψ x r) := by
              apply sum_le_sum
              intro r hr
              have hr1 : 1 ≤ r := (mem_filter.1 (mem_filter.1 hr).1).2.1
              exact mul_le_mul_of_nonneg_left
                (count_n M c u Ψ hc hΨs hΨ0 x γ γ' hx2 hγ r hr1) (hmark r)
          _ = 2 / γ * tailS := by rw [htailS_def, mul_sum]; exact sum_congr rfl fun r _ => by ring
          _ ≤ (2 / γ + 1) * (Ch * (x * exp (-ε * L ^ (1 - a ⟨K - 1, by omega⟩)))) := by
              have h0 : 0 ≤ 2 / γ := by positivity
              have hX : 0 ≤ Ch * (x * exp (-ε * L ^ (1 - a ⟨K - 1, by omega⟩))) :=
                htailS0.trans htailS
              linarith only [mul_le_mul_of_nonneg_left htailS h0, hX]
          _ ≤ e * (c₁ * x / (2 * L * w)) := htail_small
          _ ≤ e * (SM * X0 * V) := mul_le_mul_of_nonneg_left (hcxw.trans hZlo) he.le
    -- the main part `T1`
    set σ := ∑ n ∈ N, 1 / ((n : ℝ) - 1) with hσ_def
    set Y := ∑ r ∈ Gle, mark (1 / 2) x a r * (predecessorMass M c u Ψ x r * Pr M x r) with hY_def
    have hNfacts : ∀ n ∈ N, n.Prime ∧ sieveLevel x < n ∧ (n : ℝ) ≤ x ^ γ' := fun n hn =>
      ⟨(hN n hn).1, hxγ.trans (hN n hn).2.1, (hN n hn).2.2⟩
    have hGle : ∀ r ∈ Gle, 1 ≤ r ∧ (r : ℝ) ≤ x ^ ε ∧ IsGroupInteger x a r := by
      intro r hr
      simp only [hGle_def, mem_filter, mem_range] at hr
      exact ⟨hr.2.1, (Nat.le_floor_iff (by positivity)).1 (by omega), hr.2⟩
    have hσ0 : 0 ≤ σ := sum_nonneg fun n hn => by
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (hN n hn).1.two_le
      apply div_nonneg zero_le_one; linarith
    have hY0 : 0 ≤ Y := sum_nonneg fun r _ =>
      mul_nonneg (hmark r) (mul_nonneg (hA0 r) (Pr_pos M x r).le)
    have hY2 : x ^ γ' * sieveLevel x ^ (4 * H + 2) ≤ x ^ (1 / 2 - κ / 2) := by
      rw [hW, ← exp_nat_mul, hxpow, hxpow, ← exp_add]
      apply exp_le_exp.2
      have h1 : (↑(4 * H + 2) : ℝ) * w ≤ κ / 2 * L := by
        have : (↑(4 * H + 2) : ℝ) = 4 * H + 2 := by push_cast; ring
        rw [this]
        have hpos : (0 : ℝ) < 4 * H + 2 := by positivity
        calc (4 * (H : ℝ) + 2) * w ≤ (4 * H + 2) * (κ / (2 * (4 * H + 2)) * L) :=
              mul_le_mul_of_nonneg_left hLH hpos.le
          _ = κ / 2 * L := by field_simp
      linarith only [h1, mul_le_mul_of_nonneg_right hγ' hL0.le]
    set Rsum := ∑ r ∈ Gle, mark (1 / 2) x a r * ∑ n ∈ N, B * ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)), |massRemainder M c u Ψ x r (n * d)|
      with hRsum_def
    have hRsum : Rsum ≤ e * (SM * X0 * V) := by
      have h1 : Rsum ≤ |B| * ∑ r ∈ Gle, mark (1 / 2) x a r *
          ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            |massRemainder M c u Ψ x r ℓ| := by
        rw [hRsum_def, mul_sum]
        apply sum_le_sum
        intro r _
        rw [← mul_sum]
        have hagg := rem_agg M c u Ψ x r N H (x ^ γ') (x ^ (1 / 2 - κ / 2)) hW2 hNfacts hY2
        have h0 : 0 ≤ ∑ n ∈ N, ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
            (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)),
            |massRemainder M c u Ψ x r (n * d)| :=
          sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
        have h2 := mul_le_mul (le_abs_self B) hagg h0 (abs_nonneg B)
        have h3 := mul_le_mul_of_nonneg_left h2 (hmark r)
        linear_combination h3
      have hS0 : 0 ≤ ∑ r ∈ Gle, mark (1 / 2) x a r *
          ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            |massRemainder M c u Ψ x r ℓ| :=
        sum_nonneg fun r _ => mul_nonneg (hmark r) (sum_nonneg fun _ _ => abs_nonneg _)
      have h2 := mul_le_mul_of_nonneg_left hrem' (abs_nonneg B)
      have hL2 : L ^ (-(2 : ℝ)) = 1 / L ^ 2 := by
        rw [rpow_neg hL0.le, rpow_two, one_div]
      have hJ0 : 0 ≤ J := by linarith
      have hxJ : 0 ≤ x * J * L ^ (-(2 : ℝ)) := by rw [hL2]; positivity
      have h3 : |B| * (Crem * (x * J * L ^ (-(2 : ℝ)))) ≤ |B| * |Crem| * (x * J * L ^ (-(2 : ℝ))) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)) hxJ
      have h4 : (2 * |B| * |Crem| + 1) * w ≤ e * c₁ * L := by
        have := mul_le_mul_of_nonneg_left hLrem (show (0 : ℝ) ≤ 2 * |B| * |Crem| + 1 by positivity)
        have e1 : (2 * |B| * |Crem| + 1) * (e * c₁ / (2 * |B| * |Crem| + 1) * L) = e * c₁ * L := by
          field_simp
        linarith only [this, e1]
      have h5 : |B| * |Crem| * (x * J * L ^ (-(2 : ℝ))) ≤ e * (c₁ * x * J / (2 * L * w)) := by
        rw [hL2]
        have hBC : 0 ≤ |B| * |Crem| := by positivity
        have h6 : |B| * |Crem| * (2 * w) ≤ e * c₁ * L := by linarith only [h4, hw1]
        have hxJ' : 0 ≤ x * J := by positivity
        calc |B| * |Crem| * (x * J * (1 / L ^ 2)) = (|B| * |Crem| * (2 * w)) * (x * J) / (2 * L ^ 2 * w) := by
              field_simp
          _ ≤ (e * c₁ * L) * (x * J) / (2 * L ^ 2 * w) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right h6 hxJ'
          _ = e * (c₁ * x * J / (2 * L * w)) := by field_simp
      have h7 := mul_le_mul_of_nonneg_left hZlo he.le
      linarith
    have hT1 : |T1 - σ * Y| ≤ e * (σ * Y) + e * (SM * X0 * V) := by
      have hd := double_sum_bound N Gle (fun r => mark (1 / 2) x a r) (fun n => 1 / ((n : ℝ) - 1))
        (fun r => predecessorMass M c u Ψ x r * Pr M x r) (fun r n => Sf M c u Ψ x r n)
        (fun r n => B * ∑ d ∈ (∏ p ∈ Pset x, p).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ sieveLevel x ^ (4 * H + 2)), |massRemainder M c u Ψ x r (n * d)|)
        (B * exp (-(H : ℝ))) (fun r _ => hmark r) (by
          intro n hn r hr
          obtain ⟨hr1, hrε, -⟩ := hGle r hr
          obtain ⟨hnp, hnW, -⟩ := hNfacts n hn
          have hnMr : Nat.Coprime n (M * r) := by
            refine (Nat.Prime.coprime_iff_not_dvd hnp).2 fun hd => ?_
            rcases hnp.dvd_mul.1 hd with h | h
            · have : (n : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM h
              linarith
            · have : (n : ℝ) ≤ r := by exact_mod_cast Nat.le_of_dvd (by omega) h
              linarith [(hN n hn).2.1]
          exact block_rn M c u Ψ hc hΨs hΨ0 C₀ B H hBS hC₀ x hx0 hW2 r n hr1 hnp hnW hnMr)
      have h1 : B * exp (-(H : ℝ)) * (σ * Y) ≤ e * (σ * Y) :=
        mul_le_mul_of_nonneg_right hBH (mul_nonneg hσ0 hY0)
      have h2 : |T1 - σ * Y| ≤ B * exp (-(H : ℝ)) * (σ * Y) + Rsum := hd
      linarith
    -- the sieve products
    set ρ := Pr M x 1 / (SM * V) with hρ_def
    have hSMV : 0 < SM * V := mul_pos (by linarith) hV0
    have hρZ : ρ * (SM * X0 * V) = Pr M x 1 * X0 := by
      rw [hρ_def, div_mul_eq_mul_div, div_eq_iff hSMV.ne']; ring
    set δ := 2 * (log (2 * x) / log 2) / exp (L ^ (0.1 : ℝ)) with hδ_def
    have hlog2 : (1 : ℝ) / 2 < log 2 := by linarith [log_two_gt_d9]
    have hlog2x : log (2 * x) = log 2 + L := log_mul (by norm_num) hx0.ne'
    have hδ0 : 0 ≤ δ := by
      rw [hδ_def, hlog2x]; have := (log_pos one_lt_two); positivity
    have hδe : δ ≤ e := by
      rw [hδ_def, div_le_iff₀ (exp_pos _)]
      have h1 : log (2 * x) / log 2 ≤ 4 * L := by
        rw [div_le_iff₀ (log_pos one_lt_two), hlog2x]
        linarith only [mul_le_mul_of_nonneg_left hlog2.le hL0.le, hL1, log_two_lt_d9]
      have h2 : 8 * L ≤ e * exp (L ^ (0.1 : ℝ)) := by
        have := hLδ
        rw [div_mul_eq_mul_div, div_le_iff₀ he] at this
        linarith
      linarith
    have hsplitA : ∑ r ∈ Gle, mark (1 / 2) x a r * predecessorMass M c u Ψ x r = X0 - tailS := by
      rw [hX0, hGsplit, htailS_def]; ring
    have hPr1 : 0 < Pr M x 1 := Pr_pos M x 1
    have hYlo : ρ * (1 - e) * (SM * X0 * V) ≤ Y := by
      calc ρ * (1 - e) * (SM * X0 * V) = Pr M x 1 * X0 * (1 - e) := by
            rw [mul_right_comm, hρZ]
        _ ≤ Pr M x 1 * (X0 - tailS) := by
            linarith only [mul_le_mul_of_nonneg_left htail_X0 hPr1.le]
        _ = ∑ r ∈ Gle, mark (1 / 2) x a r * (predecessorMass M c u Ψ x r * Pr M x 1) := by
            rw [← hsplitA, mul_sum]; exact sum_congr rfl fun r _ => by ring
        _ ≤ Y := by
            apply sum_le_sum
            intro r hr
            have hr1 := (hGle r hr).1
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Pr_bounds M x r (by omega)).1 (hA0 r)) (hmark r)
    have hYhi : Y * (1 - δ) ≤ ρ * (SM * X0 * V) := by
      rw [hρZ]
      calc Y * (1 - δ) = ∑ r ∈ Gle, mark (1 / 2) x a r * (predecessorMass M c u Ψ x r *
            (Pr M x r * (1 - δ))) := by
            rw [hY_def, sum_mul]; exact sum_congr rfl fun r _ => by ring
        _ ≤ ∑ r ∈ Gle, mark (1 / 2) x a r * (predecessorMass M c u Ψ x r * Pr M x 1) := by
            apply sum_le_sum
            intro r hr
            obtain ⟨hr1, hrε, hrG⟩ := hGle r hr
            have hds := delta_small x hL1 a (fun i => (ha' i).1) r hrG (hrε.trans hxε_le)
            have hb := (Pr_bounds M x r (by omega)).2
            have hP0 := (Pr_pos M x r).le
            have : Pr M x r * (1 - δ) ≤ Pr M x 1 := by
              refine le_trans ?_ hb
              apply mul_le_mul_of_nonneg_left _ hP0
              rw [hδ_def] at *
              linarith
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (hA0 r)) (hmark r)
        _ = Pr M x 1 * (X0 - tailS) := by
            rw [← hsplitA, mul_sum]; exact sum_congr rfl fun r _ => by ring
        _ ≤ Pr M x 1 * X0 :=
            mul_le_mul_of_nonneg_left (by linarith only [htailS0]) hPr1.le
    have hZ : 0 < SM * X0 * V := lt_of_lt_of_le (by have := hJ1; positivity) hZlo
    have hρ : |ρ - 1| ≤ e := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have hσ : |σ - lam| ≤ e := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    exact final_numeric lam η e (SM * X0 * V) Y σ ρ δ T1 T2 _ hlam hη rfl hZ hσ hρ hδ0 hδe
      hYlo hYhi hT1 hσ0 hY0 hT2.1 hT2.2 hX
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
  exact ⟨x₀, hx₀⟩
