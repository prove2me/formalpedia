-- Prove2me | solution 1 for ArtinPrimitiveRoots.mass_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:12:53.54888+00:00
-- url     : https://prove2.me/submissions/5ede6f42-b5a6-430e-860d-22f810337205

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_single_r_mass

namespace ArtinPrimitiveRoots.WFDasy

section
open Real Finset Filter Topology MeasureTheory
variable {M c : ℕ} {u : ℤ} {Ψ : ℝ → ℝ}

/-- The standing hypotheses on the construction parameters. -/
structure Hyp (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) : Prop where
  hM : 0 < M
  h8 : 8 ∣ M
  hc : c = 2 ∨ c = 4
  hu : IsCoprime u M
  hcu : (c : ℤ) ∣ u - 1
  hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c)
  hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ
  hΨs : tsupport Ψ ⊆ Set.Ioo 1 2
  hΨ0 : ∀ y, 0 ≤ Ψ y
  hΨ1 : ∀ y, Ψ y ≤ 1

lemma Hyp.c_pos (H : Hyp M c u Ψ) : 0 < c := by rcases H.hc with h | h <;> omega

lemma Hyp.c_two (H : Hyp M c u Ψ) : (2 : ℝ) ≤ c := by
  rcases H.hc with h | h <;> subst h <;> norm_num

lemma Hyp.c_four (H : Hyp M c u Ψ) : (c : ℝ) ≤ 4 := by
  rcases H.hc with h | h <;> subst h <;> norm_num

lemma Hyp.c_dvd (H : Hyp M c u Ψ) : c ∣ M := by
  rcases H.hc with h | h <;> subst h
  · exact (show 2 ∣ 8 by norm_num).trans H.h8
  · exact (show 4 ∣ 8 by norm_num).trans H.h8

lemma Hyp.N_pos (H : Hyp M c u Ψ) : 0 < M / c :=
  Nat.div_pos (Nat.le_of_dvd H.hM H.c_dvd) H.c_pos

lemma Hyp.zero_out (H : Hyp M c u Ψ) {y : ℝ} (hy : y ≤ 1 ∨ 2 ≤ y) :
    Ψ y = 0 ∧ deriv Ψ y = 0 := by
  have hn : y ∉ tsupport Ψ := by
    intro h; have := H.hΨs h; rcases hy with hy | hy <;> linarith [this.1, this.2]
  refine ⟨image_eq_zero_of_notMem_tsupport hn, ?_⟩
  by_contra h
  exact hn (support_deriv_subset h)

lemma integral_one_two (H : Hyp M c u Ψ) : ∫ y in (1 : ℝ)..2, Ψ y = ∫ y, Ψ y := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  refine (H.zero_out ?_).1
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
  rcases hy with h | h
  · left; exact h
  · right; exact h.le

end

section
open Real
variable {M c : ℕ} {u : ℤ} {Ψ : ℝ → ℝ}

lemma perR_main (H : Hyp M c u Ψ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.01) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ x ^ θ → Nat.Coprime r M →
      3 < (1 - θ) * log x ∧
      x / (c * r) * (∫ y in (1 : ℝ)..2, Ψ y) / (Nat.totient (M / c) * log x) -
          C * (x / r / log x ^ 2) ≤ predecessorMass M c u Ψ x r ∧
      predecessorMass M c u Ψ x r ≤
        x / (c * r) * (∫ y in (1 : ℝ)..2, Ψ y) / (Nat.totient (M / c) * ((1 - θ) * log x - 3)) +
          C * (x / r / log x ^ 2) :=
  single_r_mass M c u H.hM H.h8 H.hc H.hu H.hcu H.hcop Ψ H.hΨ H.hΨs H.hΨ0 H.hΨ1 θ hθ hθ1

end


section
open Real Finset Filter Topology

/-- A tsum over a subtype with finitely supported weight is a finite sum. -/
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
  classical
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

open Classical in
lemma predecessorMassDvd_eq_sum (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
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

open Classical in
lemma totalMass_decomp (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hc : c = 2 ∨ c = 4)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (x : ℝ) (hx : 1 < x) {K : ℕ} (a : Fin K → ℝ)
    (hG : ∀ p ∈ groupPrimes x a, 2 < p ∧ (p : ℝ) ≤ x ^ (0.9 : ℝ)) :
    totalMass M c u Ψ x a = ∑ r ∈ (range (⌊2 * x⌋₊ + 1)).filter (IsGroupInteger x a),
      mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
  have hx0 : 0 < x := by linarith
  have hc2 : 2 ≤ c := by rcases hc with h | h <;> omega
  set R := range (⌊2 * x⌋₊ + 1) with hR
  have hd_small : ∀ d : ℕ, Ψ (d / x) ≠ 0 → d ∈ R := by
    intro d hd
    have := (psi_ne_zero hΨs hd).2
    rw [div_lt_iff₀ hx0] at this
    rw [hR, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor (by linarith)
  -- the total mass as a finite sum
  have h1 : totalMass M c u Ψ x a = ∑ d ∈ R, constructionWeight M c u Ψ x a d := by
    unfold totalMass
    refine tsum_eq_sum fun d hd => ?_
    unfold constructionWeight
    split_ifs
    · by_contra hne
      exact hd (hd_small d (fun h0 => hne (by rw [h0]; ring)))
    · rfl
  -- the right side as a double sum
  set P : ℕ → ℕ → Prop := fun r Q => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
    ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ 1 ∣ c * r * Q + 1 with hP
  set F : ℕ × ℕ → ℝ := fun rQ => mark (1 / 2) x a rQ.1 *
    if P rQ.1 rQ.2 then Ψ (((c * rQ.1 * rQ.2 + 1 : ℕ) : ℝ) / x) else 0 with hF
  have h2 : ∑ r ∈ R.filter (IsGroupInteger x a), mark (1 / 2) x a r *
      predecessorMass M c u Ψ x r = ∑ rQ ∈ R.filter (IsGroupInteger x a) ×ˢ R, F rQ := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr1 : 1 ≤ r := (Finset.mem_filter.mp hr).2.1
    unfold predecessorMass
    rw [predecessorMassDvd_eq_sum M c u Ψ hΨs x hx0 r 1 (by nlinarith), Finset.mul_sum]
  rw [h1, h2]
  -- the group part of `c r Q`
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
    rw [if_pos hp1] at hite
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
      · refine ⟨hQp, hQx, ?_, one_dvd _⟩
        rw [← hdd]; exact hcong
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

end

section
open Real Finset Filter Topology

/-- Group primes are large but below `x^{0.9}`. -/
lemma group_facts {K : ℕ} (a : Fin K → ℝ) (hai : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) (M : ℕ) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ p ∈ groupPrimes x a,
      (M : ℝ) < p ∧ 2 < p ∧ (p : ℝ) ≤ x ^ (0.9 : ℝ) := by
  set T := log ((M : ℝ) + 2) + 1 with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ log ((M : ℝ) + 2) := log_nonneg (by have := M.cast_nonneg (α := ℝ); linarith)
    linarith
  refine ⟨exp (max (T ^ 10) 32), fun x hx p hp => ?_⟩
  have hL : max (T ^ 10) 32 ≤ log x := by
    rw [← log_exp (max _ _)]; exact log_le_log (exp_pos _) hx
  set L := log x
  have hL32 : 32 ≤ L := le_trans (le_max_right _ _) hL
  have hLT : T ^ 10 ≤ L := le_trans (le_max_left _ _) hL
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  unfold groupPrimes at hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  unfold primeGroup at hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hple, -, hpge⟩ := hi
  have hple' : (p : ℝ) ≤ exp (2 * L ^ a i) :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hple)).trans (Nat.floor_le (exp_pos _).le)
  have hL1 : 1 ≤ L := by linarith
  have hLnn : 0 ≤ L := by linarith
  -- lower bound
  set t := L ^ (0.1 : ℝ) with ht
  have ht10 : t ^ 10 = L := by
    rw [ht, ← rpow_natCast, ← rpow_mul hLnn]; norm_num
  have htT : T ≤ t := by
    have ht0 : 0 ≤ t := rpow_nonneg hLnn _
    by_contra h
    push_neg at h
    have : t ^ 10 < T ^ 10 := pow_lt_pow_left₀ h ht0 (by norm_num)
    linarith
  have hta : t ≤ L ^ a i := rpow_le_rpow_of_exponent_le hL1 (hai i).1.le
  have hexp : (M : ℝ) + 2 < exp t := by
    have h1 : log ((M : ℝ) + 2) < t := by linarith
    have := exp_lt_exp.mpr h1
    rwa [exp_log (by positivity)] at this
  have hlow : (M : ℝ) + 2 < p :=
    lt_of_lt_of_le hexp ((exp_le_exp.mpr hta).trans hpge)
  -- upper bound
  set s := L ^ (0.2 : ℝ) with hs
  have hs5 : s ^ 5 = L := by
    rw [hs, ← rpow_natCast, ← rpow_mul hLnn]; norm_num
  have hs0 : 0 ≤ s := rpow_nonneg hLnn _
  have hs2 : 2 ≤ s := by
    by_contra h
    push_neg at h
    have : s ^ 5 < 2 ^ 5 := pow_lt_pow_left₀ h hs0 (by norm_num)
    linarith
  have has : L ^ a i ≤ s := rpow_le_rpow_of_exponent_le hL1 (hai i).2.le
  have h2s : 2 * s ≤ 0.9 * L := by
    rw [← hs5]
    have h16 : 16 ≤ s ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hs2 4; norm_num at this; linarith
    nlinarith
  have hup : (p : ℝ) ≤ x ^ (0.9 : ℝ) := by
    refine hple'.trans ?_
    rw [rpow_def_of_pos hx0]
    exact exp_le_exp.mpr (by linarith)
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  exact ⟨by linarith, by exact_mod_cast (by linarith : (2 : ℝ) < p), hup⟩

lemma coprime_of_large {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {M : ℕ} (hM : 0 < M)
    (hG : ∀ p ∈ groupPrimes x a, (M : ℝ) < p) {r : ℕ} (hr : IsGroupInteger x a r) :
    Nat.Coprime r M := by
  by_contra h
  obtain ⟨p, hp, hpr, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hmem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpr, hr.1.ne'⟩
  have := hG p (hr.2 p hmem)
  have : p ≤ M := Nat.le_of_dvd hM hpM
  have : (p : ℝ) ≤ M := by exact_mod_cast this
  linarith

/-- A finite partial sum of a nonnegative family with finite support is below the tsum. -/
lemma sum_le_tsum_subtype (P : ℕ → Prop) (g : ℕ → ℝ) (F : Finset ℕ) (hF : ∀ r ∈ F, P r)
    (hg : ∀ r, P r → 0 ≤ g r) (n : ℕ) (hfin : ∀ r, n < r → g r = 0) :
    ∑ r ∈ F, g r ≤ ∑' r : {r : ℕ // P r}, g r := by
  classical
  have hsum : Summable (fun r : {r : ℕ // P r} => g r) := by
    refine summable_of_ne_finset_zero (s := (range (n + 1)).subtype P) fun r hr => ?_
    apply hfin
    by_contra h
    push_neg at h
    exact hr (Finset.mem_subtype.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  have h1 : ∑ r ∈ F, g r = ∑ r ∈ F.subtype P, g r := by
    rw [Finset.sum_subtype_eq_sum_filter (f := g), filter_true_of_mem hF]
  rw [h1]
  exact hsum.sum_le_tsum _ fun r _ => hg r r.2

/-- The harmonic mass splits at `x^θ`. -/
lemma J_split (x θ : ℝ) {K : ℕ} (a : Fin K → ℝ) (F : Finset ℕ)
    (hF : ∀ r, r ∈ F ↔ IsGroupInteger x a r ∧ (r : ℝ) ≤ x ^ θ) (hJ : 0 < harmonicMass x a) :
    harmonicMass x a ≤ ∑ r ∈ F, mark (1 / 2) x a r / r +
      ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ θ < r}, mark (1 / 2) x a r / r := by
  classical
  set g : ℕ → ℝ := fun r => mark (1 / 2) x a r / r with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _)
  set S1 : Set ℕ := {r | IsGroupInteger x a r} with hS1
  set S2 : Set ℕ := {r | IsGroupInteger x a r ∧ x ^ θ < r} with hS2
  have hJ' : harmonicMass x a = ∑' r : S1, g r := rfl
  have hsum : Summable (fun r : S1 => g r) := by
    by_contra h
    rw [hJ', tsum_eq_zero_of_not_summable h] at hJ
    exact lt_irrefl _ hJ
  have hsumI : Summable (S1.indicator g) := (summable_subtype_iff_indicator).mp hsum
  have htail : (∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ θ < r}, g r) =
      ∑' r, S2.indicator g r := by
    rw [show (∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ θ < r}, g r) = ∑' r : S2, g r from rfl,
      _root_.tsum_subtype]
  have hfin : (∑ r ∈ F, g r) = ∑' r, (F : Set ℕ).indicator g r := by
    rw [tsum_eq_sum (s := F)]
    · exact Finset.sum_congr rfl fun r hr => by simp [Set.indicator_apply, hr]
    · intro r hr; simp [Set.indicator_apply, hr]
  have hpt : ∀ r, S1.indicator g r = (F : Set ℕ).indicator g r + S2.indicator g r := by
    intro r
    simp only [Set.indicator_apply, hS1, hS2, Set.mem_setOf_eq, Finset.mem_coe, hF]
    by_cases h1 : IsGroupInteger x a r
    · by_cases h2 : (r : ℝ) ≤ x ^ θ
      · simp [h1, h2, not_lt.mpr h2]
      · simp [h1, h2, lt_of_not_ge h2]
    · simp [h1]
  have hs2 : Summable (S2.indicator g) := by
    refine Summable.of_nonneg_of_le (fun r => Set.indicator_nonneg (fun r _ => hg0 r) r)
      (fun r => ?_) hsumI
    rw [hpt r]
    have := Set.indicator_nonneg (s := (F : Set ℕ)) (fun r _ => hg0 r) r
    linarith
  have hs1 : Summable ((F : Set ℕ).indicator g) := by
    refine summable_of_ne_finset_zero (s := F) fun r hr => ?_
    simp [Set.indicator_apply, hr]
  rw [hJ', _root_.tsum_subtype, htail, hfin, ← hs1.tsum_add hs2]
  exact le_of_eq (tsum_congr hpt)

lemma predecessorMass_eq_zero (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    {x : ℝ} (hx : 0 < x) (hc : 1 ≤ c) {r : ℕ} (hr : 2 * x < r) :
    predecessorMass M c u Ψ x r = 0 := by
  unfold predecessorMass predecessorMassDvd
  refine (tsum_congr fun Q => ?_).trans tsum_zero
  by_contra hne
  have h := (psi_ne_zero hΨs hne).2
  rw [div_lt_iff₀ hx] at h
  have hQ : 1 ≤ Q.1 := Q.2.1.one_lt.le
  have : r ≤ c * r * Q.1 + 1 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hc (le_refl r)) hQ; omega
  have : (r : ℝ) ≤ ((c * r * Q.1 + 1 : ℕ) : ℝ) := by exact_mod_cast this
  linarith

/-- `L e^{-θ L^{0.8}} → 0`. -/
lemma tendsto_L_exp {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun L : ℝ => L * exp (-θ * L ^ (0.8 : ℝ))) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1.25 θ hθ).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.8))
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  simp only [Function.comp_apply]
  rw [← rpow_mul hL]; norm_num

lemma tendsto_exp_L {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun L : ℝ => exp (-θ * L ^ (0.8 : ℝ))) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 θ hθ).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.8))
  refine h1.congr' ?_
  filter_upwards with L
  simp

/-- The final comparison. -/
lemma final_alg {T J S Q Q' E X τ η : ℝ} (hQ : 0 < Q) (hJ : 1 ≤ J) (hSJ : S ≤ J)
    (hJS : J ≤ S + τ) (hη : 0 < η) (hη1 : η ≤ 1) (hlow : S * (Q - E) ≤ T)
    (hup : T ≤ S * (Q' + E) + X) (hE0 : 0 ≤ E) (hEle : E ≤ η / 4 * Q) (hτ : τ ≤ η / 4)
    (hτ0 : 0 ≤ τ) (hX : X ≤ η / 4 * Q) (hQ'0 : 0 ≤ Q') (hQ' : Q' ≤ (1 + η / 4) * Q) :
    |T - J * Q| ≤ η * (J * Q) := by
  have hQE : 0 ≤ Q - E := by nlinarith
  have hJ0 : 0 ≤ J := by linarith
  have hQJ : Q ≤ J * Q := by nlinarith
  rw [abs_le]
  constructor
  · have h1 : (J - τ) * (Q - E) ≤ S * (Q - E) := mul_le_mul_of_nonneg_right (by linarith) hQE
    have h2 : J * E ≤ J * (η / 4 * Q) := mul_le_mul_of_nonneg_left hEle hJ0
    have h3 : τ * Q ≤ η / 4 * Q := mul_le_mul_of_nonneg_right hτ hQ.le
    have h4 : 0 ≤ τ * E := mul_nonneg hτ0 hE0
    have h5 : η / 4 * Q ≤ η / 4 * (J * Q) := mul_le_mul_of_nonneg_left hQJ (by positivity)
    nlinarith
  · have h1 : S * (Q' + E) ≤ J * (Q' + E) := mul_le_mul_of_nonneg_right hSJ (by linarith)
    have h2 : J * Q' ≤ J * ((1 + η / 4) * Q) := mul_le_mul_of_nonneg_left hQ' hJ0
    have h3 : J * E ≤ J * (η / 4 * Q) := mul_le_mul_of_nonneg_left hEle hJ0
    have h5 : η / 4 * Q ≤ η / 4 * (J * Q) := mul_le_mul_of_nonneg_left hQJ (by positivity)
    nlinarith

lemma finite_le_J (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (F : Finset ℕ)
    (hF : ∀ r ∈ F, IsGroupInteger x a r) (hJ : 0 < harmonicMass x a) :
    ∑ r ∈ F, mark (1 / 2) x a r / r ≤ harmonicMass x a := by
  classical
  have hsum : Summable (fun r : {r : ℕ // IsGroupInteger x a r} => mark (1 / 2) x a r / r) := by
    by_contra h
    unfold harmonicMass at hJ
    rw [tsum_eq_zero_of_not_summable h] at hJ
    exact lt_irrefl _ hJ
  have h1 : ∑ r ∈ F, mark (1 / 2) x a r / r =
      ∑ r ∈ F.subtype (IsGroupInteger x a), mark (1 / 2) x a r / r := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun r : ℕ => mark (1 / 2) x a r / (r : ℝ)),
      filter_true_of_mem hF]
  rw [h1]
  exact hsum.sum_le_tsum _ (fun r _ => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _))

end

section
open Real Finset Filter Topology
variable {M c : ℕ} {u : ℤ} {Ψ : ℝ → ℝ}

set_option maxHeartbeats 1000000 in
lemma asymp_le_one (H : Hyp M c u Ψ) (hΨi : 0 < ∫ y, Ψ y) (K : ℕ) (hK : 1 ≤ K)
    (a : Fin K → ℝ) (ha : StrictMono a) (hai : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |totalMass M c u Ψ x a -
          x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) / (c * Nat.totient (M / c) * log x)| ≤
        η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
          (c * Nat.totient (M / c) * log x)) := by
  classical
  set AΨ := ∫ y in (1 : ℝ)..2, Ψ y with hAΨ_def
  have hAΨ : 0 < AΨ := by rw [hAΨ_def, integral_one_two H]; exact hΨi
  set φ : ℝ := (Nat.totient (M / c) : ℝ) with hφ_def
  have hφ : 1 ≤ φ := by
    rw [hφ_def]; exact_mod_cast Nat.totient_pos.mpr H.N_pos
  set cr : ℝ := (c : ℝ) with hcr_def
  have hc2 : 2 ≤ cr := H.c_two
  set θ := min (η / 16) 0.01 with hθ_def
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ1 : θ ≤ 0.01 := min_le_right _ _
  have hθη : θ ≤ η / 16 := min_le_left _ _
  obtain ⟨CJ, hCJ⟩ := harmonic_mass M c u H.hM H.h8 H.hc H.hu H.hcu H.hcop Ψ H.hΨ H.hΨs H.hΨ0
    H.hΨ1 hΨi K hK
  obtain ⟨x₁, h₁⟩ := hCJ a ha hai θ hθ
  obtain ⟨C1, x₂, hC10, h₂⟩ := perR_main H θ hθ hθ1
  obtain ⟨x₃, h₃⟩ := group_facts a hai M
  set iK : Fin K := ⟨K - 1, by omega⟩ with hiK
  have hs : (0.8 : ℝ) ≤ 1 - a iK := by linarith [(hai iK).2]
  -- eventual facts in `L`
  have E1 : ∀ᶠ L : ℝ in atTop, CJ * exp (-θ * L ^ (0.8 : ℝ)) ≤ η / 4 := by
    have := (tendsto_exp_L hθ).const_mul CJ
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  have E2 : ∀ᶠ L : ℝ in atTop,
      CJ * (L * exp (-θ * L ^ (0.8 : ℝ))) ≤ η / 4 * (AΨ / (cr * φ)) := by
    have := (tendsto_L_exp hθ).const_mul CJ
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  have E3 : ∀ᶠ L : ℝ in atTop, C1 * (cr * φ) ≤ η / 4 * AΨ * L :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < η / 4 * AΨ)).eventually_ge_atTop _
  have E4 : ∀ᶠ L : ℝ in atTop, 48 / η + 100 ≤ L := eventually_ge_atTop _
  obtain ⟨x₄, h₄⟩ := eventually_atTop.mp
    (tendsto_log_atTop.eventually (((E1.and E2).and E3).and E4))
  refine ⟨max (max x₁ x₂) (max x₃ (max x₄ 3)), fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : x₄ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx5 : 3 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h₄ x hx4
  set L := log x with hL_def
  have hx0 : 0 < x := by linarith
  have hL100 : 100 ≤ L := by
    have : 0 ≤ 48 / η := by positivity
    linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨-, -, hJ1, hJC, htailJ, htailX⟩ := h₁ x hx1
  set J := harmonicMass x a with hJ_def
  have hCJ0 : 0 ≤ CJ := by linarith
  -- comparing the exponentials
  have hexp : exp (-θ * L ^ (1 - a iK)) ≤ exp (-θ * L ^ (0.8 : ℝ)) := by
    refine exp_le_exp.mpr ?_
    have : L ^ (0.8 : ℝ) ≤ L ^ (1 - a iK) := rpow_le_rpow_of_exponent_le (by linarith) hs
    nlinarith
  have hθe : -θ * L ^ (1 - a iK) = -(θ * L ^ (1 - a iK)) := by ring
  rw [show -θ * log x ^ (1 - a ⟨K - 1, by omega⟩) = -θ * L ^ (1 - a iK) from rfl] at htailJ htailX
  set τ := CJ * exp (-θ * L ^ (0.8 : ℝ)) with hτ_def
  set X := CJ * (x * exp (-θ * L ^ (0.8 : ℝ))) with hX_def
  have hτJ : (∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ θ < r}, mark (1 / 2) x a r / r) ≤ τ :=
    htailJ.trans (mul_le_mul_of_nonneg_left hexp hCJ0)
  have hXX : (∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ θ < r},
      mark (1 / 2) x a r * predecessorMass M c u Ψ x r) ≤ X :=
    htailX.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hx0.le) hCJ0)
  -- the decomposition
  have hG := h₃ x hx3
  have hdec := totalMass_decomp M c u Ψ H.hc H.hΨs x (by linarith) a
    (fun p hp => ⟨(hG p hp).2.1, (hG p hp).2.2⟩)
  set GR := (range (⌊2 * x⌋₊ + 1)).filter (IsGroupInteger x a) with hGR
  set Gs := GR.filter (fun r : ℕ => (r : ℝ) ≤ x ^ θ) with hGs
  set Gb := GR.filter (fun r : ℕ => ¬ (r : ℝ) ≤ x ^ θ) with hGb
  have hxθ : x ^ θ ≤ 2 * x := by
    have : x ^ θ ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [rpow_one] at this; linarith
  have hFs : ∀ r : ℕ, r ∈ Gs ↔ IsGroupInteger x a r ∧ (r : ℝ) ≤ x ^ θ := by
    intro r
    simp only [hGs, hGR, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith)), h1⟩, h2⟩
  set S := ∑ r ∈ Gs, mark (1 / 2) x a r / r with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => div_nonneg (mark_nonneg x a r) (by positivity)
  have hSJ : S ≤ J := finite_le_J x a Gs (fun r hr => ((hFs r).mp hr).1) (by linarith)
  have hJS : J ≤ S + τ := (J_split x θ a Gs hFs (by linarith)).trans (by linarith)
  -- the main quantities
  set Q := x * AΨ / (cr * φ * L) with hQ_def
  set D := (1 - θ) * L - 3 with hD_def
  set Q' := x * AΨ / (cr * φ * D) with hQ'_def
  set E := C1 * (x / L ^ 2) with hE_def
  have hQ : 0 < Q := by positivity
  -- the small `r`
  have hsmall : ∀ r ∈ Gs, 1 ≤ r ∧ (r : ℝ) ≤ x ^ θ ∧ Nat.Coprime r M := by
    intro r hr
    obtain ⟨h1, h2⟩ := (hFs r).mp hr
    exact ⟨h1.1, h2, coprime_of_large H.hM (fun p hp => (hG p hp).1) h1⟩
  have hDpos : 0 < D := by
    obtain ⟨r, hr⟩ : ∃ r, r ∈ Gs ∨ True := ⟨0, Or.inr trivial⟩
    have := mul_le_mul_of_nonneg_right hθ1 hL0.le
    rw [hD_def]; nlinarith
  have hlow : S * (Q - E) ≤ ∑ r ∈ Gs, mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
    rw [hS_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => ?_
    obtain ⟨hr1, hrx, hrM⟩ := hsmall r hr
    obtain ⟨-, hlo, -⟩ := h₂ x hx2 r hr1 hrx hrM
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hid : x / (c * r) * AΨ / (φ * log x) - C1 * (x / r / log x ^ 2) = (Q - E) / r := by
      rw [hQ_def, hE_def, hcr_def, ← hL_def]; field_simp
    rw [hid] at hlo
    calc mark (1 / 2) x a r / r * (Q - E) = mark (1 / 2) x a r * ((Q - E) / r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (mark_nonneg x a r)
  have hup : ∑ r ∈ Gs, mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤ S * (Q' + E) := by
    rw [hS_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => ?_
    obtain ⟨hr1, hrx, hrM⟩ := hsmall r hr
    obtain ⟨-, -, hhi⟩ := h₂ x hx2 r hr1 hrx hrM
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hid : x / (c * r) * AΨ / (φ * ((1 - θ) * log x - 3)) + C1 * (x / r / log x ^ 2) =
        (Q' + E) / r := by
      rw [hQ'_def, hE_def, hcr_def, hD_def, ← hL_def]; field_simp
    rw [hid] at hhi
    calc mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤
          mark (1 / 2) x a r * ((Q' + E) / r) := mul_le_mul_of_nonneg_left hhi (mark_nonneg x a r)
      _ = mark (1 / 2) x a r / r * (Q' + E) := by ring
  -- the large `r`
  have hA0 : ∀ r, 0 ≤ predecessorMass M c u Ψ x r := fun r =>
    tsum_nonneg fun Q => H.hΨ0 _
  have hbig0 : 0 ≤ ∑ r ∈ Gb, mark (1 / 2) x a r * predecessorMass M c u Ψ x r :=
    Finset.sum_nonneg fun r _ => mul_nonneg (mark_nonneg x a r) (hA0 r)
  have hbig : ∑ r ∈ Gb, mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤ X := by
    refine le_trans ?_ hXX
    refine sum_le_tsum_subtype (fun r => IsGroupInteger x a r ∧ x ^ θ < r)
      (fun r => mark (1 / 2) x a r * predecessorMass M c u Ψ x r) Gb ?_
      (fun r _ => mul_nonneg (mark_nonneg x a r) (hA0 r)) ⌊2 * x⌋₊ ?_
    · intro r hr
      simp only [hGb, hGR, Finset.mem_filter] at hr
      exact ⟨hr.1.2, lt_of_not_ge hr.2⟩
    · intro r hr
      have : 2 * x < r := Nat.lt_of_floor_lt hr
      rw [predecessorMass_eq_zero M c u Ψ H.hΨs hx0 H.c_pos this, mul_zero]
  have hT : totalMass M c u Ψ x a =
      ∑ r ∈ Gs, mark (1 / 2) x a r * predecessorMass M c u Ψ x r +
        ∑ r ∈ Gb, mark (1 / 2) x a r * predecessorMass M c u Ψ x r := by
    rw [hdec, hGs, hGb, Finset.sum_filter_add_sum_filter_not]
  -- the comparison inequalities
  have hEle : E ≤ η / 4 * Q := by
    have hid : η / 4 * Q - E = x / (cr * φ * L ^ 2) * (η / 4 * AΨ * L - C1 * (cr * φ)) := by
      rw [hQ_def, hE_def]; field_simp
    have : 0 ≤ x / (cr * φ * L ^ 2) * (η / 4 * AΨ * L - C1 * (cr * φ)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hXle : X ≤ η / 4 * Q := by
    have hid : η / 4 * Q - X =
        x / L * (η / 4 * (AΨ / (cr * φ)) - CJ * (L * exp (-θ * L ^ (0.8 : ℝ)))) := by
      rw [hQ_def, hX_def]; field_simp
    have : 0 ≤ x / L * (η / 4 * (AΨ / (cr * φ)) - CJ * (L * exp (-θ * L ^ (0.8 : ℝ)))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hQ'le : Q' ≤ (1 + η / 4) * Q := by
    have hηL : 48 ≤ η * L := by
      have h := mul_le_mul_of_nonneg_left e4 hη.le
      have : η * (48 / η + 100) = 48 + 100 * η := by field_simp
      nlinarith
    have hθL : θ * L ≤ η / 16 * L := mul_le_mul_of_nonneg_right hθη hL0.le
    have hθηL : θ * (η * L) ≤ 0.01 * (η * L) := mul_le_mul_of_nonneg_right hθ1 (by linarith)
    have hLD : L ≤ (1 + η / 4) * D := by rw [hD_def]; nlinarith
    have hid : (1 + η / 4) * Q - Q' = x * AΨ / (cr * φ) * (((1 + η / 4) * D - L) / (L * D)) := by
      rw [hQ_def, hQ'_def]; field_simp
    have : 0 ≤ x * AΨ / (cr * φ) * (((1 + η / 4) * D - L) / (L * D)) :=
      mul_nonneg (by positivity) (div_nonneg (by linarith) (by positivity))
    linarith
  have hE0 : 0 ≤ E := by positivity
  have hτ0 : 0 ≤ τ := by positivity
  have hQ'0 : 0 ≤ Q' := by positivity
  have hfin := final_alg (T := totalMass M c u Ψ x a) hQ hJ1 hSJ hJS hη hη1
    (by rw [hT]; linarith) (by rw [hT]; linarith) hE0 hEle e1 hτ0 hXle hQ'0 hQ'le
  have hJQ : J * Q = x * J * AΨ / (c * Nat.totient (M / c) * log x) := by
    rw [hQ_def, hcr_def, hφ_def]; ring
  rw [hJQ] at hfin
  exact hfin

end
lemma harmonicMass_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : 0 ≤ harmonicMass x a :=
  tsum_nonneg fun r => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _)

open Real in
theorem mass_asymptotic_proof (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (hΨi : 0 < ∫ y, Ψ y) (K : ℕ) (hK : 1 ≤ K) (a : Fin K → ℝ) (ha : StrictMono a)
    (hai : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) (η : ℝ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |totalMass M c u Ψ x a -
          x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) / (c * Nat.totient (M / c) * log x)| ≤
        η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
          (c * Nat.totient (M / c) * log x)) := by
  have H : Hyp M c u Ψ := ⟨hM, h8, hc, hu, hcu, hcop, hΨ, hΨs, hΨ0, hΨ1⟩
  obtain ⟨x₀, h⟩ := asymp_le_one H hΨi K hK a ha hai (min η 1) (lt_min hη one_pos)
    (min_le_right _ _)
  refine ⟨max x₀ 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  refine (h x (le_trans (le_max_left _ _) hx)).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) ?_)
  have := harmonicMass_nonneg x a
  have : 0 ≤ ∫ y in (1 : ℝ)..2, Ψ y := intervalIntegral.integral_nonneg (by norm_num)
    fun y _ => hΨ0 y
  have : 0 ≤ log x := log_nonneg hx1
  positivity

end ArtinPrimitiveRoots.WFDasy

open ArtinPrimitiveRoots ArtinPrimitiveRoots.WFDasy Real in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (hΨi : 0 < ∫ y, Ψ y) (K : ℕ) (hK : 1 ≤ K) (a : Fin K → ℝ) (ha : StrictMono a)
    (hai : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) (η : ℝ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |totalMass M c u Ψ x a -
          x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) / (c * Nat.totient (M / c) * log x)| ≤
        η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
          (c * Nat.totient (M / c) * log x)) := by
  apply ArtinPrimitiveRoots.WFDasy.mass_asymptotic_proof <;> assumption
