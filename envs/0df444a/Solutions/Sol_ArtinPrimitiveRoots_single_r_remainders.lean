-- Prove2me | solution 1 for ArtinPrimitiveRoots.single_r_remainders
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:13:02.023594+00:00
-- url     : https://prove2.me/submissions/fee30b95-418d-44b7-a2a3-b9cd977a91e9

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_smoothed_bombieri_vinogradov

namespace ArtinPrimitiveRoots.WFDrem

section
open Real Finset Filter Topology MeasureTheory

/-- Indicator of primes in a residue class. -/
noncomputable def primeInd (q v : ℕ) (k : ℕ) : ℝ :=
  if k.Prime ∧ k ≡ v [MOD q] then 1 else 0

/-- Hypotheses on a smooth weight supported in `[T₁, T₂]`. -/
structure Weight (f : ℝ → ℝ) (T₁ T₂ : ℝ) : Prop where
  diff : Differentiable ℝ f
  cont : Continuous (deriv f)
  zero : ∀ t, t ≤ T₁ ∨ T₂ ≤ t → f t = 0 ∧ deriv f t = 0

end

section
open Real Finset

lemma smoothed_bv (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (T₁ T₂ B : ℝ), Weight f T₁ T₂ → 2 ≤ T₁ → T₁ ≤ T₂ →
      (∀ t, |deriv f t| ≤ B) → ∀ (S : Finset ℕ) (v : ℕ → ℕ),
      (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) < T₁ ^ (1 / 2 - η) ∧ Nat.Coprime (v q) q) →
      ∑ q ∈ S, |∑ k ∈ Icc 0 ⌊T₂⌋₊, f k * primeInd q (v q) k - (1 / (Nat.totient q : ℝ)) *
          ∫ t in T₁..T₂, f t * (1 / log t)| ≤
        C * (B * ((T₂ - T₁) * (T₂ * log T₁ ^ (-A')))) := by
  obtain ⟨C, hC0, hC⟩ := smoothed_bombieri_vinogradov A' η hA' hη hη2
  refine ⟨C, hC0, fun f T₁ T₂ B hw h2 h12 hB S v hS => ?_⟩
  convert hC f T₁ T₂ B hw.diff hw.cont hw.zero h2 h12 hB S v hS using 4 with q _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold primeInd
  split_ifs <;> simp

end


section
open Real Finset Filter Topology

lemma le_totient_mul_card (n : ℕ) : n ≤ Nat.totient n * #n.divisors := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      Nat.totient_prime_pow hp hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    have h2 := hp.two_le
    have : p ≤ (p - 1) * (j + 1 + 1) := by
      have : (p - 1) * 2 ≤ (p - 1) * (j + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    calc p ^ j * p ≤ p ^ j * ((p - 1) * (j + 1 + 1)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  | zero => simp
  | one => simp
  | coprime a b _ _ hab ha hb =>
    rw [Nat.totient_mul hab, Nat.Coprime.card_divisors_mul hab]
    calc a * b ≤ (Nat.totient a * #a.divisors) * (Nat.totient b * #b.divisors) :=
          Nat.mul_le_mul ha hb
      _ = _ := by ring

lemma inv_totient_le (n : ℕ) (hn : 1 ≤ n) :
    1 / (Nat.totient n : ℝ) ≤ ∑ x ∈ n.divisorsAntidiagonal, 1 / ((x.1 : ℝ) * x.2) := by
  have hcard : #n.divisorsAntidiagonal = #n.divisors := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have hsum : ∑ x ∈ n.divisorsAntidiagonal, 1 / ((x.1 : ℝ) * x.2) =
      #n.divisors / (n : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => 1 / (n : ℝ)), Finset.sum_const, hcard,
      nsmul_eq_mul]
    · ring
    · intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      rw [← hx.1]; push_cast; rfl
  rw [hsum]
  have hφ : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  have hle : (n : ℝ) ≤ Nat.totient n * #n.divisors := by exact_mod_cast le_totient_mul_card n
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hφ' : (0 : ℝ) < Nat.totient n := by exact_mod_cast hφ
  rw [div_le_div_iff₀ hφ' hn']
  linarith

lemma sum_inv_totient_le (n : ℕ) :
    ∑ ℓ ∈ range (n + 1), 1 / (Nat.totient ℓ : ℝ) ≤ (1 + log n) ^ 2 := by
  have h0 : ∑ ℓ ∈ range (n + 1), 1 / (Nat.totient ℓ : ℝ) =
      ∑ ℓ ∈ Icc 1 n, 1 / (Nat.totient ℓ : ℝ) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.Ico_add_one_right_eq_Icc]
    simp
  rw [h0]
  have h1 : ∑ ℓ ∈ Icc 1 n, 1 / (Nat.totient ℓ : ℝ) ≤
      ∑ ℓ ∈ Icc 1 n, ∑ x ∈ ℓ.divisorsAntidiagonal, 1 / ((x.1 : ℝ) * x.2) :=
    Finset.sum_le_sum fun ℓ hℓ => inv_totient_le ℓ (Finset.mem_Icc.mp hℓ).1
  refine h1.trans ?_
  rw [← Finset.sum_biUnion]
  · have hsub : (Icc 1 n).biUnion Nat.divisorsAntidiagonal ⊆ Icc 1 n ×ˢ Icc 1 n := by
      intro x hx
      simp only [Finset.mem_biUnion, Nat.mem_divisorsAntidiagonal, Finset.mem_Icc] at hx
      obtain ⟨ℓ, ⟨h1, h2⟩, he, hne⟩ := hx
      have ha : 1 ≤ x.1 := Nat.pos_of_ne_zero (by rintro h; rw [h] at he; simp at he; omega)
      have hb : 1 ≤ x.2 := Nat.pos_of_ne_zero (by rintro h; rw [h] at he; simp at he; omega)
      have : x.1 ≤ ℓ := by rw [← he]; exact Nat.le_mul_of_pos_right _ hb
      have : x.2 ≤ ℓ := by rw [← he]; exact Nat.le_mul_of_pos_left _ ha
      simp only [Finset.mem_product, Finset.mem_Icc]
      omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [Finset.sum_product]
    have hH : ∑ a ∈ Icc 1 n, (1 : ℝ) / a ≤ 1 + log n := by
      have := harmonic_le_one_add_log n
      rw [harmonic_eq_sum_Icc] at this
      push_cast at this
      simpa [one_div] using this
    have hH0 : 0 ≤ ∑ a ∈ Icc 1 n, (1 : ℝ) / a := Finset.sum_nonneg fun _ _ => by positivity
    calc ∑ a ∈ Icc 1 n, ∑ b ∈ Icc 1 n, 1 / ((a : ℝ) * b) =
          (∑ a ∈ Icc 1 n, (1 : ℝ) / a) * ∑ b ∈ Icc 1 n, (1 : ℝ) / b := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [one_div_mul_one_div]
      _ ≤ (1 + log n) * (1 + log n) := mul_le_mul hH hH hH0 (hH0.trans hH)
      _ = _ := by ring
  · intro ℓ _ ℓ' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Nat.mem_divisorsAntidiagonal] at hx hx'
    exact hne (hx.1.symm.trans hx'.1)

/-- The predecessor conditions form one reduced class modulo `N ℓ`, `N = M / c`. -/
lemma class_exists (M c : ℕ) (u : ℤ) (hM : 0 < M) (hc0 : 0 < c) (hcM : c ∣ M)
    (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (r ℓ : ℕ) (hℓpos : 0 < ℓ) (hr : Nat.Coprime r M) (hℓ : Nat.Coprime ℓ M) (hℓr : Nat.Coprime ℓ r) :
    ∃ v : ℕ, Nat.Coprime v (M / c * ℓ) ∧ ∀ Q : ℕ,
      ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1) ↔
        Q ≡ v [MOD M / c * ℓ]) := by
  obtain ⟨N, hN⟩ := hcM
  have hcz : (c : ℤ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hNdef : M / c = N := by rw [hN]; exact Nat.mul_div_cancel_left N hc0
  rw [hNdef]
  obtain ⟨w, hw⟩ := hcu
  have hwdef : (u - 1) / c = w := by rw [hw]; exact Int.mul_ediv_cancel_left w hcz
  have hMN : (M : ℤ) / c = N := by rw [hN]; push_cast; exact Int.mul_ediv_cancel_left _ hcz
  rw [hwdef, hMN] at hcop
  -- coprimality facts in ℤ
  have hrN : IsCoprime (r : ℤ) N := by
    have : IsCoprime (r : ℤ) M := Nat.isCoprime_iff_coprime.mpr hr
    rw [hN] at this; push_cast at this; exact this.of_mul_right_right
  have hℓM : IsCoprime (ℓ : ℤ) M := Nat.isCoprime_iff_coprime.mpr hℓ
  have hℓN : IsCoprime (N : ℤ) ℓ := by
    rw [hN] at hℓM; push_cast at hℓM; exact hℓM.of_mul_right_right.symm
  have hcrℓ : IsCoprime ((c : ℤ) * r) ℓ := by
    have h1 : IsCoprime (c : ℤ) ℓ := by
      rw [hN] at hℓM; push_cast at hℓM; exact hℓM.of_mul_right_left.symm
    have h2 : IsCoprime (r : ℤ) ℓ := (Nat.isCoprime_iff_coprime.mpr hℓr).symm
    exact h1.mul_left h2
  obtain ⟨r', k, hr'⟩ := id hrN
  obtain ⟨s, t, hs⟩ := id hcrℓ
  obtain ⟨α, β, hαβ⟩ := id hℓN
  set Q₁ : ℤ := r' * w
  set Q₂ : ℤ := -s
  set Q₀ : ℤ := Q₁ * (β * ℓ) + Q₂ * (α * N)
  -- the two conditions, as divisibilities
  have cond_iff : ∀ Q : ℤ, (((c * r * Q + 1 : ℤ)) ≡ u [ZMOD M] ∧ (ℓ : ℤ) ∣ c * r * Q + 1) ↔
      ((N : ℤ) ∣ r * Q - w ∧ (ℓ : ℤ) ∣ c * r * Q + 1) := by
    intro Q
    rw [Int.modEq_iff_dvd]
    have : u - (c * r * Q + 1) = -(c * (r * Q - w)) := by linear_combination hw
    rw [this, dvd_neg, hN]; push_cast
    rw [mul_dvd_mul_iff_left hcz]
  have hQ₀N : (N : ℤ) ∣ r * Q₀ - w := by
    refine ⟨r * (Q₂ - Q₁) * α - w * k, ?_⟩
    have : β * ℓ = 1 - α * N := by linarith
    simp only [Q₀, Q₁, Q₂, this]
    linear_combination w * hr'
  have hQ₀ℓ : (ℓ : ℤ) ∣ c * r * Q₀ + 1 := by
    refine ⟨c * r * (Q₁ - Q₂) * β + t, ?_⟩
    have : α * N = 1 - β * ℓ := by linarith
    simp only [Q₀, Q₁, Q₂, this]
    linear_combination (-1 : ℤ) * hs
  have key : ∀ Q : ℤ, ((N : ℤ) ∣ r * Q - w ∧ (ℓ : ℤ) ∣ c * r * Q + 1) ↔
      ((N : ℤ) * ℓ ∣ Q - Q₀) := by
    intro Q
    constructor
    · rintro ⟨h1, h2⟩
      have hN' : (N : ℤ) ∣ Q - Q₀ := by
        have : (N : ℤ) ∣ r * (Q - Q₀) := by
          have := dvd_sub h1 hQ₀N; rw [show r * Q - w - (r * Q₀ - w) = (r:ℤ) * (Q - Q₀) by ring]
            at this; exact this
        exact hrN.symm.dvd_of_dvd_mul_left this
      have hℓ' : (ℓ : ℤ) ∣ Q - Q₀ := by
        have : (ℓ : ℤ) ∣ c * r * (Q - Q₀) := by
          have := dvd_sub h2 hQ₀ℓ
          rw [show (c : ℤ) * r * Q + 1 - (c * r * Q₀ + 1) = c * r * (Q - Q₀) by ring] at this
          exact this
        exact hcrℓ.symm.dvd_of_dvd_mul_left this
      exact hℓN.mul_dvd hN' hℓ'
    · intro h
      obtain ⟨m, hm⟩ := h
      constructor
      · have : r * Q - w = r * (N * ℓ * m) + (r * Q₀ - w) := by rw [← hm]; ring
        rw [this]
        exact dvd_add (Dvd.intro (ℓ * m * r) (by ring)) hQ₀N
      · have : (c : ℤ) * r * Q + 1 = c * r * (N * ℓ * m) + (c * r * Q₀ + 1) := by rw [← hm]; ring
        rw [this]
        exact dvd_add (Dvd.intro_left (c * r * N * m) (by ring)) hQ₀ℓ
  -- the representative
  have hm0 : ((N * ℓ : ℕ) : ℤ) ≠ 0 := by
    have hN0 : N ≠ 0 := by rintro rfl; simp at hN; omega
    exact_mod_cast Nat.mul_ne_zero hN0 hℓpos.ne'
  set m : ℤ := ((N * ℓ : ℕ) : ℤ) with hm
  have hmpos : 0 < m := lt_of_le_of_ne (by positivity) (Ne.symm hm0)
  have hvnn : 0 ≤ Q₀ % m := Int.emod_nonneg _ hm0
  refine ⟨(Q₀ % m).toNat, ?_, ?_⟩
  · have hv : (((Q₀ % m).toNat : ℕ) : ℤ) = Q₀ % m := Int.toNat_of_nonneg hvnn
    rw [← Nat.isCoprime_iff_coprime, hv]
    have h1 : IsCoprime Q₀ N := by
      obtain ⟨e, he⟩ := hQ₀N
      have : w = r * Q₀ + N * (-e) := by linarith
      rw [this] at hcop
      exact (IsCoprime.of_add_mul_left_left hcop).of_mul_left_right
    have h2 : IsCoprime Q₀ ℓ := by
      obtain ⟨e, he⟩ := hQ₀ℓ
      have : IsCoprime ((c : ℤ) * r * Q₀) ℓ := ⟨-1, e, by linarith⟩
      exact this.of_mul_left_right
    have h3 : IsCoprime Q₀ m := by rw [hm]; push_cast; exact h1.mul_right h2
    rw [Int.emod_def]
    have := h3.add_mul_left_left (-(Q₀ / m))
    have e : Q₀ - m * (Q₀ / m) = Q₀ + m * -(Q₀ / m) := by ring
    rw [e]; exact this
  · intro Q
    have hv : (((Q₀ % m).toNat : ℕ) : ℤ) = Q₀ - m * (Q₀ / m) := by
      rw [Int.toNat_of_nonneg hvnn, Int.emod_def]
    have e1 : (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1) ↔
        ((c * r * (Q : ℤ) + 1 : ℤ) ≡ u [ZMOD M] ∧ (ℓ : ℤ) ∣ c * r * (Q : ℤ) + 1) := by
      rw [← Int.natCast_dvd_natCast]; push_cast; rfl
    rw [e1, cond_iff, key, Nat.modEq_iff_dvd, hv]
    rw [show (m : ℤ) = (N : ℤ) * ℓ by rw [hm]; push_cast; ring]
    rw [show Q₀ - (N : ℤ) * ℓ * (Q₀ / ((N : ℤ) * ℓ)) - Q =
      -(Q - Q₀) + (N : ℤ) * ℓ * (-(Q₀ / ((N : ℤ) * ℓ))) by ring]
    push_cast
    rw [dvd_add_left (dvd_mul_right _ _), dvd_neg]

lemma class_empty (M c : ℕ) (u : ℤ) (hu : IsCoprime u M) (r ℓ Q : ℕ)
    (h : ¬ Nat.Coprime ℓ (M * r)) :
    ¬ ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧ ℓ ∣ c * r * Q + 1) := by
  rintro ⟨h1, h2⟩
  obtain ⟨p, hp, hpℓ, hpMr⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpd : p ∣ c * r * Q + 1 := hpℓ.trans h2
  rcases (Nat.Prime.dvd_mul hp).mp hpMr with hpM | hpr
  · have h3 : (p : ℤ) ∣ u - ((c * r * Q + 1 : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.mpr hpM).trans (Int.ModEq.dvd h1)
    have h4 : (p : ℤ) ∣ ((c * r * Q + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    have h5 : (p : ℤ) ∣ u := by have := dvd_add h3 h4; simpa using this
    have h6 : (p : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hpM
    have := hu.isUnit_of_dvd' h5 h6
    rw [Int.isUnit_iff] at this
    have := hp.two_le
    omega
  · have : p ∣ c * r * Q := Dvd.dvd.mul_right (Dvd.dvd.mul_left hpr c) Q
    have := (Nat.dvd_add_right this).mp hpd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

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

lemma psi_ne_zero {Ψ : ℝ → ℝ} (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) {y : ℝ} (h : Ψ y ≠ 0) :
    1 < y ∧ y < 2 :=
  hΨs (subset_tsupport Ψ h)

end

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

lemma Hyp.diff (H : Hyp M c u Ψ) : Differentiable ℝ Ψ :=
  H.hΨ.differentiable (by simp)

lemma Hyp.cont_deriv (H : Hyp M c u Ψ) : Continuous (deriv Ψ) :=
  H.hΨ.continuous_deriv (by simp)

lemma Hyp.zero_out (H : Hyp M c u Ψ) {y : ℝ} (hy : y ≤ 1 ∨ 2 ≤ y) :
    Ψ y = 0 ∧ deriv Ψ y = 0 := by
  have hn : y ∉ tsupport Ψ := by
    intro h; have := H.hΨs h; rcases hy with hy | hy <;> linarith [this.1, this.2]
  refine ⟨image_eq_zero_of_notMem_tsupport hn, ?_⟩
  by_contra h
  exact hn (support_deriv_subset h)

lemma Hyp.deriv_bound (H : Hyp M c u Ψ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |deriv Ψ y| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    H.cont_deriv.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 ⟨le_rfl, by norm_num⟩)
  refine ⟨B, hB0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (1 : ℝ) 2
  · exact hB y hy
  · have : y < 1 ∨ 2 < y := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy; tauto
    rw [(H.zero_out (by rcases this with h | h; left; linarith; right; linarith)).2]
    simpa using hB0

/-- The weight `t ↦ Ψ((c r t + 1)/x)`. -/
noncomputable def wt (c : ℕ) (Ψ : ℝ → ℝ) (x : ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  Ψ ((c * r * t + 1) / x)

lemma wt_hasDerivAt (H : Hyp M c u Ψ) (x : ℝ) (r : ℕ) (t : ℝ) :
    HasDerivAt (wt c Ψ x r) (deriv Ψ ((c * r * t + 1) / x) * (c * r / x)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (c * r * t + 1) / x) (c * r / x) t := by
    have := (((hasDerivAt_id t).const_mul ((c : ℝ) * r)).add_const 1).div_const x
    simpa using this
  exact (H.diff _).hasDerivAt.comp t h1

lemma wt_deriv (H : Hyp M c u Ψ) (x : ℝ) (r : ℕ) :
    deriv (wt c Ψ x r) = fun t => deriv Ψ ((c * r * t + 1) / x) * (c * r / x) :=
  funext fun t => (wt_hasDerivAt H x r t).deriv

lemma wt_weight (H : Hyp M c u Ψ) {x : ℝ} (hx : 0 < x) {r : ℕ} (hr : 1 ≤ r) :
    Weight (wt c Ψ x r) ((x - 1) / (c * r)) ((2 * x - 1) / (c * r)) := by
  have hcr : (0 : ℝ) < c * r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [H.c_two]
  refine ⟨fun t => (wt_hasDerivAt H x r t).differentiableAt, ?_, ?_⟩
  · rw [wt_deriv H x r]
    exact (H.cont_deriv.comp (by fun_prop)).mul continuous_const
  · intro t ht
    have hy : (c * r * t + 1) / x ≤ 1 ∨ 2 ≤ (c * r * t + 1) / x := by
      rcases ht with ht | ht
      · left
        rw [le_div_iff₀ hcr] at ht
        rw [div_le_one hx]; nlinarith
      · right
        rw [div_le_iff₀ hcr] at ht
        rw [le_div_iff₀ hx]; nlinarith
    rw [wt_deriv H x r]
    refine ⟨(H.zero_out hy).1, ?_⟩
    simp only [(H.zero_out hy).2, zero_mul]

lemma wt_deriv_bound (H : Hyp M c u Ψ) {x : ℝ} (hx : 0 < x) (r : ℕ) {B : ℝ}
    (hB : ∀ y, |deriv Ψ y| ≤ B) (t : ℝ) :
    |deriv (wt c Ψ x r) t| ≤ c * r / x * B := by
  rw [wt_deriv H x r]
  simp only
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * r / x), mul_comm]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

/-- The residue class of the predecessor primes modulo `N ℓ`. -/
noncomputable def rep (M c : ℕ) (u : ℤ) (r ℓ : ℕ) : ℕ :=
  Classical.epsilon fun v : ℕ => Nat.Coprime v (M / c * ℓ) ∧ ∀ Q : ℕ,
    ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1) ↔ Q ≡ v [MOD M / c * ℓ])

lemma rep_spec (H : Hyp M c u Ψ) (r ℓ : ℕ) (hℓ0 : 0 < ℓ) (hr : Nat.Coprime r M)
    (hℓ : Nat.Coprime ℓ (M * r)) :
    Nat.Coprime (rep M c u r ℓ) (M / c * ℓ) ∧ ∀ Q : ℕ,
      ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1) ↔
        Q ≡ rep M c u r ℓ [MOD M / c * ℓ]) := by
  have h := Nat.coprime_mul_iff_right.mp hℓ
  exact Classical.epsilon_spec (class_exists M c u H.hM H.c_pos H.c_dvd H.hcu H.hcop r ℓ hℓ0 hr
    h.1 h.2)

lemma pmd_eq (H : Hyp M c u Ψ) {x : ℝ} (hx : 0 < x) {r : ℕ} (hr : 1 ≤ r)
    (h09 : x ^ (0.9 : ℝ) ≤ (x - 1) / (c * r)) (hrM : Nat.Coprime r M) (ℓ : ℕ) (hℓ0 : 0 < ℓ)
    (hℓ : Nat.Coprime ℓ (M * r)) :
    predecessorMassDvd M c u Ψ x r ℓ = ∑ k ∈ Icc 0 ⌊(2 * x - 1) / (c * r)⌋₊,
      wt c Ψ x r k * primeInd (M / c * ℓ) (rep M c u r ℓ) k := by
  classical
  have hcr : (0 : ℝ) < c * r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [H.c_two]
  have hspec := (rep_spec H r ℓ hℓ0 hrM hℓ).2
  unfold predecessorMassDvd
  rw [tsum_subtype_eq_sum _ (fun Q : ℕ => Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x))
    (Icc 0 ⌊(2 * x - 1) / (c * r)⌋₊)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hwt : wt c Ψ x r k = Ψ (((c * r * k + 1 : ℕ) : ℝ) / x) := by unfold wt; push_cast; rfl
    rw [hwt]
    by_cases hz : Ψ (((c * r * k + 1 : ℕ) : ℝ) / x) = 0
    · have hz' := hz; push_cast at hz'; simp [hz, hz']
    have h1 : 1 < ((c * r * k + 1 : ℕ) : ℝ) / x := (psi_ne_zero H.hΨs hz).1
    have hk : x ^ (0.9 : ℝ) < k := by
      refine lt_of_le_of_lt h09 ?_
      rw [lt_div_iff₀ hx] at h1
      push_cast at h1
      rw [div_lt_iff₀ hcr]; linarith
    unfold primeInd
    by_cases hp : k.Prime ∧ k ≡ rep M c u r ℓ [MOD M / c * ℓ]
    · rw [if_pos hp, if_pos ⟨hp.1, hk, (hspec k).mpr hp.2⟩, mul_one]
    · rw [if_neg hp, mul_zero, if_neg]
      rintro ⟨hkp, -, h3, h4⟩
      exact hp ⟨hkp, (hspec k).mp ⟨h3, h4⟩⟩
  · intro k hk
    simp only [Finset.mem_Icc, zero_le, true_and, not_le] at hk
    have : (2 * x - 1) / (c * r) < k := Nat.lt_of_floor_lt hk
    rw [div_lt_iff₀ hcr] at this
    refine (H.zero_out (Or.inr ?_)).1
    rw [le_div_iff₀ hx]; push_cast; linarith

lemma pmd_zero (H : Hyp M c u Ψ) (x : ℝ) (r ℓ : ℕ) (hℓ : ¬ Nat.Coprime ℓ (M * r)) :
    predecessorMassDvd M c u Ψ x r ℓ = 0 := by
  unfold predecessorMassDvd
  have : IsEmpty {Q : ℕ // Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1} :=
    ⟨fun ⟨Q, hQ⟩ => class_empty M c u H.hu r ℓ Q hℓ ⟨hQ.2.2.1, hQ.2.2.2⟩⟩
  exact tsum_empty

lemma massRemainder_zero (H : Hyp M c u Ψ) (x : ℝ) (r ℓ : ℕ) (hℓ : ¬ Nat.Coprime ℓ (M * r)) :
    massRemainder M c u Ψ x r ℓ = 0 := by
  unfold massRemainder localDensity
  rw [pmd_zero H x r ℓ hℓ, if_neg hℓ]; ring

lemma T_facts (H : Hyp M c u Ψ) {θ : ℝ} (hθ : 0 < θ) {x : ℝ} (hx : 2 ≤ x) {r : ℕ}
    (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x ^ θ) :
    (1 - θ) * log x - log 8 ≤ log ((x - 1) / (c * r)) ∧
    (2 * x - 1) / (c * r) ≤ x / r ∧ 0 < (x - 1) / (c * r) ∧
    (x - 1) / (c * r) ≤ (2 * x - 1) / (c * r) ∧
    (2 * x - 1) / (c * r) - (x - 1) / (c * r) = x / (c * r) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcr : (0 : ℝ) < c * r := by nlinarith [H.c_two]
  have hx0 : 0 < x := by linarith
  refine ⟨?_, ?_, by apply div_pos <;> linarith, div_le_div_of_nonneg_right (by linarith) hcr.le,
    by field_simp; ring⟩
  · rw [log_div (by linarith) hcr.ne', log_mul (by have := H.c_two; positivity) (by positivity)]
    have h1 : log (x / 2) ≤ log (x - 1) := log_le_log (by positivity) (by linarith)
    rw [log_div hx0.ne' (by norm_num)] at h1
    have h2 : log (c : ℝ) ≤ log 4 := log_le_log (by have := H.c_two; positivity) H.c_four
    have h3 : log (r : ℝ) ≤ θ * log x := by
      rw [← log_rpow hx0]; exact log_le_log (by positivity) hrx
    have h8 : log (8 : ℝ) = log 2 + log 4 := by
      rw [← log_mul (by norm_num) (by norm_num)]; norm_num
    nlinarith
  · rw [div_le_div_iff₀ hcr (by positivity)]
    have : 2 * (x * r) ≤ c * (x * r) := mul_le_mul_of_nonneg_right H.c_two (by positivity)
    nlinarith

end

section
open Real Finset Filter Topology MeasureTheory
variable {M c : ℕ} {u : ℤ} {Ψ : ℝ → ℝ}

lemma rpow_split {L A : ℝ} (hL : 0 < L) :
    (L / 2) ^ (-(A + 2)) = 4 * 2 ^ A * L ^ (-A) / L ^ 2 := by
  rw [show -(A + 2) = -A + -2 by ring, rpow_add (by positivity),
    div_rpow hL.le (by norm_num), div_rpow hL.le (by norm_num),
    rpow_neg (by norm_num : (0:ℝ) ≤ 2) A, rpow_neg hL.le 2, rpow_neg (by norm_num : (0:ℝ) ≤ 2) 2]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, rpow_natCast]
  field_simp
  norm_num

set_option maxHeartbeats 1000000 in
lemma perR_bv (H : Hyp M c u Ψ) (κ ε A : ℝ) (hκ : 0 < κ) (hκ1 : κ < 0.01) (hε : 0 < ε)
    (hεκ : ε < κ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ x ^ ε → Nat.Coprime r M →
      ∑ ℓ ∈ (range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          |massRemainder M c u Ψ x r ℓ| ≤ C * (x / r * log x ^ (-A)) := by
  set η := (κ - ε) / 4 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  have hη2 : η < 1 / 2 := by rw [hη_def]; linarith
  obtain ⟨C0, hC0, hbv⟩ := smoothed_bv (A + 2) η (by linarith) hη hη2
  obtain ⟨B, hB0, hB⟩ := H.deriv_bound
  set N := M / c with hN_def
  have hN1 : 1 ≤ N := H.N_pos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set δ := (κ - ε) * (1 + ε) / 4 with hδ_def
  have hδ : 0 < δ := by
    rw [hδ_def]; have := mul_pos (sub_pos.mpr hεκ) (by linarith : (0:ℝ) < 1 + ε); linarith
  have hδ1 : δ ≤ 0.01 := by
    rw [hδ_def]
    have := mul_le_mul (by linarith : κ - ε ≤ 0.01) (by linarith : 1 + ε ≤ 1.01)
      (by linarith) (by norm_num)
    linarith
  have hkey : (1 / 2 - η) * (1 - ε) - (1 / 2 - κ / 2) = δ := by rw [hη_def, hδ_def]; ring
  have hlog8 : 0 < log (8 : ℝ) := log_pos (by norm_num)
  have hlog28 : log (2 : ℝ) ≤ log 8 := log_le_log (by norm_num) (by norm_num)
  have hlogN : 0 ≤ log (N : ℝ) := log_natCast_nonneg N
  set K0 := log (N : ℝ) + 2 * log 8 + 2 with hK0
  set L₀ := K0 / δ + 2 with hL₀
  refine ⟨8 * 2 ^ A * C0 * B, exp L₀, by positivity, ?_⟩
  intro x hx r hr hrx hrM
  set L := log x with hL_def
  have hL : L₀ ≤ L := by rw [hL_def, ← log_exp L₀]; exact log_le_log (exp_pos _) hx
  have hK0pos : 0 ≤ K0 := by rw [hK0]; positivity
  have hKδ : 0 ≤ K0 / δ := div_nonneg hK0pos hδ.le
  have hL2 : 2 ≤ L := by linarith
  have hx2 : 2 ≤ x := by
    have : exp 2 ≤ x := (exp_le_exp.mpr (by linarith)).trans hx
    have h3 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    linarith
  have hx0 : 0 < x := by linarith
  have hδL : K0 ≤ δ * L := by
    have h1 : K0 / δ ≤ L := by linarith
    calc K0 = δ * (K0 / δ) := by field_simp
      _ ≤ δ * L := mul_le_mul_of_nonneg_left h1 hδ.le
  obtain ⟨hlogT1, hT2x, hT1pos, h12, hdiff⟩ := T_facts H hε hx2 hr hrx
  set T₁ := (x - 1) / (c * r) with hT₁
  set T₂ := (2 * x - 1) / (c * r) with hT₂
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcr : (0 : ℝ) < c * r := mul_pos (by linarith [H.c_two]) (by linarith)
  -- consequences of `L ≥ L₀`
  have hLnn : 0 ≤ L := by linarith
  have hgap1 : δ * L ≤ (0.1 - ε) * L := mul_le_mul_of_nonneg_right (by linarith) hLnn
  have hgap2 : δ * L ≤ (1 / 2 - ε) * L := mul_le_mul_of_nonneg_right (by linarith) hLnn
  have hT1_2 : 2 ≤ T₁ := by
    have : log 2 ≤ log T₁ := by linarith
    exact (log_le_log_iff (by norm_num) hT1pos).mp this
  have h09 : x ^ (0.9 : ℝ) ≤ T₁ := by
    have : log (x ^ (0.9 : ℝ)) ≤ log T₁ := by rw [log_rpow hx0]; linarith
    exact (log_le_log_iff (by positivity) hT1pos).mp this
  have hLT1 : L / 2 ≤ log T₁ := by linarith
  set D := ⌊x ^ (1 / 2 - κ / 2)⌋₊ with hD
  have hlogD : log (D : ℝ) ≤ (1 / 2 - κ / 2) * L := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0]; simp; exact mul_nonneg (by linarith) hLnn
    · rw [← log_rpow hx0]
      exact log_le_log (by exact_mod_cast h0) (Nat.floor_le (by positivity))
  have hlogD0 : 0 ≤ log (D : ℝ) := log_natCast_nonneg D
  have hmod : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ D → ((N * ℓ : ℕ) : ℝ) < T₁ ^ (1 / 2 - η) := by
    intro ℓ hℓ1 hℓD
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    have hlogℓ : log (ℓ : ℝ) ≤ (1 / 2 - κ / 2) * L := by
      rw [← log_rpow hx0]
      exact log_le_log hℓpos ((Nat.cast_le.mpr hℓD).trans (Nat.floor_le (by positivity)))
    have : log ((N * ℓ : ℕ) : ℝ) < log (T₁ ^ (1 / 2 - η)) := by
      rw [log_rpow hT1pos, Nat.cast_mul, log_mul (by positivity) hℓpos.ne']
      have h1 : (1 / 2 - η) * ((1 - ε) * L - log 8) ≤ (1 / 2 - η) * log T₁ :=
        mul_le_mul_of_nonneg_left hlogT1 (by linarith)
      have hkeyL : (1 / 2 - η) * (1 - ε) * L - (1 / 2 - κ / 2) * L = δ * L := by
        rw [← hkey]; ring
      have := mul_nonneg hη.le hlog8.le
      linarith
    exact (log_lt_log_iff (by positivity) (by positivity)).mp this
  -- the main term and the prime sums
  set Main := ∫ t in T₁..T₂, wt c Ψ x r t * (1 / log t) with hMain
  set P : ℕ → ℝ := fun ℓ => ∑ k ∈ Icc 0 ⌊T₂⌋₊,
    wt c Ψ x r k * primeInd (N * ℓ) (rep M c u r ℓ) k with hP
  set Bw := c * r / x * B with hBw
  set Y := C0 * (Bw * ((T₂ - T₁) * (T₂ * log T₁ ^ (-(A + 2))))) with hY
  have hw := wt_weight H hx0 hr
  have hdb : ∀ t, |deriv (wt c Ψ x r) t| ≤ Bw := wt_deriv_bound H hx0 r hB
  set S := (range (D + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) with hS
  set S' := S.filter (fun ℓ => Nat.Coprime ℓ (M * r)) with hS'
  have hNM : N ∣ M := Nat.div_dvd_of_dvd H.c_dvd
  have hmemS' : ∀ ℓ ∈ S', 1 ≤ ℓ ∧ ℓ ≤ D ∧ Nat.Coprime ℓ (M * r) := by
    intro ℓ hℓ
    simp only [hS', hS, Finset.mem_filter, Finset.mem_range] at hℓ
    exact ⟨Nat.pos_of_ne_zero (by rintro rfl; exact absurd hℓ.1.2.1 (by decide)), by omega,
      hℓ.2⟩
  -- step 0: only coprime `ℓ` contribute
  have step0 : ∑ ℓ ∈ S, |massRemainder M c u Ψ x r ℓ| =
      ∑ ℓ ∈ S', |massRemainder M c u Ψ x r ℓ| := by
    rw [hS']; symm
    apply Finset.sum_filter_of_ne
    intro ℓ _ h
    by_contra hc
    exact h (by rw [massRemainder_zero H x r ℓ hc, abs_zero])
  -- the remainder in terms of the prime sums
  have hE : ∀ ℓ ∈ S', massRemainder M c u Ψ x r ℓ =
      P ℓ - 1 / (Nat.totient ℓ : ℝ) * P 1 := by
    intro ℓ hℓ
    obtain ⟨hℓ1, -, hcop⟩ := hmemS' ℓ hℓ
    unfold massRemainder localDensity predecessorMass
    rw [if_pos hcop, pmd_eq H hx0 hr h09 hrM ℓ hℓ1 hcop,
      pmd_eq H hx0 hr h09 hrM 1 Nat.one_pos (Nat.coprime_one_left _)]
  have hsplit : ∀ ℓ ∈ S', |P ℓ - 1 / (Nat.totient ℓ : ℝ) * P 1| ≤
      |P ℓ - 1 / (Nat.totient (N * ℓ) : ℝ) * Main| +
        1 / (Nat.totient ℓ : ℝ) * |P 1 - 1 / (Nat.totient (N * 1) : ℝ) * Main| := by
    intro ℓ hℓ
    obtain ⟨hℓ1, -, hcop⟩ := hmemS' ℓ hℓ
    have hℓN : Nat.Coprime N ℓ :=
      (Nat.Coprime.coprime_dvd_right hNM (Nat.coprime_mul_iff_right.mp hcop).1).symm
    rw [Nat.totient_mul hℓN, mul_one]
    have hφ : (0 : ℝ) ≤ 1 / (Nat.totient ℓ : ℝ) := by positivity
    have : P ℓ - 1 / (Nat.totient ℓ : ℝ) * P 1 =
        (P ℓ - 1 / ((Nat.totient N * Nat.totient ℓ : ℕ) : ℝ) * Main) -
          1 / (Nat.totient ℓ : ℝ) * (P 1 - 1 / (Nat.totient N : ℝ) * Main) := by
      push_cast; ring
    rw [this]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg hφ]
  -- the two sums
  have sum1 : ∑ ℓ ∈ S', |P ℓ - 1 / (Nat.totient (N * ℓ) : ℝ) * Main| ≤ Y := by
    have hinj : Set.InjOn (fun ℓ => N * ℓ) S' := by
      intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hN1 hab
    set vq : ℕ → ℕ := fun q => rep M c u r (q / N) with hvq
    have := hbv (wt c Ψ x r) T₁ T₂ Bw hw hT1_2 h12 hdb (S'.image fun ℓ => N * ℓ) vq ?_
    · rw [Finset.sum_image hinj] at this
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun ℓ _ => ?_)) this
      simp only [hP, hMain, hvq, Nat.mul_div_cancel_left _ hN1]
    · intro q hq
      obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hℓ1, hℓD, hcop⟩ := hmemS' ℓ hℓ
      refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hmod ℓ hℓ1 hℓD, ?_⟩
      simp only [hvq, Nat.mul_div_cancel_left _ hN1]
      exact (rep_spec H r ℓ hℓ1 hrM hcop).1
  have sum2 : |P 1 - 1 / (Nat.totient (N * 1) : ℝ) * Main| ≤ Y := by
    have := hbv (wt c Ψ x r) T₁ T₂ Bw hw hT1_2 h12 hdb {N * 1} (fun _ => rep M c u r 1) ?_
    · rw [Finset.sum_singleton] at this; exact this
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      refine ⟨by omega, hmod 1 Nat.one_pos ?_, (rep_spec H r 1 Nat.one_pos hrM (Nat.coprime_one_left _)).1⟩
      have : (1 : ℝ) ≤ x ^ (1 / 2 - κ / 2) := one_le_rpow (by linarith) (by linarith)
      exact Nat.le_floor (by simpa using this)
  have hφsum : ∑ ℓ ∈ S', 1 / (Nat.totient ℓ : ℝ) ≤ (1 + log D) ^ 2 := by
    refine le_trans ?_ (sum_inv_totient_le D)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro ℓ hℓ; simp only [hS', hS, Finset.mem_filter] at hℓ; exact hℓ.1.1
  have hY0 : 0 ≤ Y := by
    have := (abs_nonneg _).trans sum2; exact this
  have htotal : ∑ ℓ ∈ S', |massRemainder M c u Ψ x r ℓ| ≤ (1 + (1 + log D) ^ 2) * Y := by
    calc ∑ ℓ ∈ S', |massRemainder M c u Ψ x r ℓ|
        ≤ ∑ ℓ ∈ S', (|P ℓ - 1 / (Nat.totient (N * ℓ) : ℝ) * Main| +
            1 / (Nat.totient ℓ : ℝ) * |P 1 - 1 / (Nat.totient (N * 1) : ℝ) * Main|) := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          rw [hE ℓ hℓ]; exact hsplit ℓ hℓ
      _ = ∑ ℓ ∈ S', |P ℓ - 1 / (Nat.totient (N * ℓ) : ℝ) * Main| +
            (∑ ℓ ∈ S', 1 / (Nat.totient ℓ : ℝ)) *
              |P 1 - 1 / (Nat.totient (N * 1) : ℝ) * Main| := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ Y + (1 + log D) ^ 2 * Y := by
          refine add_le_add sum1 (mul_le_mul hφsum sum2 (abs_nonneg _) (by positivity))
      _ = (1 + (1 + log D) ^ 2) * Y := by ring
  -- simplify `Y`
  have hYle : Y ≤ C0 * B * (x / r) * (L / 2) ^ (-(A + 2)) := by
    have hBw : Bw * (T₂ - T₁) = B := by
      have hc0 : (c : ℝ) ≠ 0 := (by linarith [H.c_two] : (0:ℝ) < c).ne'
      have hr0 : (r : ℝ) ≠ 0 := (by linarith : (0:ℝ) < r).ne'
      rw [hdiff, hBw]; field_simp
    have hlogpow : log T₁ ^ (-(A + 2)) ≤ (L / 2) ^ (-(A + 2)) :=
      rpow_le_rpow_of_nonpos (by linarith) hLT1 (by linarith)
    have hT2nn : 0 ≤ T₂ := by linarith
    calc Y = C0 * B * (T₂ * log T₁ ^ (-(A + 2))) := by rw [hY, ← mul_assoc Bw, hBw]; ring
      _ ≤ C0 * B * (x / r * (L / 2) ^ (-(A + 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hB0)
          exact mul_le_mul hT2x hlogpow (rpow_nonneg (by linarith) _) (by positivity)
      _ = _ := by ring
  have hLpos : 0 < L := by linarith
  rw [step0]
  refine htotal.trans ?_
  have hfac : (1 + (1 + log D) ^ 2) ≤ 2 * L ^ 2 := by
    have h1 : (1 / 2 - κ / 2) * L ≤ L / 2 := by
      have := mul_nonneg hκ.le hLnn; linarith
    have h2 : 1 + log D ≤ L := by linarith
    have h3 : (1 + log D) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
    have h4 : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
    linarith
  rw [rpow_split hLpos] at hYle
  have hY' : Y ≤ C0 * B * (x / r) * (4 * 2 ^ A * L ^ (-A)) / L ^ 2 := by
    exact le_of_le_of_eq hYle (by ring)
  have hpos : 0 ≤ C0 * B * (x / r) * (4 * 2 ^ A * L ^ (-A)) := by positivity
  calc (1 + (1 + log D) ^ 2) * Y ≤ 2 * L ^ 2 * (C0 * B * (x / r) * (4 * 2 ^ A * L ^ (-A)) / L ^ 2) :=
        mul_le_mul hfac hY' hY0 (by positivity)
    _ = 8 * 2 ^ A * C0 * B * (x / r * L ^ (-A)) := by field_simp; ring

end
open Real in
theorem single_r_remainders_proof (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (κ ε A : ℝ) (hκ : 0 < κ) (hκ1 : κ < 0.01) (hε : 0 < ε) (hεκ : ε < κ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ x ^ ε → Nat.Coprime r M →
      ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          |massRemainder M c u Ψ x r ℓ| ≤ C * (x / r * log x ^ (-A)) :=
  perR_bv ⟨hM, h8, hc, hu, hcu, hcop, hΨ, hΨs, hΨ0, hΨ1⟩ κ ε A hκ hκ1 hε hεκ hA

end ArtinPrimitiveRoots.WFDrem

open ArtinPrimitiveRoots ArtinPrimitiveRoots.WFDrem Real in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (κ ε A : ℝ) (hκ : 0 < κ) (hκ1 : κ < 0.01) (hε : 0 < ε) (hεκ : ε < κ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ x ^ ε → Nat.Coprime r M →
      ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          |massRemainder M c u Ψ x r ℓ| ≤ C * (x / r * log x ^ (-A)) := by
  apply ArtinPrimitiveRoots.WFDrem.single_r_remainders_proof <;> assumption
