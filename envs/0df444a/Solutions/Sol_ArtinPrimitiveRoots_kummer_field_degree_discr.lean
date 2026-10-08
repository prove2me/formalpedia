-- Prove2me | solution 1 for ArtinPrimitiveRoots.kummer_field_degree_discr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T09:22:34.134733+00:00
-- url     : https://prove2.me/submissions/903bd501-8fb3-4f53-b739-9d2cea54a976

import Mathlib
open NumberField Polynomial

namespace ArtinPrimitiveRoots.KummerDeg

theorem core (q : ℕ) (hq : q.Prime) (a : ℤ)
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    [hcyc : IsCyclotomicExtension {q} ℚ E]
    (hfin : Module.finrank E K = q) (hfinE : Module.finrank ℚ E = q - 1)
    (x : 𝓞 K) (hx : (x : K) ^ q = (a : K))
    (hgen : IntermediateField.adjoin E {(x : K)} = ⊤) :
    ∃ d : ℕ, d ∣ q ^ ((q - 1) * q) * a.natAbs ^ ((q - 1) * (q - 1)) ∧
      (discr K).natAbs = d * (q ^ (q - 2)) ^ q := by
  have hqpos : 0 < q := hq.pos
  have hxint : IsIntegral E (x : K) := (Algebra.IsIntegral.isIntegral (R := E) (x : K))
  -- minpoly over E
  have hmin : minpoly E (x : K) = X ^ q - C (a : E) := by
    have hmonic : (X ^ q - C (a : E)).Monic := monic_X_pow_sub_C _ hqpos.ne'
    have hdvd : minpoly E (x : K) ∣ X ^ q - C (a : E) := by
      apply minpoly.dvd
      simp [hx]
    have hdeg : (minpoly E (x : K)).natDegree = q := by
      rw [← IntermediateField.adjoin.finrank hxint, hgen, IntermediateField.finrank_top', hfin]
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxint) hmonic hdvd
      (by rw [natDegree_X_pow_sub_C, hdeg])).symm
  have hxO : IsIntegral (𝓞 E) x := Algebra.IsIntegral.isIntegral x
  have hminO : minpoly (𝓞 E) x = X ^ q - C ((a : 𝓞 E)) := by
    have h1 := minpoly.isIntegrallyClosed_eq_field_fractions E K hxO
    apply Polynomial.map_injective (algebraMap (𝓞 E) E) (RingOfIntegers.coe_injective)
    rw [← h1]
    simp [hmin]
  have hgenA : Algebra.adjoin E {(algebraMap (𝓞 K) K x)} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxint.isAlgebraic
    change Algebra.adjoin E {(x : K)} = ⊤
    rw [← this, hgen]
    simp
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 E) E K x hgenA
  rw [hminO] at hmem
  simp only [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, map_natCast,
    map_pow, aeval_X] at hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Module.finrank ℤ (𝓞 K) = (q - 1) * q := by
    rw [RingOfIntegers.rank, ← Module.finrank_mul_finrank ℚ E K, hfin, hfinE]
  have hxq : x ^ q = ((a : ℤ) : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    simpa using hx
  have hNx : (Algebra.norm ℤ x).natAbs = a.natAbs ^ (q - 1) := by
    have h1 : (Algebra.norm ℤ x) ^ q = a ^ ((q - 1) * q) := by
      rw [← map_pow, hxq, ← hn]
      exact Algebra.norm_algebraMap a
    have h2 : (Algebra.norm ℤ x).natAbs ^ q = (a.natAbs ^ (q - 1)) ^ q := by
      rw [← Int.natAbs_pow, h1, Int.natAbs_pow, ← pow_mul, mul_comm]
    exact Nat.pow_left_injective hq.ne_zero h2
  have hNy : (Algebra.norm ℤ ((q : 𝓞 K) * x ^ (q - 1))).natAbs =
      q ^ ((q - 1) * q) * a.natAbs ^ ((q - 1) * (q - 1)) := by
    rw [map_mul, map_pow, Int.natAbs_mul, Int.natAbs_pow, hNx, ← pow_mul]
    congr 1
    have : (q : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hn]
    simp
  have : Fact q.Prime := ⟨hq⟩
  have hdE : (discr E).natAbs = q ^ (q - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime q E]
    simp [Int.natAbs_mul, Int.natAbs_pow]
  refine ⟨Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 K)), hNy ▸ hdvd, ?_⟩
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) K (𝓞 K), hdE, hfin]


/-- `a` is not a `q`-th power in `ℚ`. -/
theorem not_pow (a : ℤ) (ℓ q : ℕ) (hℓ : ℓ.Prime) (hℓa : (ℓ : ℤ) ∣ a)
    (ha : a ≠ 0) (hqv : padicValInt ℓ a < q) (b : ℚ) : b ^ q ≠ (a : ℚ) := by
  intro hb
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h1 : padicValRat ℓ (b ^ q) = q * padicValRat ℓ b := padicValRat.pow b
  rw [hb, padicValRat.of_int] at h1
  have hpos : 0 < padicValInt ℓ a := by
    have := (padicValInt_dvd_iff (p := ℓ) 1 a).mp (by simpa using hℓa)
    omega
  have hdvd : (q : ℤ) ∣ (padicValInt ℓ a : ℤ) := ⟨_, h1⟩
  have : q ∣ padicValInt ℓ a := by exact_mod_cast hdvd
  have := Nat.le_of_dvd hpos this
  omega

end ArtinPrimitiveRoots.KummerDeg

open NumberField Polynomial in
theorem solution (a : ℤ) (ℓ q : ℕ) (hℓ : ℓ.Prime) (hℓa : (ℓ : ℤ) ∣ a)
    (ha : a ≠ 0) (hq : q.Prime) (hqℓ : q ≠ ℓ) (hqv : padicValInt ℓ a < q)
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    Module.finrank ℚ K = q * (q - 1) ∧
    (|discr K| : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (|a| : ℝ) ^ (q - 1)) ^ (q - 1) ∧
    (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * q →
      ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1) := by
  classical
  have hqpos := hq.pos
  set f : ℚ[X] := X ^ q - C (a : ℚ) with hf
  have hirr : Irreducible f := X_pow_sub_C_irreducible_of_prime hq
    (ArtinPrimitiveRoots.KummerDeg.not_pow a ℓ q hℓ hℓa ha hqv)
  have hsplit : (f.map (algebraMap ℚ K)).Splits := IsSplittingField.splits K f
  have hsep : (f.map (algebraMap ℚ K)).Separable := by
    rw [hf, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact separable_X_pow_sub_C _ (by exact_mod_cast hq.ne_zero) (by simpa using ha)
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hroot : ∀ r : K, r ∈ f.rootSet K ↔ r ^ q = (a : K) := by
    intro r
    rw [mem_rootSet]
    constructor
    · rintro ⟨-, h⟩
      simpa [hf, sub_eq_zero] using h
    · intro h
      exact ⟨hf0, by simp [hf, h]⟩
  have hcard : 1 < (f.aroots K).toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), ← hsplit.natDegree_eq_card_roots,
      natDegree_map, hf, natDegree_X_pow_sub_C]
    exact hq.one_lt
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.mp hcard
  have hα' : α ^ q = (a : K) := (hroot α).mp hα
  have hβ' : β ^ q = (a : K) := (hroot β).mp hβ
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hq.ne_zero] at hα'
    exact haK hα'.symm
  set ζ : K := β / α with hζdef
  have hζq : ζ ^ q = 1 := by rw [div_pow, hβ', hα', div_self haK]
  have hζ1 : ζ ≠ 1 := by
    intro h
    exact hαβ ((div_eq_one_iff_eq hα0).mp h).symm
  have hζ : IsPrimitiveRoot ζ q := by
    have hord : orderOf ζ = q := by
      have hd : orderOf ζ ∣ q := orderOf_dvd_of_pow_eq_one hζq
      rcases hq.eq_one_or_self_of_dvd _ hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hζ1
      · exact h
    rw [← hord]
    exact IsPrimitiveRoot.orderOf ζ
  set E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {ζ} with hE
  have : NeZero q := ⟨hq.ne_zero⟩
  have hcyc : IsCyclotomicExtension {q} ℚ E := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hfinE : Module.finrank ℚ E = q - 1 := by
    rw [IsCyclotomicExtension.finrank E (cyclotomic.irreducible_rat hq.pos), Nat.totient_prime hq]
  have hgen : IntermediateField.adjoin E {α} = ⊤ := by
    rw [eq_top_iff]
    have hle : Algebra.adjoin ℚ (f.rootSet K) ≤
        ((IntermediateField.adjoin E {α}).restrictScalars ℚ).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      intro r hr
      have hr' : r ^ q = (a : K) := (hroot r).mp hr
      have hrq : (r / α) ^ q = 1 := by rw [div_pow, hr', hα', div_self haK]
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hrq
      have hrr : r = ζ ^ i * α := by rw [hi]; field_simp
      rw [hrr]
      have hζmem : ζ ∈ IntermediateField.adjoin E {α} :=
        IntermediateField.algebraMap_mem (IntermediateField.adjoin E {α})
          (⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩ : E)
      exact mul_mem (pow_mem hζmem i) (IntermediateField.mem_adjoin_simple_self E α)
    intro y _
    have : y ∈ Algebra.adjoin ℚ (f.rootSet K) := by
      rw [IsSplittingField.adjoin_rootSet]; trivial
    exact hle this
  have hαint : IsIntegral E α := Algebra.IsIntegral.isIntegral α
  have hleq : Module.finrank E K ≤ q := by
    rw [← IntermediateField.finrank_top', ← hgen, IntermediateField.adjoin.finrank hαint]
    have : minpoly E α ∣ X ^ q - C (a : E) := minpoly.dvd E α (by simp [hα'])
    calc _ ≤ (X ^ q - C (a : E)).natDegree :=
          natDegree_le_of_dvd this (X_pow_sub_C_ne_zero hqpos _)
      _ = q := natDegree_X_pow_sub_C
  have hαQ : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = q := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)]
    have : f = minpoly ℚ α := minpoly.eq_of_irreducible_of_monic hirr (by simp [hf, hα'])
      (monic_X_pow_sub_C _ hq.ne_zero)
    rw [← this, hf, natDegree_X_pow_sub_C]
  have hqdvd : q ∣ Module.finrank ℚ K :=
    hαQ ▸ ⟨_, (Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {α}) K).symm⟩
  have htower : Module.finrank ℚ K = (q - 1) * Module.finrank E K := by
    rw [← Module.finrank_mul_finrank ℚ E K, hfinE]
  have hcop : Nat.Coprime q (q - 1) := by
    rw [hq.coprime_iff_not_dvd]
    intro h
    have := Nat.le_of_dvd (by have := hq.two_le; omega) h
    omega
  have hfin : Module.finrank E K = q := by
    have h1 : q ∣ Module.finrank E K := hcop.dvd_of_dvd_mul_left (htower ▸ hqdvd)
    have h2 : 0 < Module.finrank E K := Module.finrank_pos
    exact le_antisymm hleq (Nat.le_of_dvd h2 h1)
  have hαZ : IsIntegral ℤ α :=
    ⟨X ^ q - C a, monic_X_pow_sub_C _ hq.ne_zero, by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, hα']; simp⟩
  let x : 𝓞 K := ⟨α, hαZ⟩
  obtain ⟨d, hd, hdisc⟩ := ArtinPrimitiveRoots.KummerDeg.core q hq a E K hfin hfinE x hα' hgen
  refine ⟨by rw [htower, hfin, mul_comm], ?_, ?_⟩
  · have hN : 0 < q ^ ((q - 1) * q) * a.natAbs ^ ((q - 1) * (q - 1)) := by
      have : 0 < a.natAbs := Int.natAbs_pos.mpr ha
      positivity
    have hdle := Nat.le_of_dvd hN hd
    have hnat : (discr K).natAbs ≤ q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
      rw [hdisc, mul_comm, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm (q - 2) q,
        mul_comm q (q - 1)]
      exact Nat.mul_le_mul_left _ hdle
    have hcast : |((discr K : ℤ) : ℝ)| = ((discr K).natAbs : ℝ) := by
      simp [Nat.cast_natAbs]
    rw [hcast]
    have : (|a| : ℝ) = (a.natAbs : ℝ) := by simp [Nat.cast_natAbs]
    rw [this]
    exact_mod_cast hnat
  · intro p hp hpaq P hP hpP
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpq : ¬ p ∣ q := by
      intro h
      exact hpaq (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr h) a)
    have hpa : ¬ p ∣ a.natAbs := by
      intro h
      exact hpaq (Dvd.dvd.mul_right (Int.natCast_dvd.mpr h) _)
    have hnd : ¬ (p : ℤ) ∣ discr K := by
      intro h
      have h1 : p ∣ (discr K).natAbs := Int.natCast_dvd.mp h
      rw [hdisc] at h1
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp (h2.trans hd) with h4 | h4
        · exact hpq (hp.dvd_of_dvd_pow h4)
        · exact hpa (hp.dvd_of_dvd_pow h4)
      · exact hpq (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h2))
    have hun := (not_dvd_discr_iff_forall_mem K (𝓞 K) hpZ).mp hnd P hP (by simpa using hpP)
    exact Ideal.ramificationIdx_eq_one P ℤ
