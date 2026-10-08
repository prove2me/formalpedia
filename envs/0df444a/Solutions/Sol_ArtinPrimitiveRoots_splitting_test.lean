-- Prove2me | solution 1 for ArtinPrimitiveRoots.splitting_test
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T09:13:56.245991+00:00
-- url     : https://prove2.me/submissions/5dd04c98-d12e-40ff-8293-b9f2c863e57c

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots.Lemma23

open NumberField Polynomial

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

lemma isIntegral_root (a : ℤ) (q : ℕ) (hq : 0 < q) (x : K) (hx : x ^ q = a) :
    IsIntegral ℤ x := by
  refine ⟨(X ^ q - C a : ℤ[X]), monic_X_pow_sub_C a hq.ne', ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, hx]; simp

lemma smul_intCast' (τ : Gal(K/ℚ)) (n : ℤ) : τ • (n : 𝓞 K) = n := by
  change (MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) τ) (n : 𝓞 K) = n
  exact map_intCast _ n

lemma lift_pow (a : ℤ) (q : ℕ) (x : K) (hint : IsIntegral ℤ x) (hx : x ^ q = a) :
    (⟨x, hint⟩ : 𝓞 K) ^ q = a := by
  apply RingOfIntegers.ext
  exact hx

lemma coe_pow_eq (a : ℤ) (q : ℕ) (x : 𝓞 K) (hx : x ^ q = a) : (x : K) ^ q = a := by
  have := congrArg (fun y : 𝓞 K => (y : K)) hx
  push_cast at this
  exact this

lemma coe_smul (τ : Gal(K/ℚ)) (x : 𝓞 K) : ((τ • x : 𝓞 K) : K) = τ (x : K) := rfl

/-- Distinct roots of `X^q - a` in `𝓞 K` stay distinct under a ring hom to a domain in which
`q` and `a` are nonzero. -/
lemma sep_hom {F : Type*} [CommRing F] [IsDomain F] (ψ : 𝓞 K →+* F) (a : ℤ) (q : ℕ)
    (hqF : (q : F) ≠ 0) (haF : (a : F) ≠ 0) (β γ : 𝓞 K) (hβ : β ^ q = a) (hγ : γ ^ q = a)
    (h : ψ β = ψ γ) : β = γ := by
  by_contra hne
  have hq0 : q ≠ 0 := by rintro rfl; simp at hqF
  have hψγ : ψ γ ≠ 0 := by
    intro h0; apply haF; rw [← map_intCast ψ, ← hγ, map_pow, h0, zero_pow hq0]
  have hγ0 : (γ : K) ≠ 0 := by
    intro h0; apply hψγ
    have : γ = 0 := RingOfIntegers.ext h0
    rw [this, map_zero]
  have hβK : (β : K) ^ q = a := coe_pow_eq a q β hβ
  have hγK : (γ : K) ^ q = a := coe_pow_eq a q γ hγ
  have hzq : ((β : K) / γ) ^ q = ((1 : ℤ) : K) := by
    rw [div_pow, hβK, hγK, div_self (by rw [← hγK]; exact pow_ne_zero _ hγ0)]; simp
  let ζ : 𝓞 K := ⟨(β : K) / γ, isIntegral_root 1 q (Nat.pos_of_ne_zero hq0) _ hzq⟩
  have hζγ : ζ * γ = β := RingOfIntegers.ext (by
    change (β : K) / γ * γ = β; field_simp)
  have hζ1 : ζ ≠ 1 := by intro h1; apply hne; rw [← hζγ, h1, one_mul]
  have hζq : ζ ^ q = 1 := RingOfIntegers.ext (by
    change ((β : K) / γ) ^ q = 1; rw [hzq]; simp)
  have hsum : ∑ i ∈ Finset.range q, ζ ^ i = 0 := by
    have := geom_sum_mul ζ q
    rw [hζq, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hζ1)
  have hψζ : ψ ζ = 1 := by
    have : ψ ζ * ψ γ = 1 * ψ γ := by rw [← map_mul, hζγ, h, one_mul]
    exact mul_right_cancel₀ hψγ this
  apply hqF
  have := congrArg ψ hsum
  simpa [map_sum, hψζ] using this

lemma mem_rootSet_iff (a : ℤ) (q : ℕ) (hq : 0 < q) (x : K) :
    x ∈ (X ^ q - C (a : ℚ)).rootSet K ↔ x ^ q = a := by
  rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero hq _)]
  simp [sub_eq_zero]

lemma two_roots (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime)
    [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    ∃ β γ : 𝓞 K, β ^ q = a ∧ γ ^ q = a ∧ β ≠ γ := by
  classical
  have hsep : (X ^ q - C (a : ℚ)).Separable :=
    separable_X_pow_sub_C _ (by exact_mod_cast hq.ne_zero) (by exact_mod_cast ha)
  have hcard := card_rootSet_eq_natDegree (K := K) hsep (IsSplittingField.splits K _)
  rw [natDegree_X_pow_sub_C] at hcard
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (hcard ▸ hq.one_lt)
  have hx := (mem_rootSet_iff a q hq.pos _).mp x.2
  have hy := (mem_rootSet_iff a q hq.pos _).mp y.2
  refine ⟨⟨x, isIntegral_root a q hq.pos _ hx⟩, ⟨y, isIntegral_root a q hq.pos _ hy⟩,
    lift_pow a q _ _ hx, lift_pow a q _ _ hy, ?_⟩
  intro h
  exact hxy (Subtype.ext (congrArg (fun z : 𝓞 K => (z : K)) h))

lemma gal_ext (a : ℤ) (q : ℕ) (hq : q.Prime) [IsSplittingField ℚ K (X ^ q - C (a : ℚ))]
    (τ τ' : Gal(K/ℚ)) (h : ∀ x : 𝓞 K, x ^ q = a → τ • x = τ' • x) : τ = τ' := by
  have hadj := IsSplittingField.adjoin_rootSet (L := K) (X ^ q - C (a : ℚ))
  have : (τ : K →ₐ[ℚ] K) = τ' := by
    refine AlgHom.ext_of_adjoin_eq_top hadj ?_
    intro x hx
    have hx' := (mem_rootSet_iff a q hq.pos _).mp hx
    have := h ⟨x, isIntegral_root a q hq.pos _ hx'⟩ (lift_pow a q _ _ hx')
    exact congrArg (fun z : 𝓞 K => (z : K)) this
  exact AlgEquiv.ext fun x => DFunLike.congr_fun this x

lemma ker_mem (p : ℕ) [hp : Fact p.Prime] (ψ : 𝓞 K →+* ZMod p) :
    (RingHom.ker ψ).IsPrime ∧ RingHom.ker ψ ≠ ⊥ ∧ Ideal.absNorm (RingHom.ker ψ) = p := by
  refine ⟨RingHom.ker_isPrime ψ, ?_, ?_⟩
  · intro h
    have : (p : 𝓞 K) ∈ RingHom.ker ψ := by simp [RingHom.mem_ker]
    rw [h, Ideal.mem_bot] at this
    exact hp.out.ne_zero (by exact_mod_cast this)
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ψ)).toEquiv,
      Nat.card_zmod]

lemma set_sub (p : ℕ) [hp : Fact p.Prime] (P : Ideal (𝓞 K))
    (h : P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  obtain ⟨hP, -, hn⟩ := h
  refine ⟨hP, ⟨?_⟩⟩
  have hmem : ((p : ℤ) : 𝓞 K) ∈ P := by
    have := Ideal.absNorm_mem P; rw [hn] at this; exact_mod_cast this
  refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (p : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 K))
  rw [Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
  exact hmem

lemma card_le (p : ℕ) [hp : Fact p.Prime] [IsGalois ℚ K] :
    Finite {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} ∧
    Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} ≤
      Module.finrank ℚ K := by
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hfin := IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 K)
  have hsub : {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} ⊆
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := fun P h => set_sub p P h
  have key := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at key
  refine ⟨(hfin.subset hsub).to_subtype, ?_⟩
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  change Nat.card ↥{P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} ≤ _
  rw [Nat.card_coe_set_eq]
  calc _ ≤ ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ _ := by
      rw [← key]
      refine Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ?_)
      intro h0; rw [h0, mul_zero] at key; omega

lemma nonzero_facts (a : ℤ) (p q : ℕ) (hpaq : ¬ (p : ℤ) ∣ a * q) :
    (a : ZMod p) ≠ 0 ∧ (q : ZMod p) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => hpaq (dvd_mul_of_dvd_left h _)
  · have : ((q : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact fun h => hpaq (dvd_mul_of_dvd_right h _)
    exact_mod_cast this

lemma conds_of_hom (a : ℤ) (ha : a ≠ 0) (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * q) [IsSplittingField ℚ K (X ^ q - C (a : ℚ))]
    (ψ : 𝓞 K →+* ZMod p) :
    p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  obtain ⟨haP, hqP⟩ := nonzero_facts a p q hpaq
  obtain ⟨β, γ, hβ, hγ, hne⟩ := two_roots (K := K) a ha q hq
  have hψ : ψ β ≠ ψ γ := fun h => hne (sep_hom ψ a q hqP haP β γ hβ hγ h)
  have hb : ψ β ^ q = a := by rw [← map_pow, hβ, map_intCast]
  have hc : ψ γ ^ q = a := by rw [← map_pow, hγ, map_intCast]
  have hc0 : ψ γ ≠ 0 := by
    intro h0; rw [h0, zero_pow hq.ne_zero] at hc; exact haP hc.symm
  have hdvd : q ∣ p - 1 := by
    by_contra hnd
    have hz1 : ψ β / ψ γ ≠ 1 := by
      intro h; exact hψ ((div_eq_one_iff_eq hc0).mp h)
    have hzq : (ψ β / ψ γ) ^ q = 1 := by rw [div_pow, hb, hc, div_self haP]
    have hz0 : ψ β / ψ γ ≠ 0 := by
      intro h; rw [h, zero_pow hq.ne_zero] at hzq; exact zero_ne_one hzq
    have hzp : (ψ β / ψ γ) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz0
    have hcop : Nat.Coprime q (p - 1) := (Nat.coprime_or_dvd_of_prime hq _).resolve_right hnd
    have := pow_gcd_eq_one.mpr ⟨hzq, hzp⟩
    rw [hcop.gcd_eq_one, pow_one] at this
    exact hz1 this
  refine ⟨((Nat.modEq_iff_dvd' hp.out.one_le).mpr hdvd).symm, ?_⟩
  rw [← hc, ← pow_mul, Nat.mul_div_cancel' hdvd]
  exact ZMod.pow_card_sub_one_eq_one hc0

lemma lower (a : ℤ) (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * q) [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] [IsGalois ℚ K]
    (ψ : 𝓞 K →+* ZMod p)
    [Finite {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p}] :
    Module.finrank ℚ K ≤
      Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} := by
  obtain ⟨haP, hqP⟩ := nonzero_facts a p q hpaq
  rw [← IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  refine Nat.card_le_card_of_injective (fun τ : Gal(K/ℚ) =>
    ⟨RingHom.ker (ψ.comp (MulSemiringAction.toRingHom _ (𝓞 K) τ)), ker_mem p _⟩) ?_
  intro τ τ' h
  have h' := ZMod.ringHom_eq_of_ker_eq _ _ (congrArg Subtype.val h)
  apply gal_ext a q hq
  intro x hx
  have hτ : ∀ σ : Gal(K/ℚ), (σ • x) ^ q = a := fun σ => by
    rw [← smul_pow', hx, smul_intCast']
  exact sep_hom ψ a q hqP haP _ _ (hτ τ) (hτ τ') (DFunLike.congr_fun h' x)

lemma isGalois (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime)
    [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] : IsGalois ℚ K :=
  IsGalois.of_separable_splitting_field (p := X ^ q - C (a : ℚ))
    (separable_X_pow_sub_C _ (by exact_mod_cast hq.ne_zero) (by exact_mod_cast ha))

lemma exists_hom (a : ℤ) (ha : a ≠ 0) (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * q) [IsSplittingField ℚ K (X ^ q - C (a : ℚ))]
    (h1 : p ≡ 1 [MOD q]) (h2 : (a : ZMod p) ^ ((p - 1) / q) = 1) :
    Nonempty (𝓞 K →+* ZMod p) := by
  classical
  have := isGalois (K := K) a ha q hq
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hPm, hPo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := hPo.over.symm
  have hmemint : ∀ n : ℤ, (n : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ n := by
    intro n
    rw [← Ideal.mem_span_singleton, ← hunder, Ideal.under, Ideal.mem_comap, algebraMap_int_eq,
      eq_intCast]
  have hP0 : P ≠ ⊥ := by
    intro h
    have := (hmemint p).mpr dvd_rfl
    rw [h, Ideal.mem_bot] at this
    exact hp.out.ne_zero (by exact_mod_cast this)
  have : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hunder, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hσ' : ∀ x : 𝓞 K, σ • x - x ^ p ∈ P := fun x => by
    have := hσ x; rw [hcard] at this; exact this
  have hdvd : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp.out.one_le).mp h1.symm
  have hm : ((a ^ ((p - 1) / q) - 1 : ℤ) : 𝓞 K) ∈ P := by
    rw [hmemint, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [h2, sub_self]
  have hroot : ∀ x : 𝓞 K, x ^ q = a → x ^ p - x ∈ P := by
    intro x hx
    have hpm : p = q * ((p - 1) / q) + 1 := by
      rw [Nat.mul_div_cancel' hdvd]; have := hp.out.one_le; omega
    have : x ^ p - x = x * ((a ^ ((p - 1) / q) - 1 : ℤ) : 𝓞 K) := by
      rw [congrArg (x ^ ·) hpm, pow_succ, pow_mul, hx]; push_cast; ring
    rw [this]; exact P.mul_mem_left _ hm
  obtain ⟨haP, hqP⟩ := nonzero_facts a p q hpaq
  have haQ : ((a : ℤ) : 𝓞 K ⧸ P) ≠ 0 := by
    rw [← map_intCast (Ideal.Quotient.mk P), Ne, Ideal.Quotient.eq_zero_iff_mem, hmemint]
    exact fun h => hpaq (dvd_mul_of_dvd_left h _)
  have hqQ : ((q : ℕ) : 𝓞 K ⧸ P) ≠ 0 := by
    have : (((q : ℤ) : 𝓞 K) : 𝓞 K ⧸ P) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem, hmemint]
      exact fun h => hpaq (dvd_mul_of_dvd_right h _)
    simpa using this
  have hfix : σ = 1 := by
    apply gal_ext a q hq
    intro x hx
    rw [one_smul]
    have hσx : (σ • x) ^ q = a := by rw [← smul_pow', hx, smul_intCast']
    refine sep_hom (Ideal.Quotient.mk P) a q (by simpa using hqQ) (by simpa using haQ) _ _ hσx hx ?_
    rw [Ideal.Quotient.eq]
    have e : σ • x - x = (σ • x - x ^ p) + (x ^ p - x) := by ring
    rw [e]; exact add_mem (hσ' x) (hroot x hx)
  have hfrob : ∀ y : 𝓞 K, y ^ p - y ∈ P := fun y => by
    have := hσ' y; rw [hfix, one_smul] at this
    rw [← neg_sub]; exact P.neg_mem this
  let := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hchar : CharP (𝓞 K ⧸ P) p := by
    refine ⟨fun n => ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    have := hmemint n
    push_cast at this
    rw [this]; exact Int.natCast_dvd_natCast
  have hle : Fintype.card (𝓞 K ⧸ P) ≤ p := by
    have hne := FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ P) hp.out.one_lt
    calc Fintype.card (𝓞 K ⧸ P) = (Finset.univ : Finset (𝓞 K ⧸ P)).card := rfl
      _ ≤ (X ^ p - X : (𝓞 K ⧸ P)[X]).roots.toFinset.card := by
        refine Finset.card_le_card fun y _ => ?_
        rw [Multiset.mem_toFinset, mem_roots hne]
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        simp only [IsRoot, eval_sub, eval_pow, eval_X]
        rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hfrob y
      _ ≤ (X ^ p - X : (𝓞 K ⧸ P)[X]).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X ^ p - X : (𝓞 K ⧸ P)[X]).natDegree := card_roots' _
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt
  have hge : p ≤ Fintype.card (𝓞 K ⧸ P) := by
    have := Fintype.card_le_of_injective _ (ZMod.castHom_injective (𝓞 K ⧸ P))
    rwa [ZMod.card] at this
  let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hp.out (le_antisymm hle hge)
  exact ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk P)⟩

end ArtinPrimitiveRoots.Lemma23

open NumberField Polynomial ArtinPrimitiveRoots in
theorem solution (a : ℤ) (ha : a ≠ 0) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * q) (K : Type*) [Field K] [NumberField K]
    [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    SplitsCompletely K p ↔ (p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have := Lemma23.isGalois (K := K) a ha q hq
  obtain ⟨hfin, hle⟩ := Lemma23.card_le (K := K) p
  constructor
  · intro h
    have hpos : 0 < Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} := by
      rw [SplitsCompletely] at h; rw [h]; exact Module.finrank_pos
    obtain ⟨⟨P, hP, -, hn⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    have hcard : Nat.card (𝓞 K ⧸ P) = p := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn; exact hn
    have : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hp (by rw [← Nat.card_eq_fintype_card, hcard])
    exact Lemma23.conds_of_hom a ha p q hq hpaq (e.symm.toRingHom.comp (Ideal.Quotient.mk P))
  · rintro ⟨h1, h2⟩
    obtain ⟨ψ⟩ := Lemma23.exists_hom (K := K) a ha p q hq hpaq h1 h2
    exact le_antisymm hle (Lemma23.lower a p q hq hpaq ψ)
