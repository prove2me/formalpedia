-- Prove2me | solution 1 for ArtinL.Abelian.factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d4332256-1a91-54ef-8c07-e97371d2949d

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent

set_option autoImplicit false

noncomputable section

namespace ArtinConductorSupport

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply ArtinL.Abelian LanglandsTunnell.P2.Artin

open scoped Classical

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

omit [NumberField M] [IsGalois K M] in
theorem ramificationGroup_succ_le (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    ramificationGroup K M v (i + 1) ≤ inertiaGroup K M v := by
  intro σ hσ x
  exact Ideal.pow_le_self (Nat.succ_ne_zero _) (hσ x)

omit [IsGalois K M] in
theorem conductorExponent_eq_zero_of_isUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (h : IsUnramifiedAt ψ v) : conductorExponent ψ v = 0 := by
  have hsw : swanConductor ψ v = 0 := by
    unfold swanConductor
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    rw [if_pos, mul_zero]
    intro σ hσ
    exact h σ (ramificationGroup_succ_le v i hσ)
  rw [conductorExponent, if_pos h, hsw]
  simp

omit [IsGalois K M] in
theorem one_le_conductorExponent_of_not_isUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (h : ¬ IsUnramifiedAt ψ v) : 1 ≤ conductorExponent ψ v := by
  rw [conductorExponent, if_neg h]
  exact Nat.le_add_right 1 _

omit [IsGalois K M] in

theorem exists_ne_zero_forall_mem (h1 : ∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ∃ x : 𝓞 M, σ • x - x ≠ 0) :
    ∃ N : 𝓞 M, N ≠ 0 ∧ ∀ σ : M ≃ₐ[K] M, σ ≠ 1 →
      ∀ P : Ideal (𝓞 M), (∀ x : 𝓞 M, σ • x - x ∈ P) → N ∈ P := by
  choose! x hx using h1
  refine ⟨∏ σ ∈ (Finset.univ.filter fun σ : M ≃ₐ[K] M ↦ σ ≠ 1), (σ • x σ - x σ), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro σ hσ
    exact hx σ (Finset.mem_filter.1 hσ).2
  · intro σ hσ P hP
    have hmem : σ ∈ Finset.univ.filter fun σ : M ≃ₐ[K] M ↦ σ ≠ 1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hP (x σ))

theorem exists_smul_sub_ne_zero (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) : ∃ x : 𝓞 M, σ • x - x ≠ 0 := by
  by_contra h
  push Not at h
  apply hσ
  haveI : FaithfulSMul (M ≃ₐ[K] M) (𝓞 M) :=
    (isGaloisGroup_ringOfIntegers K M).faithful
  exact FaithfulSMul.eq_of_smul_eq_smul (M := M ≃ₐ[K] M) (α := 𝓞 M)
    fun x ↦ by rw [one_smul]; exact sub_eq_zero.1 (h x)

theorem finite_setOf_not_isUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ¬ IsUnramifiedAt ψ v}.Finite := by
  obtain ⟨N, hN0, hN⟩ := exists_ne_zero_forall_mem (K := K) (M := M)
    fun σ hσ ↦ exists_smul_sub_ne_zero σ hσ

  let f : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 M) := fun v ↦
    ⟨primeAbove K M v, (primeAbove_isMaximal K M v).isPrime, primeAbove_ne_bot K M v⟩
  have hinj : Set.InjOn f {v : HeightOneSpectrum (𝓞 K) | ¬ IsUnramifiedAt ψ v} := by
    intro v _ w _ h
    have h' : primeAbove K M v = primeAbove K M w := congrArg HeightOneSpectrum.asIdeal h
    apply HeightOneSpectrum.ext
    rw [← under_primeAbove K M v, ← under_primeAbove K M w, h']
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Ideal.finite_factors (I := Ideal.span {N}) ?_).subset ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hN0
  · rintro P ⟨v, hv, rfl⟩
    rw [Set.mem_setOf_eq] at hv ⊢
    rw [IsUnramifiedAt] at hv
    push Not at hv
    obtain ⟨σ, hσI, hσψ⟩ := hv
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact hσψ (map_one ψ)
    show primeAbove K M v ∣ Ideal.span {N}
    rw [Ideal.dvd_span_singleton]
    exact hN σ hσ1 _ hσI

omit [IsGalois K M] in
theorem hasFiniteMulSupport_of_finite (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ IsUnramifiedAt ψ v}.Finite) :
    Function.HasFiniteMulSupport
      fun w : HeightOneSpectrum (𝓞 K) ↦ w.asIdeal ^ conductorExponent ψ w := by
  refine hfin.subset fun w hw ↦ ?_
  rw [Function.mem_mulSupport] at hw
  rw [Set.mem_setOf_eq]
  intro hunr
  exact hw (by rw [conductorExponent_eq_zero_of_isUnramifiedAt ψ w hunr, pow_zero])

theorem dvd_conductor_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ conductor ψ ↔ ¬ IsUnramifiedAt ψ v := by
  have hfin := hasFiniteMulSupport_of_finite ψ (finite_setOf_not_isUnramifiedAt ψ)
  have hconductor : conductor ψ = ∏ w ∈ hfin.toFinset, w.asIdeal ^ conductorExponent ψ w := by
    unfold ArtinL.Abelian.conductor
    exact finprod_eq_prod _ hfin
  rw [hconductor]
  constructor
  · intro hv hunr
    have hf0 := conductorExponent_eq_zero_of_isUnramifiedAt ψ v hunr
    have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    obtain ⟨w, hw, hvw⟩ := (Prime.dvd_finsetProd_iff hprime _).1 hv
    have hvw' : v.asIdeal ∣ w.asIdeal := hprime.dvd_of_dvd_pow hvw
    have heq : v = w := by
      have hle : w.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd hvw'
      exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hle).symm
    subst heq
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, hf0, pow_zero] at hw
    exact hw rfl
  · intro hram
    have h1 := one_le_conductorExponent_of_not_isUnramifiedAt ψ v hram
    have hmem : v ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
      intro h
      have h' : v.asIdeal ^ conductorExponent ψ v ≤ v.asIdeal :=
        Ideal.pow_le_self (by omega)
      rw [h, Ideal.one_eq_top, top_le_iff] at h'
      exact v.isPrime.ne_top h'
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    exact dvd_pow_self _ (by omega)

end ArtinConductorSupport

end

namespace ArtinConductorNorm

open NumberField IsDedekindDomain ArtinL.Abelian ArtinConductorSupport
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

theorem exists_prime_natCast_mem (w : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have hmem : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
  have hn0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  rw [← Nat.prod_primeFactorsList hn0, Nat.cast_list_prod] at hmem
  obtain ⟨x, hx, hxw⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem w.isPrime _).1
    (by rw [Multiset.prod_coe]; exact hmem)
  rw [Multiset.mem_coe, List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q, Nat.prime_of_mem_primeFactorsList hq, hxw⟩

theorem liesOver_span_of_natCast_mem (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (hqw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : w.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := by
  refine ⟨?_⟩
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hq)).isMaximal (by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero)
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_)
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap,
    map_natCast]
  exact hqw

theorem not_natCast_mem_of_ne (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hqw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro hpw
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  obtain ⟨a, b, hab⟩ := hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * p + b * q : ℤ) : 𝓞 K) = 1 := by rw [hab, Int.cast_one]
  rw [← h1]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hqw)

end ArtinConductorNorm

open NumberField IsDedekindDomain ArtinL.Abelian ArtinConductorSupport ArtinConductorNorm in
open scoped Classical in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) (p : ℕ) (hp : p.Prime) :
    (Ideal.absNorm (ArtinL.Abelian.conductor ψ)).factorization p =
      ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        if ((p : ℕ) : 𝓞 K) ∈ w.asIdeal then
          (Ideal.span {(p : ℤ)}).inertiaDeg' w.asIdeal * ArtinL.Abelian.conductorExponent ψ w
        else 0 := by
  classical
  have hfin := hasFiniteMulSupport_of_finite ψ (finite_setOf_not_isUnramifiedAt ψ)
  have hconductor : ArtinL.Abelian.conductor ψ =
      ∏ w ∈ hfin.toFinset, w.asIdeal ^ ArtinL.Abelian.conductorExponent ψ w := by
    unfold ArtinL.Abelian.conductor
    exact finprod_eq_prod _ hfin
  have hne : ∀ w ∈ hfin.toFinset, Ideal.absNorm (w.asIdeal ^ ArtinL.Abelian.conductorExponent ψ w) ≠ 0 := by
    intro w _
    rw [map_pow]
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  rw [hconductor, map_prod, Nat.factorization_prod_apply hne]
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · refine Finset.sum_congr rfl fun w _ => ?_
    obtain ⟨q, hq, hqw⟩ := exists_prime_natCast_mem w
    haveI := liesOver_span_of_natCast_mem w hq hqw
    rw [map_pow, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Ideal.absNorm_eq_pow_inertiaDeg' w.asIdeal hq, hq.factorization_pow, Finsupp.single_apply]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, if_pos hqw, mul_comm]
    · rw [if_neg (fun h => hpq h.symm), mul_zero, if_neg (not_natCast_mem_of_ne w hp hq hpq hqw)]
  · intro w hw
    rw [Function.mem_support] at hw
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    have hf0 : ArtinL.Abelian.conductorExponent ψ w = 0 := by
      by_contra hne0
      have h' : w.asIdeal ^ ArtinL.Abelian.conductorExponent ψ w ≤ w.asIdeal := Ideal.pow_le_self hne0
      rw [h1, Ideal.one_eq_top, top_le_iff] at h'
      exact w.isPrime.ne_top h'
    rw [hf0, mul_zero, ite_self]

end S_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
end P2MW
export P2MW.S_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent (solution)
