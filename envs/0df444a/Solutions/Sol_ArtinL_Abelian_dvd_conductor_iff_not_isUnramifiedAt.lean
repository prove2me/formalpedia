-- Prove2me | solution 1 for ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/dee9309b-3f29-59cc-8ba0-ad54ce4c8ef6

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt

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

universe u v

open NumberField IsDedekindDomain in
theorem solution
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ ArtinL.Abelian.conductor ψ ↔ ¬ ArtinL.Abelian.IsUnramifiedAt ψ v :=
  ArtinConductorSupport.dvd_conductor_iff ψ v

end S_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt
end P2MW
export P2MW.S_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt (solution)
