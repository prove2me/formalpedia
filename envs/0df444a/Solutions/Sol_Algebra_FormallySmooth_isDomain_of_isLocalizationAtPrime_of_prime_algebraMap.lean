-- Prove2me | solution 1 for Algebra.FormallySmooth.isDomain_of_isLocalizationAtPrime_of_prime_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c18e7b52-6b9d-5ad9-9df1-ebf596df3c30

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap

set_option autoImplicit false

open IsLocalRing

theorem solution
    {A B S : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (hprime : Prime (algebraMap A B ϖ))
    (𝔫 : Ideal B) [𝔫.IsMaximal] (hϖ𝔫 : algebraMap A B ϖ ∈ 𝔫)
    [CommRing S] [Algebra B S] [IsLocalization.AtPrime S 𝔫] [IsLocalRing S] :
    IsDomain S := by
  classical

  haveI : Algebra.Smooth A B := {}
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔫.primeCompl S inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat B S := IsLocalization.flat S 𝔫.primeCompl
  haveI : Module.Flat A S := Module.Flat.trans A B S
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hϖ
    exact IsDiscreteValuationRing.not_isField A ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hϖ)
  set π : S := algebraMap B S (algebraMap A B ϖ) with hπ
  have hπA : ∀ s : S, ϖ • s = π * s := fun s => Algebra.smul_def ϖ s

  have hreg : ∀ s : S, π * s = 0 → s = 0 := by
    intro s hs
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) (mem_nonZeroDivisors_of_ne_zero hϖ0)
    exact this (by show ϖ • s = ϖ • (0 : S); rw [hπA, hs, hπA, mul_zero])
  have hregpow : ∀ (n : ℕ) (s : S), π ^ n * s = 0 → s = 0 := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      rw [pow_succ, mul_assoc] at hs
      exact hreg _ (ih _ hs)

  have hπ𝔪 : π ∈ maximalIdeal S := by
    rw [hπ]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔫 _).mpr hϖ𝔫
  have hπ0 : π ≠ 0 := fun h0 => by
    have := hreg 1 (by rw [h0, zero_mul])
    exact one_ne_zero this
  have hπprime : Prime π := by
    have hdisj : Disjoint (𝔫.primeCompl : Set B) (Ideal.span {algebraMap A B ϖ} : Set B) := by
      rw [Set.disjoint_left]
      intro b hb hb'
      exact hb ((Ideal.span_singleton_le_iff_mem _).mpr hϖ𝔫 hb')
    haveI : (Ideal.span {algebraMap A B ϖ}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    have hP : ((Ideal.span {algebraMap A B ϖ}).map (algebraMap B S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint 𝔫.primeCompl S _ inferInstance hdisj
    rw [Ideal.map_span, Set.image_singleton] at hP
    exact (Ideal.span_singleton_prime hπ0).mp hP

  have hkrull : ⨅ n : ℕ, (Ideal.span {π}) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (fun h => hπprime.not_unit
      (Ideal.span_singleton_eq_top.mp h))
  have hdecomp : ∀ a : S, a ≠ 0 → ∃ (m : ℕ) (a' : S), a = π ^ m * a' ∧ ¬ π ∣ a' := by
    intro a ha
    have hex : ∃ n : ℕ, ¬ π ^ n ∣ a := by
      by_contra hall
      push_neg at hall
      apply ha
      have : a ∈ ⨅ n : ℕ, (Ideal.span {π}) ^ n := by
        rw [Submodule.mem_iInf]; intro n
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact hall n
      rwa [hkrull, Submodule.mem_bot] at this
    let k := Nat.find hex
    have hk : ¬ π ^ k ∣ a := Nat.find_spec hex
    have hk0 : k ≠ 0 := fun h => hk (by rw [h, pow_zero]; exact one_dvd a)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hdvd : π ^ m ∣ a := by
      have := Nat.find_min hex (show m < k by omega)
      push_neg at this; exact this
    obtain ⟨a', ha'⟩ := hdvd
    refine ⟨m, a', ha', fun hd => hk ?_⟩
    rw [hm, pow_succ, ha']
    exact mul_dvd_mul_left _ hd

  haveI : NoZeroDivisors S := ⟨fun {a b} hab => by
    by_contra hne
    push_neg at hne
    obtain ⟨ha, hb⟩ := hne
    obtain ⟨m, a', rfl, ha'⟩ := hdecomp a ha
    obtain ⟨k, b', rfl, hb'⟩ := hdecomp b hb
    have : π ^ (m + k) * (a' * b') = 0 := by rw [← hab]; ring
    have h0 := hregpow _ _ this
    rcases hπprime.dvd_or_dvd (show π ∣ a' * b' by rw [h0]; exact dvd_zero π) with h | h
    · exact ha' h
    · exact hb' h⟩
  exact NoZeroDivisors.to_isDomain S

end S_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap
end P2MW
export P2MW.S_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap (solution)
