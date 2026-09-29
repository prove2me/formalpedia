-- Prove2me | solution 1 for Algebra.Smooth.fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/77f8338c-59d1-5893-b704-11418213044d

import Mathlib
import Theorems.Thm_Algebra_Smooth_isIntegrallyClosed_of_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Smooth_fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime

set_option autoImplicit false

open IsLocalRing

theorem solution
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {F₀ : Type} [Field F₀] [Algebra A₀ F₀]
    (B : Subalgebra A₀ F₀) [Algebra.Smooth A₀ ↥B]
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)
    (hprime : (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).IsPrime)
    (hdim1 : Ring.KrullDimLE 1 (↥B ⧸ Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀))) :
    B.FG ∧
    (∀ x : F₀, IsIntegral ↥B x → x ∈ B) ∧
    (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
    (∀ (𝔪 : Ideal ↥B) [𝔪.IsPrime], (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) := by
  classical
  set I : Ideal ↥B := Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) with hI
  haveI : Algebra.FinitePresentation A₀ ↥B := Algebra.Smooth.finitePresentation
  haveI : Algebra.FormallySmooth A₀ ↥B := Algebra.Smooth.formallySmooth
  haveI : Algebra.FiniteType A₀ ↥B := Algebra.FiniteType.of_finitePresentation
  refine ⟨(Subalgebra.fg_iff_finiteType B).mpr inferInstance, ?_, ?_, ?_⟩
  ·
    haveI : IsIntegrallyClosed ↥B := Algebra.Smooth.isIntegrallyClosed_of_isDomain A₀ ↥B

    haveI : IsFractionRing ↥B F₀ := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        exact isUnit_iff_ne_zero.mpr (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hc) (Subtype.ext h))
      · intro x
        obtain ⟨b, c, hb, hc, hc0, hx⟩ := hBfrac x
        exact ⟨⟨⟨b, hb⟩, ⟨⟨c, hc⟩, mem_nonZeroDivisors_iff_ne_zero.mpr (fun h => hc0 (congrArg Subtype.val h))⟩⟩, hx⟩
      · intro a b h
        exact ⟨1, by simpa using Subtype.ext h⟩
    intro x hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
    rw [← hy]; exact y.2
  ·
    intro 𝔮 h𝔮 hI𝔮 hnm
    haveI := h𝔮
    haveI : I.IsPrime := hprime

    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔮 := by rw [Ideal.mk_ker]; exact hI𝔮
    haveI hP : (𝔮.map (Ideal.Quotient.mk I)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hcomap : (𝔮.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = 𝔮 := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    have hnm' : ¬ (𝔮.map (Ideal.Quotient.mk I)).IsMaximal := fun hM =>
      hnm (hcomap ▸ Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    have hmin : 𝔮.map (Ideal.Quotient.mk I) ∈ minimalPrimes (↥B ⧸ I) :=
      ((Ring.krullDimLE_one_iff.mp hdim1) _ hP).resolve_right hnm'
    haveI : IsDomain (↥B ⧸ I) := Ideal.Quotient.isDomain I
    have hbot : 𝔮.map (Ideal.Quotient.mk I) = ⊥ := by
      rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
      exact hmin
    have h𝔮I : 𝔮 = I := by
      rw [← hcomap, hbot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [h𝔮I, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton I
  ·
    intro 𝔪 _
    haveI : Algebra.FormallySmooth ↥B (Localization.AtPrime 𝔪) :=
      Algebra.FormallySmooth.of_isLocalization 𝔪.primeCompl
    haveI : Algebra.FormallySmooth A₀ (Localization.AtPrime 𝔪) :=
      Algebra.FormallySmooth.comp A₀ ↥B (Localization.AtPrime 𝔪)
    exact RingHom.formallySmooth_algebraMap.mpr inferInstance

end S_Algebra_Smooth_fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime
end P2MW
export P2MW.S_Algebra_Smooth_fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime (solution)
