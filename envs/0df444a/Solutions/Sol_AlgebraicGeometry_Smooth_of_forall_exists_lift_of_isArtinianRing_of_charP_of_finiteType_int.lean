-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f6c7700f-ea2f-5dec-ad4d-7dc0e89cabcf

import Mathlib
import Theorems.Thm_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
import Theorems.Thm_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift
import Theorems.Thm_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift
import Theorems.Thm_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace SmoothCritAux

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_sInf_maximal]
  intro I hI
  by_cases h0 : I = ⊥
  · refine ⟨{J : Ideal ℤ | J.IsMaximal}, fun J hJ => Or.inl hJ, ?_⟩
    rw [h0]
    apply le_antisymm bot_le
    intro n hn
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := IsPrime.to_maximal_ideal hp0
    have hmem : n ∈ Ideal.span {(p : ℤ)} := (Submodule.mem_sInf.mp hn) _ hmax
    rw [Ideal.mem_span_singleton] at hmem
    have hdvd : p ∣ n.natAbs := Int.natCast_dvd.mp hmem
    have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hne
    have := Nat.le_of_dvd hpos hdvd
    omega
  · haveI := hI
    exact ⟨{I}, fun J hJ => Or.inl (by rw [Set.mem_singleton_iff.mp hJ]; exact IsPrime.to_maximal_ideal h0), by simp⟩

end SmoothCritAux

theorem solution
    {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType ϖ]
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    Smooth ϖ := by
  classical
  haveI : IsJacobsonRing ℤ := SmoothCritAux.int_isJacobsonRing
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ) (B := R)
  haveI : JacobsonSpace ↥M := LocallyOfFiniteType.jacobsonSpace ϖ
  haveI : LocallyOfFinitePresentation ϖ := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  apply AlgebraicGeometry.smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap ϖ
  intro x hx

  obtain ⟨n, I, J, hIJ, hJ, hJI, ι, hιopen, hι, -, himp⟩ := AlgebraicGeometry.Scheme.exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization ϖ x hx
  apply himp
  haveI := hιopen
  haveI := hJ

  have hlift := AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion ϖ I ι hι h
  obtain ⟨D, iR, iA, iC, iT, iF, σ, hσ⟩ := MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift R I J hIJ hJ hlift
  letI := iR; letI := iA; letI := iC; haveI := iT; haveI := iF

  exact MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem R I J hIJ (fun v hv hdv => MvPolynomial.mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift R I J hIJ hJ D σ hσ v hv hdv)

end S_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int (solution)
