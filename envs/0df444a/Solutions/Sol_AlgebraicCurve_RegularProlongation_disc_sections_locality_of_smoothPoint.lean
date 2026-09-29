-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.disc_sections_locality_of_smoothPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/005a50c9-1903-547c-a024-b3d3137274ec

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver

import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc
import Theorems.Thm_AlgebraicCurve_RegularProlongation_existsUnique_mem_disc_forall_evalAt_eq_of_section
import Theorems.Thm_AlgebraicCurve_RegularProlongation_locality_of_disc_of_smoothPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_disc_sections_locality_of_smoothPoint
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F] [IsScalarTower k₀ L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (F₀ : IntermediateField k₀ F)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)

    (K₁ : IntermediateField k₀ L) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A) (D₁ : Set (Place L F))
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))

    (ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c))
    (hlocal : IsLocalRing ↥S₁) (hmax : ∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0)
    (hnoeth : IsNoetherianRing ↥S₁) (hufd : UniqueFactorizationMonoid ↥S₁)
    (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
    (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
    (hld : ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
      LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
    (hdvr : ∀ O : ValuationSubring F, (∀ x : L, algebraMap L F x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O)
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (hprime : Prime (φ₁ (Polynomial.C ϖ)))
    (hRint : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F)))

    (hker : ∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))})

    (hbranch : ∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x) :

    (∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      ∃! P, P ∈ D₁ ∧ ∀ f : ↥S₁, P.evalAt (f : F) = ((χ f : ↥K₁) : L)) ∧

    (∀ P ∈ D₁, ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ P.toValuationSubring ↔ ∃ g h : ↥S₁, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F))) ∧

    (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → f ≠ 0 → (∀ P ∈ D₁, P.ord f = 0) →
      ∃ (c : ↥K₁) (u : (↥S₁)ˣ), c ≠ 0 ∧ algebraMap L F (c : L) * f = ((u : ↥S₁) : F)) ∧

    (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → f ∈ R.integers → (∀ P ∈ D₁, f ∈ P.toValuationSubring) → f ∈ S₁) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro χ hχa hχr
    exact AlgebraicCurve.RegularProlongation.existsUnique_mem_disc_forall_evalAt_eq_of_section F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch χ hχa hχr
  · intro P hP f hf
    obtain ⟨p, hp, hpϖ, hzero, hval⟩ := AlgebraicCurve.RegularProlongation.exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch P hP
    rw [hval f hf]
    constructor
    · rintro ⟨g, h, hh, hfh⟩; exact ⟨g, h, fun h0 => hh ((hzero h).mp h0), hfh⟩
    · rintro ⟨g, h, hh, hfh⟩; exact ⟨g, h, fun hd => hh ((hzero h).mpr hd), hfh⟩
  · exact (AlgebraicCurve.RegularProlongation.locality_of_disc_of_smoothPoint F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch).1
  · exact (AlgebraicCurve.RegularProlongation.locality_of_disc_of_smoothPoint F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch).2

end S_AlgebraicCurve_RegularProlongation_disc_sections_locality_of_smoothPoint
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_disc_sections_locality_of_smoothPoint (solution)
