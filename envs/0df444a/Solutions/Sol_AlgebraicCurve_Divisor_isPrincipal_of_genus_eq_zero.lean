-- Prove2me | solution 1 for AlgebraicCurve.Divisor.isPrincipal_of_genus_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c61ce637-6965-57a2-afdd-7e3440851328

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_genus_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_genus_eq_zero.AlgebraicCurve IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Divisor Divisor.degree Divisor.IsPrincipal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite IsCurveOver HasCanonicalDivisor canonicalDivisorOf genus FunctionFieldRiemannRoch LSpace ell mem_lSpace_iff_ord dCoordGenerates_of_isCurveOver IsCurveOver.exists_separating_transcendental isCurveOver_ratFunc essFiniteType_of_transcendental_of_finiteDimensional functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver"
namespace GenusZeroPrincipal
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem eq_zero_of_nonneg_of_degree_eq_zero [∀ v : Place K F, v.FiniteResidue]
    {E : Divisor K F} (hE : 0 ≤ E) (hdeg : Divisor.degree E = 0) : E = 0 := by
  classical
  have hdegv : ∀ v : Place K F, 0 < (v.deg : ℤ) := fun v => by
    haveI : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
    have : 0 < v.deg := Module.finrank_pos
    exact_mod_cast this
  have hsum : Divisor.degree E = E.sum fun v n => n * (v.deg : ℤ) := by
    simp [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [hsum, Finsupp.sum] at hdeg
  have hterm : ∀ v ∈ E.support, E v * (v.deg : ℤ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun v _ =>
      mul_nonneg (hE v) (hdegv v).le).mp hdeg
  ext v
  by_cases hv : v ∈ E.support
  · have := hterm v hv
    rcases mul_eq_zero.mp this with h | h
    · simpa using h
    · exact absurd h (hdegv v).ne'
  · simpa [Finsupp.mem_support_iff] using hv

theorem isPrincipal_of_riemannRoch_of_genus_eq_zero
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (h0 : genus K F = 0)
    {D : Divisor K F} (hD : Divisor.degree D = 0) : Divisor.IsPrincipal D := by
  classical
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hRRD := hRR hω D
  rw [hD, h0] at hRRD
  simp only [Nat.cast_zero, sub_zero, zero_add] at hRRD
  have hpos : 0 < ell D := by
    have h1 : (1 : ℤ) ≤ (ell D : ℤ) := by
      have : (0 : ℤ) ≤ (ell (canonicalDivisorOf hω - D) : ℤ) := Nat.cast_nonneg _
      linarith
    exact_mod_cast h1
  haveI : Nontrivial (LSpace D) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨⟨f, hfL⟩, hf0⟩ := exists_ne (0 : LSpace D)
  have hf : f ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hford : ∀ v : Place K F, -D v ≤ v.ord f :=
    ((mem_lSpace_iff_ord (D := D)).mp hfL).resolve_left hf

  obtain ⟨P, hP, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf

  have hE : P + D = 0 := by
    refine eq_zero_of_nonneg_of_degree_eq_zero (fun v => ?_) (by rw [map_add, hPdeg, hD, add_zero])
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, hP v]
    linarith [hford v]
  have hDP : D = -P := by
    have := congrArg (fun X => X - P) hE
    simpa using this
  refine ⟨f⁻¹, inv_ne_zero hf, fun v => ?_⟩
  rw [hDP, Finsupp.neg_apply, hP v, v.ord_inv]

theorem functionFieldRiemannRoch [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] :
    FunctionFieldRiemannRoch K F := by
  classical
  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨t, ht, htfd, htsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := htfd
  haveI := htsep
  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D

end AlgebraicCurve.GenusZeroPrincipal

open AlgebraicCurve.GenusZeroPrincipal in
theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (h0 : genus K F = 0) {D : Divisor K F} (hD : Divisor.degree D = 0) :
    Divisor.IsPrincipal D := by
  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  exact isPrincipal_of_riemannRoch_of_genus_eq_zero functionFieldRiemannRoch h0 hD

end S_AlgebraicCurve_Divisor_isPrincipal_of_genus_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_genus_eq_zero (solution)
