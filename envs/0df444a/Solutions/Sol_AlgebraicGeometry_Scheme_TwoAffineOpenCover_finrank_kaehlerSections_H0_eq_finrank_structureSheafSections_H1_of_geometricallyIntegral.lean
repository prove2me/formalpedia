-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d54e5fc9-225e-5899-8491-df67e8c79fa4

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace L3Aux

universe v w

variable {R : Type u} [CommRing R] {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem baseChange_apply_eq_lTensor (f : M →ₗ[R] N) (A : Type w) [CommRing A] [Algebra R A] (x : A ⊗[R] M) :
    f.baseChange A x = f.lTensor A x :=
  congrFun (LinearMap.baseChange_eq_ltensor (f := f) (A := A)) x

theorem kerBaseChangeHom_bijective (d : M →ₗ[R] N) (A : Type w) [CommRing A] [Algebra R A] [Module.Flat R A] :
    Function.Bijective (TwoChartCech.kerBaseChangeHom d A) := by
  constructor
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, TwoChartCech.kerBaseChangeHom_apply_coe,
      baseChange_apply_eq_lTensor, baseChange_apply_eq_lTensor] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker d).injective_subtype h
  · intro z
    have hex := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map d)
    have hz : (d.lTensor A) (z : A ⊗[R] M) = 0 := by
      rw [← baseChange_apply_eq_lTensor]
      exact z.2
    obtain ⟨x, hx⟩ := (hex _).mp hz
    refine ⟨x, Subtype.ext ?_⟩
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, baseChange_apply_eq_lTensor]
    exact hx

theorem exists_quotRangeBaseChange_linearEquiv (d : M →ₗ[R] N) (A : Type w) [CommRing A] [Algebra R A] :
    Nonempty (((A ⊗[R] N) ⧸ LinearMap.range (d.baseChange A)) ≃ₗ[A] A ⊗[R] (N ⧸ LinearMap.range d)) := by
  let φ : A ⊗[R] N →ₗ[A] A ⊗[R] (N ⧸ LinearMap.range d) := (LinearMap.range d).mkQ.baseChange A

  have hle : LinearMap.range (d.baseChange A) ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have h0 : (LinearMap.range d).mkQ ∘ₗ d = 0 := by
      ext m
      simp
    rw [h0, LinearMap.baseChange_zero, LinearMap.zero_apply]
  let ψ : ((A ⊗[R] N) ⧸ LinearMap.range (d.baseChange A)) →ₗ[A] A ⊗[R] (N ⧸ LinearMap.range d) :=
    (LinearMap.range (d.baseChange A)).liftQ φ hle
  refine ⟨LinearEquiv.ofBijective ψ ⟨?_, ?_⟩⟩
  ·
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hq

    have hz : ((LinearMap.range d).mkQ.lTensor A) z = 0 := by rw [← baseChange_apply_eq_lTensor]; exact hq
    have hz' : z ∈ LinearMap.range (((LinearMap.range d).subtype).lTensor A) := by
      rw [← lTensor_mkQ]; exact LinearMap.mem_ker.2 hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨w', rfl⟩ := LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict d) w
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨w', ?_⟩
    rw [baseChange_apply_eq_lTensor, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  ·
    intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective A (Submodule.mkQ_surjective (LinearMap.range d)) y
    exact ⟨Submodule.Quotient.mk x, by rw [Submodule.liftQ_apply, baseChange_apply_eq_lTensor]; exact hx⟩

end L3Aux

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    Module.finrank K (𝒱.kaehlerSections c).H0 = Module.finrank K (𝒱.structureSheafSections c).H1 := by
  let Kb : Type u := AlgebraicClosure K
  haveI : IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap K Kb)) :=
    SmoothProperCurve.isIntegral_pullback_Spec_field (c := c) (ξ := Scheme.TwoAffineOpenCover.specMap K Kb)

  obtain ⟨_, _, _, eH0, _, -, -, -, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections 𝒱 c Kb
  obtain ⟨_, _, _, _, eH1, -, -, -, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c Kb

  have hΩ := (AlgebraicCurve.finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed (𝒱.pullback c Kb)
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap K Kb))).2
  have hO := (AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed (𝒱.pullback c Kb)
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap K Kb))).2.2.2

  have eK : Kb ⊗[K] (𝒱.kaehlerSections c).H0 ≃ₗ[Kb] LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange Kb) :=
    LinearEquiv.ofBijective _ (L3Aux.kerBaseChangeHom_bijective (𝒱.kaehlerSections c).cechDiff Kb)
  obtain ⟨eQ⟩ := L3Aux.exists_quotRangeBaseChange_linearEquiv (𝒱.structureSheafSections c).cechDiff Kb
  calc Module.finrank K (𝒱.kaehlerSections c).H0
      = Module.finrank Kb (Kb ⊗[K] (𝒱.kaehlerSections c).H0) := (Module.finrank_baseChange (R := Kb)).symm
    _ = Module.finrank Kb (LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange Kb)) := eK.finrank_eq
    _ = _ := eH0.finrank_eq
    _ = _ := hΩ
    _ = _ := hO.symm
    _ = _ := eH1.finrank_eq.symm
    _ = Module.finrank Kb (Kb ⊗[K] (𝒱.structureSheafSections c).H1) := eQ.finrank_eq
    _ = Module.finrank K (𝒱.structureSheafSections c).H1 := Module.finrank_baseChange (R := Kb)

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral (solution)
