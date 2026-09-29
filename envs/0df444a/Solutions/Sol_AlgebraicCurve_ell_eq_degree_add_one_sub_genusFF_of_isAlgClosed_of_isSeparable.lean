-- Prove2me | solution 1 for AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/61f21c19-de5a-5806-bf87-90b6b7aac3dd

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve KaehlerDifferential
open scoped IntermediateField

namespace E97cRRExact

set_option maxHeartbeats 6400000 in
theorem main (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by
  classical

  haveI hCO : IsCurveOver k F := isCurveOver_of_transcendental hx hfin hsep
  haveI : HasPrincipalDivisors k F := IsCurveOver.hasPrincipalDivisors

  let e := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc k) k⟮x⟯ := e.toAlgHom.toRingHom.toAlgebra
  letI : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc k) k⟮x⟯ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k (RatFunc k) k⟮x⟯ :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap k k⟮x⟯ r = e (algebraMap k (RatFunc k) r)
      rw [AlgEquiv.commutes]
  haveI : IsScalarTower k (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap k F r = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) r))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply k k⟮x⟯ F r
  haveI : Module.Finite (RatFunc k) k⟮x⟯ :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) k⟮x⟯) e.surjective
  haveI : FiniteDimensional k⟮x⟯ F := hfin
  haveI : Module.Finite (RatFunc k) F := Module.Finite.trans k⟮x⟯ F
  haveI : Algebra.IsIntegral (RatFunc k) F := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable k⟮x⟯ F := hsep
  haveI : Algebra.IsSeparable (RatFunc k) k⟮x⟯ :=
    Algebra.IsSeparable.of_algHom (RatFunc k) (RatFunc k)
      { e.symm.toRingEquiv.toRingHom with
        commutes' := fun r => by
          show e.symm (algebraMap (RatFunc k) k⟮x⟯ r) = r
          exact e.symm_apply_apply r }
  haveI : Algebra.IsSeparable (RatFunc k) F := Algebra.IsSeparable.trans (RatFunc k) k⟮x⟯ F

  haveI : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc k) (nonZeroDivisors (Polynomial k))
  haveI : Algebra.EssFiniteType k (RatFunc k) := Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  haveI : Algebra.EssFiniteType (RatFunc k) F := inferInstance
  haveI : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k (RatFunc k) F
  haveI hHCD : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI hDCG : ∀ w : Place k F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  haveI : IsCurveOver k (RatFunc k) := AlgebraicCurve.instIsCurveOverRatFunc k
  haveI hDCGR : ∀ v : Place k (RatFunc k), v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  have hRR : FunctionFieldRiemannRoch k F := functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
  have hC : ConstantsAreBase k F := constantsAreBase_of_isAlgClosed k F
  haveI : FiniteDimensional k (LSpace (0 : Divisor k F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase k F hC
  haveI : Nonempty (Place k F) := RationalFunctionField.nonempty_place_of_ratFunc_tower k F
  have hSG : StichtenothGenusExists k F := RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower k F
  have hWDA : WeilDualityAdelic k F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  have hg : genus k F = genusFF k F := genus_eq_genusFF hRR hWDA hC

  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄k])
  have hdegK : Divisor.degree (canonicalDivisorOf hω) = 2 * (genus k F : ℤ) - 2 :=
    degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω
  have hRRD : (ell D : ℤ) - (ell (canonicalDivisorOf hω - D) : ℤ) = Divisor.degree D + 1 - (genus k F : ℤ) :=
    hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hg]
    have : Divisor.degree D = D.degree := rfl
    linarith
  have hell0 : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank k ↥(LSpace (canonicalDivisorOf hω - D)) = 0
    rw [lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell0, hg, Nat.cast_zero, sub_zero] at hRRD
  exact hRRD

end E97cRRExact

end

open AlgebraicCurve in
open scoped IntermediateField in
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) :=
  E97cRRExact.main k x hx hfin hsep D hD

end S_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
end P2MW
export P2MW.S_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable (solution)
