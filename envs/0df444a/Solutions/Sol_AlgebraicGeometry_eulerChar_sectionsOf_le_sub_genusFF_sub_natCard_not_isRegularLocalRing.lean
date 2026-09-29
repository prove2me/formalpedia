-- Prove2me | solution 1 for AlgebraicGeometry.eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6af7c9e7-d02b-5b64-9ef2-70ec99f268a7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_le_add_sub_natCard_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra TopologicalSpace

namespace DIneqAux

noncomputable def coverPreimage {C X : Scheme.{u}} (i : C ⟶ X) [IsAffineHom i] (𝒱 : X.TwoAffineOpenCover) :
    C.TwoAffineOpenCover where
  U0 := i ⁻¹ᵁ 𝒱.U0
  U1 := i ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage i
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage i
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage i

theorem isReduced_image {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [IsReduced Y] : IsReduced f.image := by
  let V : X.affineOpens → f.image.Opens := fun U => f.imageι ⁻¹ᵁ (U : X.Opens)
  have hV : TopologicalSpace.IsOpenCover V := by
    show (⨆ U : X.affineOpens, f.imageι ⁻¹ᵁ (U : X.Opens)) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]; rfl
  haveI : ∀ U : X.affineOpens, IsReduced ((f.image.openCoverOfIsOpenCover V hV).X U) := fun U => by
    have hVa : IsAffineOpen (V U) := U.2.preimage f.imageι
    haveI : IsAffine ((f.image.openCoverOfIsOpenCover V hV).X U) := hVa
    haveI : _root_.IsReduced Γ((f.image.openCoverOfIsOpenCover V hV).X U, ⊤) :=
      isReduced_of_injective ((V U).topIso.hom ≫ f.toImage.app (V U)).hom
        ((f.toImage_app_injective U).comp (V U).topIso.commRingCatIsoToRingEquiv.injective)
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover f.image (f.image.openCoverOfIsOpenCover V hV)

theorem finrank_sectionsOf_pullback_unit_eq {R : Type u} [CommRing R] {C X : Scheme.{u}} (i : C ⟶ X)
    (c : C ⟶ Spec (CommRingCat.of R)) (𝒱 : C.TwoAffineOpenCover) :
    Module.finrank R (𝒱.sectionsOf c ((Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf))).H0 =
      Module.finrank R (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H0 ∧
    Module.finrank R (𝒱.sectionsOf c ((Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf))).H1 =
      Module.finrank R (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H1 := by
  obtain ⟨𝒲, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso c c (Iso.refl C)
      (Category.id_comp c) 𝒱 (SheafOfModules.unit C.ringCatSheaf)
      ((Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf))
      (Scheme.Modules.pullbackUnitIso i ≪≫ (Scheme.Modules.pullbackUnitIso (𝟙 C)).symm)
  have h𝒲 : 𝒲 = 𝒱 := by
    rcases 𝒲 with ⟨U0, U1, _, _, _, _⟩
    rcases 𝒱 with ⟨V0, V1, _, _, _, _⟩
    simp only [Iso.refl_hom, Scheme.Hom.id_preimage] at h0 h1
    subst h0; subst h1; rfl
  subst h𝒲
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem isIso_stalkMap_of_mem_interior_range {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsReduced X]
    (c : C) (hc : i c ∈ interior (Set.range i)) : IsIso (i.stalkMap c) := by
  classical
  have hsurj : Function.Surjective (i.stalkMap c) := i.stalkMap_surjective c
  suffices hinj : Function.Injective (i.stalkMap c) from
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  rw [Scheme.Hom.germ_stalkMap_apply] at hg

  obtain ⟨W', hcW', ιU, ιV, hW'⟩ := TopCat.Presheaf.germ_eq C.presheaf (U := i ⁻¹ᵁ U) (V := i ⁻¹ᵁ U) c hxU hxU (i.app U s) 0
    (by rw [hg, map_zero])
  rw [map_zero] at hW'

  obtain ⟨W₀, hW₀open, hW₀⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W'.2

  let V : X.Opens := U ⊓ ⟨W₀, hW₀open⟩ ⊓ ⟨interior (Set.range i), isOpen_interior⟩
  have hcV : i c ∈ V := ⟨⟨hxU, by show i c ∈ W₀; rw [← Set.mem_preimage, show (i ⁻¹' W₀) = (W' : Set C) from hW₀]; exact hcW'⟩, hc⟩
  have hVU : V ≤ U := inf_le_left.trans inf_le_left

  have hsV : X.presheaf.map (homOfLE hVU).op s = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Scheme.mem_basicOpen''] at hy
    obtain ⟨hyV, hunit⟩ := hy
    exfalso

    obtain ⟨c', rfl⟩ : y ∈ Set.range i := interior_subset hyV.2
    have hc'W' : c' ∈ W' := by
      have h' : c' ∈ i ⁻¹' W₀ := hyV.1.2
      rw [hW₀] at h'
      exact h'

    have h0 : i.stalkMap c' (X.presheaf.germ U (i c') hyV.1.1 s) = 0 := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      have := TopCat.Presheaf.germ_res_apply C.presheaf ιU c' hc'W' (i.app U s)
      rw [← this, hW', map_zero]
    have hu : IsUnit (i.stalkMap c' (X.presheaf.germ U (i c') hyV.1.1 s)) := by
      rw [TopCat.Presheaf.germ_res_apply] at hunit
      exact hunit.map _
    rw [h0] at hu
    exact not_isUnit_zero hu

  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) (i c) hcV s, hsV, map_zero]

theorem isRegularLocalRing_stalk_iff_of_mem_interior_range {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsReduced X] (c : C) (hc : i c ∈ interior (Set.range i)) :
    IsRegularLocalRing (X.presheaf.stalk (i c)) ↔ IsRegularLocalRing (C.presheaf.stalk c) := by
  haveI := isIso_stalkMap_of_mem_interior_range i c hc
  let e : X.presheaf.stalk (i c) ≃+* C.presheaf.stalk c := (asIso (i.stalkMap c)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩

theorem natCard_not_isRegularLocalRing_le {X C₁ C₂ : Scheme.{u}} [IsReduced X] (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcov : ∀ z : X, z ∈ Set.range i₁ ∨ z ∈ Set.range i₂) [Finite ↥(Limits.pullback i₁ i₂)] :
    Nat.card {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)} ≤
      Nat.card {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} +
        Nat.card {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} + Nat.card ↥(Limits.pullback i₁ i₂) := by
  classical

  have hint₁ : ∀ z : X, z ∉ Set.range i₂ → z ∈ interior (Set.range i₁) := by
    intro z hz
    refine mem_interior.mpr ⟨(Set.range i₂)ᶜ, fun y hy => (hcov y).resolve_right hy,
      i₂.isClosedEmbedding.isClosed_range.isOpen_compl, hz⟩
  have hint₂ : ∀ z : X, z ∉ Set.range i₁ → z ∈ interior (Set.range i₂) := by
    intro z hz
    refine mem_interior.mpr ⟨(Set.range i₁)ᶜ, fun y hy => (hcov y).resolve_left hy,
      i₁.isClosedEmbedding.isClosed_range.isOpen_compl, hz⟩

  have hlift : ∀ z : X, z ∈ Set.range i₁ → z ∈ Set.range i₂ →
      ∃ w : ↥(Limits.pullback i₁ i₂), (Limits.pullback.fst i₁ i₂ ≫ i₁) w = z := by
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) a b (ha.trans hb.symm)
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hw, ha]⟩

  by_cases hfin₁ : Finite {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)}
  swap
  ·
    rw [not_finite_iff_infinite] at hfin₁
    have hsub : Finite {c : C₁ // i₁ c ∈ Set.range i₂} := by
      have h : ∀ c : {c : C₁ // i₁ c ∈ Set.range i₂}, ∃ w : ↥(Limits.pullback i₁ i₂), Limits.pullback.fst i₁ i₂ w = c.1 := by
        rintro ⟨c, b, hb⟩
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c b hb.symm
        exact ⟨w, hw⟩
      choose φ hφ using h
      exact Finite.of_injective φ fun c c' h => Subtype.ext (by rw [← hφ c, ← hφ c', h])

    have hinf : Infinite {c : {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} // i₁ c.1 ∉ Set.range i₂} := by
      by_contra hcon
      rw [not_infinite_iff_finite] at hcon
      haveI := hsub
      have : Finite {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} := by
        refine Finite.of_injective (β := {c : {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} // i₁ c.1 ∉ Set.range i₂} ⊕ {c : C₁ // i₁ c ∈ Set.range i₂})
          (fun c => if h : i₁ c.1 ∈ Set.range i₂ then Sum.inr ⟨c.1, h⟩ else Sum.inl ⟨c, h⟩) ?_
        intro c c' h
        by_cases hc : i₁ c.1 ∈ Set.range i₂ <;> by_cases hc' : i₁ c'.1 ∈ Set.range i₂ <;>
          simp only [hc, hc', dif_pos, dif_neg, not_false_eq_true, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at h
        · exact Subtype.ext (Subtype.mk.inj h)
        · exact Subtype.mk.inj h
      exact not_finite_iff_infinite.mpr hfin₁ this
    haveI : Infinite {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)} := by
      refine Infinite.of_injective
        (fun c : {c : {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} // i₁ c.1 ∉ Set.range i₂} =>
          (⟨i₁ c.1.1, fun hreg => c.1.2
            ((isRegularLocalRing_stalk_iff_of_mem_interior_range i₁ c.1.1 (hint₁ _ c.2)).mp hreg)⟩ :
            {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)})) ?_
      intro c c' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (i₁.isClosedEmbedding.injective this))
    rw [Nat.card_eq_zero_of_infinite]; exact Nat.zero_le _
  by_cases hfin₂ : Finite {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)}
  swap
  · rw [not_finite_iff_infinite] at hfin₂
    have hsub : Finite {c : C₂ // i₂ c ∈ Set.range i₁} := by
      have h : ∀ c : {c : C₂ // i₂ c ∈ Set.range i₁}, ∃ w : ↥(Limits.pullback i₁ i₂), Limits.pullback.snd i₁ i₂ w = c.1 := by
        rintro ⟨c, a, ha⟩
        obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) a c ha
        exact ⟨w, hw⟩
      choose φ hφ using h
      exact Finite.of_injective φ fun c c' h => Subtype.ext (by rw [← hφ c, ← hφ c', h])
    have hinf : Infinite {c : {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} // i₂ c.1 ∉ Set.range i₁} := by
      by_contra hcon
      rw [not_infinite_iff_finite] at hcon
      haveI := hsub
      have : Finite {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} := by
        refine Finite.of_injective (β := {c : {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} // i₂ c.1 ∉ Set.range i₁} ⊕ {c : C₂ // i₂ c ∈ Set.range i₁})
          (fun c => if h : i₂ c.1 ∈ Set.range i₁ then Sum.inr ⟨c.1, h⟩ else Sum.inl ⟨c, h⟩) ?_
        intro c c' h
        by_cases hc : i₂ c.1 ∈ Set.range i₁ <;> by_cases hc' : i₂ c'.1 ∈ Set.range i₁ <;>
          simp only [hc, hc', dif_pos, dif_neg, not_false_eq_true, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at h
        · exact Subtype.ext (Subtype.mk.inj h)
        · exact Subtype.mk.inj h
      exact not_finite_iff_infinite.mpr hfin₂ this
    haveI : Infinite {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)} := by
      refine Infinite.of_injective
        (fun c : {c : {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} // i₂ c.1 ∉ Set.range i₁} =>
          (⟨i₂ c.1.1, fun hreg => c.1.2
            ((isRegularLocalRing_stalk_iff_of_mem_interior_range i₂ c.1.1 (hint₂ _ c.2)).mp hreg)⟩ :
            {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)})) ?_
      intro c c' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (i₂.isClosedEmbedding.injective this))
    rw [Nat.card_eq_zero_of_infinite]; exact Nat.zero_le _

  haveI := hfin₁; haveI := hfin₂
  choose ψ hψ using hlift
  let T := ({c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} ⊕
    {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)}) ⊕ ↥(Limits.pullback i₁ i₂)
  have hcardT : Nat.card T = Nat.card {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} +
      Nat.card {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} + Nat.card ↥(Limits.pullback i₁ i₂) := by
    simp only [T, Nat.card_sum]
  rw [← hcardT]

  have key : ∀ z : {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)}, ∃ t : T,
      (match t with
        | Sum.inl (Sum.inl c) => i₁ c.1
        | Sum.inl (Sum.inr c) => i₂ c.1
        | Sum.inr w => (Limits.pullback.fst i₁ i₂ ≫ i₁) w) = z.1 := by
    rintro ⟨z, hz⟩
    by_cases h₁ : z ∈ Set.range i₁ <;> by_cases h₂ : z ∈ Set.range i₂
    · exact ⟨Sum.inr (ψ z h₁ h₂), hψ z h₁ h₂⟩
    · obtain ⟨c, rfl⟩ := h₁
      exact ⟨Sum.inl (Sum.inl ⟨c, fun hreg => hz
        ((isRegularLocalRing_stalk_iff_of_mem_interior_range i₁ c (hint₁ _ h₂)).mpr hreg)⟩), rfl⟩
    · obtain ⟨c, rfl⟩ := h₂
      exact ⟨Sum.inl (Sum.inr ⟨c, fun hreg => hz
        ((isRegularLocalRing_stalk_iff_of_mem_interior_range i₂ c (hint₂ _ h₁)).mpr hreg)⟩), rfl⟩
    · exact absurd (hcov z) (not_or.mpr ⟨h₁, h₂⟩)
  choose F hF using key
  exact Nat.card_le_card_of_injective F fun z z' h => Subtype.ext (by rw [← hF z, ← hF z', h])

end DIneqAux

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] [IsReduced X]
    {F₁ F₂ : Type v} [Field F₁] [Algebra k F₁] [Field F₂] [Algebra k F₂]
    (M₁ : AlgebraicCurve.CurveModel k F₁) (M₂ : AlgebraicCurve.CurveModel k F₂)
    (ν₁ : M₁.C ⟶ X) (ν₂ : M₂.C ⟶ X) (hν₁ : ν₁ ≫ x = M₁.toBase) (hν₂ : ν₂ ≫ x = M₂.toBase)
    (hcover : Set.range ν₁.base ∪ Set.range ν₂.base = Set.univ)
    (hfin : (Set.range ν₁.base ∩ Set.range ν₂.base).Finite)
    (hbir₁ : IsIso (ν₁.stalkMap (genericPoint M₁.C)))
    (hbir₂ : IsIso (ν₂.stalkMap (genericPoint M₂.C)))
    (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H1 ≤
      (1 - (AlgebraicCurve.genusFF k F₁ : ℤ)) + (1 - (AlgebraicCurve.genusFF k F₂ : ℤ)) -
        (Nat.card {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)} : ℤ) := by
  classical

  haveI : IsProper ν₁ := by
    have : IsProper (ν₁ ≫ x) := hν₁ ▸ inferInstance
    exact IsProper.of_comp ν₁ x
  haveI : IsProper ν₂ := by
    have : IsProper (ν₂ ≫ x) := hν₂ ▸ inferInstance
    exact IsProper.of_comp ν₂ x

  let C₁ : Scheme.{u} := ν₁.image
  let C₂ : Scheme.{u} := ν₂.image
  let i₁ : C₁ ⟶ X := ν₁.imageι
  let i₂ : C₂ ⟶ X := ν₂.imageι
  let c₁ : C₁ ⟶ Spec (CommRingCat.of k) := i₁ ≫ x
  let c₂ : C₂ ⟶ Spec (CommRingCat.of k) := i₂ ≫ x
  let ν₁' : M₁.C ⟶ C₁ := ν₁.toImage
  let ν₂' : M₂.C ⟶ C₂ := ν₂.toImage
  have hfac₁ : ν₁' ≫ i₁ = ν₁ := ν₁.toImage_imageι
  have hfac₂ : ν₂' ≫ i₂ = ν₂ := ν₂.toImage_imageι
  haveI : Surjective ν₁' := inferInstance
  haveI : Surjective ν₂' := inferInstance
  haveI : IrreducibleSpace C₁ := ν₁'.surjective.irreducibleSpace ν₁'.continuous
  haveI : IrreducibleSpace C₂ := ν₂'.surjective.irreducibleSpace ν₂'.continuous
  haveI : IsReduced C₁ := DIneqAux.isReduced_image ν₁
  haveI : IsReduced C₂ := DIneqAux.isReduced_image ν₂
  haveI : IsIntegral C₁ := isIntegral_of_irreducibleSpace_of_isReduced C₁
  haveI : IsIntegral C₂ := isIntegral_of_irreducibleSpace_of_isReduced C₂
  have hbir' : ∀ {C : Scheme.{u}} {Y : Scheme.{u}} (f : Y ⟶ C) (g : C ⟶ X) [IsClosedImmersion g] (y : Y),
      IsIso ((f ≫ g).stalkMap y) → IsIso (f.stalkMap y) := by
    intro C Y f g _ y hc
    haveI := hc
    have hbij : Function.Bijective ((f ≫ g).stalkMap y) := ConcreteCategory.bijective_of_isIso _
    rw [Scheme.Hom.stalkMap_comp] at hbij
    have hsurj : Function.Surjective (g.stalkMap (f y)) := g.stalkMap_surjective (f y)
    have hinj : Function.Injective (g.stalkMap (f y)) := by
      apply Function.Injective.of_comp (f := (f.stalkMap y))
      exact hbij.1
    haveI : IsIso (g.stalkMap (f y)) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    haveI : IsIso (g.stalkMap (f y) ≫ f.stalkMap y) := by
      rw [← Scheme.Hom.stalkMap_comp]; exact hc
    exact IsIso.of_isIso_comp_left (g.stalkMap (f y)) (f.stalkMap y)
  have hbir₁' : IsIso (ν₁'.stalkMap (genericPoint M₁.C)) :=
    hbir' ν₁' i₁ _ (by rw [hfac₁]; exact hbir₁)
  have hbir₂' : IsIso (ν₂'.stalkMap (genericPoint M₂.C)) :=
    hbir' ν₂' i₂ _ (by rw [hfac₂]; exact hbir₂)

  let 𝒱₁ := DIneqAux.coverPreimage i₁ 𝒱
  let 𝒱₂ := DIneqAux.coverPreimage i₂ 𝒱

  have h₁ := AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing k c₁ M₁ ν₁' (by rw [← Category.assoc, hfac₁, hν₁]) hbir₁' 𝒱₁
  have h₂ := AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing k c₂ M₂ ν₂' (by rw [← Category.assoc, hfac₂, hν₂]) hbir₂' 𝒱₂

  let I₁ : SchemeHomOver c₁ x := ⟨i₁, rfl⟩
  let I₂ : SchemeHomOver c₂ x := ⟨i₂, rfl⟩

  have hrange : ∀ {C : Scheme.{u}} {Y : Scheme.{u}} (f : Y ⟶ C) (g : C ⟶ X), Function.Surjective f.base →
      Set.range (f ≫ g).base = Set.range g.base := by
    intro C Y f g hf
    ext z; constructor
    · rintro ⟨y, rfl⟩; exact ⟨f.base y, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨c, rfl⟩; obtain ⟨y, rfl⟩ := hf c; exact ⟨y, by rw [Scheme.Hom.comp_apply]⟩
  have hr₁ : Set.range ν₁.base = Set.range i₁.base := by
    rw [← hrange ν₁' i₁ ν₁'.surjective, hfac₁]
  have hr₂ : Set.range ν₂.base = Set.range i₂.base := by
    rw [← hrange ν₂' i₂ ν₂'.surjective, hfac₂]
  have hcov : ∀ z : X, z ∈ Set.range I₁.1.base ∨ z ∈ Set.range I₂.1.base := by
    intro z
    have hz : z ∈ Set.range ν₁.base ∪ Set.range ν₂.base := hcover ▸ Set.mem_univ z
    rcases hz with h | h
    · exact Or.inl (hr₁ ▸ h)
    · exact Or.inr (hr₂ ▸ h)

  have hinjP : Function.Injective (pullback.fst I₁.1 I₂.1 ≫ I₁.1).base :=
    (pullback.fst I₁.1 I₂.1 ≫ I₁.1).isClosedEmbedding.injective
  have hmemP : ∀ w : ↥(pullback I₁.1 I₂.1),
      (pullback.fst I₁.1 I₂.1 ≫ I₁.1).base w ∈ Set.range ν₁.base ∩ Set.range ν₂.base := by
    intro w
    refine ⟨hr₁ ▸ ⟨(pullback.fst I₁.1 I₂.1).base w, by rw [Scheme.Hom.comp_apply]⟩,
      hr₂ ▸ ⟨(pullback.snd I₁.1 I₂.1).base w, ?_⟩⟩
    rw [Scheme.Hom.comp_apply]
    show (pullback.snd I₁.1 I₂.1 ≫ i₂).base w = (pullback.fst I₁.1 I₂.1 ≫ i₁).base w
    rw [← pullback.condition]
  have hfinP : Finite ↥(pullback I₁.1 I₂.1) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun w => (⟨_, hmemP w⟩ : ↥(Set.range ν₁.base ∩ Set.range ν₂.base)))
      (fun w w' h => hinjP (by have h' := congrArg Subtype.val h; dsimp only at h'; exact h'))
  have hfin : Finite ↥(pullback I₁.1 I₂.1) := hfinP
  have hinv : Scheme.Modules.IsInvertible (SheafOfModules.unit X.ringCatSheaf) :=
    Scheme.Modules.isInvertible_unit X
  have hMV := AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_le_add_sub_natCard_of_isInvertible k x c₁ c₂ I₁ I₂ hcov hfin _ rfl (SheafOfModules.unit X.ringCatSheaf) hinv 𝒱 𝒱₁ 𝒱₂

  have hunit₁ : ((Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback I₁.1).obj
        (SheafOfModules.unit X.ringCatSheaf))).H0 : ℤ) -
      Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback I₁.1).obj
        (SheafOfModules.unit X.ringCatSheaf))).H1) =
      (Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf)).H0 : ℤ) -
        Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf)).H1 := by
    obtain ⟨e0, e1⟩ := DIneqAux.finrank_sectionsOf_pullback_unit_eq I₁.1 c₁ 𝒱₁
    rw [e0, e1]
  have hunit₂ : ((Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback I₂.1).obj
        (SheafOfModules.unit X.ringCatSheaf))).H0 : ℤ) -
      Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback I₂.1).obj
        (SheafOfModules.unit X.ringCatSheaf))).H1) =
      (Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf)).H0 : ℤ) -
        Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf)).H1 := by
    obtain ⟨e0, e1⟩ := DIneqAux.finrank_sectionsOf_pullback_unit_eq I₂.1 c₂ 𝒱₂
    rw [e0, e1]

  have hN : (Nat.card {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)} : ℤ) ≤
      Nat.card {c : C₁ // ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} +
        Nat.card {c : C₂ // ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} + Nat.card ↥(pullback I₁.1 I₂.1) := by
    haveI := hfinP
    exact_mod_cast DIneqAux.natCard_not_isRegularLocalRing_le I₁.1 I₂.1 hcov
  linarith [hMV, h₁, h₂, hunit₁, hunit₂, hN]

#print axioms solution

end S_AlgebraicGeometry_eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing (solution)
