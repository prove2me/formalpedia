-- Prove2me | solution 1 for AlgebraicCurve.Pic0.surjective_aeval_of_finite_ker_of_pushforwardAlong_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fa7748e0-7b03-5bc0-91f5-f091382d7ce2

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Pic0_exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_surjective_aeval_of_finite_ker_of_pushforwardAlong_frobenius
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve

universe u v

namespace P2mSurjLang

section EndCalculus

variable {K : Type u} [Field K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

def IsHom (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    (L.mul t x y) ⊚ β = L.mul t (x ⊚ β) (y ⊚ β)

theorem comp_mul (L : RelativeGroupLaw K f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t f) (β γ : SchemeHomOver f f) :
    z ⊚ (L.mul f β γ) = L.mul t (z ⊚ β) (z ⊚ γ) := by
  have h := L.mul_natural f t z.1 z.2 β γ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = z ⊚ δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

theorem comp_one (L : RelativeGroupLaw K f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t f) : z ⊚ (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) = z ⊚ (L.one f) := Subtype.ext rfl
  rw [e] at h
  exact h

theorem comp_inv (L : RelativeGroupLaw K f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t f) (β : SchemeHomOver f f) :
    z ⊚ (L.inv f β) = L.inv t (z ⊚ β) := by
  letI := L.pointGroup t
  have h : (z ⊚ (L.inv f β)) * (z ⊚ β) = 1 := by
    change L.mul _ (z ⊚ (L.inv f β)) (z ⊚ β) = L.one _
    rw [← comp_mul, L.inv_mul_cancel, comp_one]
  exact eq_inv_of_mul_eq_one_left h

theorem isHom_id (L : RelativeGroupLaw K f) : IsHom L (schemeHomOverId f) := by
  intro T t x y
  simp

theorem IsHom.comp {L : RelativeGroupLaw K f} {β γ : SchemeHomOver f f} (hβ : IsHom L β)
    (hγ : IsHom L γ) : IsHom L (β ⊚ γ) := by
  intro T t x y
  rw [← schemeHomOverComp_assoc, hβ, hγ, schemeHomOverComp_assoc, schemeHomOverComp_assoc]

theorem IsHom.npow {L : RelativeGroupLaw K f} {β : SchemeHomOver f f} (hβ : IsHom L β) (i : ℕ) :
    IsHom L (schemeHomOverNpow β i) := by
  induction i with
  | zero => exact isHom_id L
  | succ i ih => exact ih.comp hβ

theorem isHom_one (L : RelativeGroupLaw K f) : IsHom L (L.one f) := by
  intro T t x y
  rw [comp_one, comp_one, comp_one, L.one_mul]

theorem IsHom.mul {L : RelativeGroupLaw K f} (hc : L.IsCommutative) {β γ : SchemeHomOver f f}
    (hβ : IsHom L β) (hγ : IsHom L γ) : IsHom L (L.mul f β γ) := by
  intro T t x y
  letI := L.pointCommGroup hc t
  rw [comp_mul, comp_mul, comp_mul, hβ, hγ]
  exact mul_mul_mul_comm (x ⊚ β) (y ⊚ β) (x ⊚ γ) (y ⊚ γ)

theorem IsHom.inv {L : RelativeGroupLaw K f} (hc : L.IsCommutative) {β : SchemeHomOver f f}
    (hβ : IsHom L β) : IsHom L (L.inv f β) := by
  intro T t x y
  letI := L.pointCommGroup hc t
  rw [comp_inv, comp_inv, comp_inv, hβ]
  exact mul_inv (x ⊚ β) (y ⊚ β)

def homSubgroup (L : RelativeGroupLaw K f) (hc : L.IsCommutative) :
    letI := L.pointCommGroup hc f; Subgroup (SchemeHomOver f f) :=
  letI := L.pointCommGroup hc f
  { carrier := {β | IsHom L β}
    mul_mem' := fun {_ _} hβ hγ => IsHom.mul hc hβ hγ
    one_mem' := isHom_one L
    inv_mem' := fun {_} hβ => IsHom.inv hc hβ }

theorem IsHom.endAeval {L : RelativeGroupLaw K f} (hc : L.IsCommutative) {N : SchemeHomOver f f}
    (hN : IsHom L N) (G : Polynomial ℤ) : IsHom L (L.endAeval hc N G) := by
  letI := L.pointCommGroup hc f
  change L.endAeval hc N G ∈ homSubgroup L hc
  unfold RelativeGroupLaw.endAeval
  exact Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ (hN.npow i) _

abbrev KerPts (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Type u :=
  {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f // x ⊚ β = L.one (𝟙 (Spec (CommRingCat.of K)))}

end EndCalculus

section Induces

variable {K : Type u} [Field K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

variable (L : RelativeGroupLaw K f)
variable {A : Type v} [AddCommGroup A] (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)

def Induces (β : SchemeHomOver f f) (U : A → A) : Prop := ∀ x : A, pts (U x) = (pts x) ⊚ β

omit L [AddCommGroup A] in
theorem Induces.iterate {π : SchemeHomOver f f} {U : A → A} (hπ : Induces pts π U) (i : ℕ) :
    Induces pts (schemeHomOverNpow π i) (U^[i]) := by
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    rw [Function.iterate_succ_apply', hπ, ih, schemeHomOverNpow_succ, schemeHomOverComp_assoc]

variable (hadd : ∀ x y : A, pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of K))) (pts x) (pts y))
include hadd

theorem pts_zero : pts 0 = L.one _ := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of K)))
  have h : pts 0 * pts 0 = pts 0 := by
    change L.mul _ (pts 0) (pts 0) = pts 0
    rw [← hadd, add_zero]
  exact mul_eq_left.mp h

theorem pts_neg (x : A) : pts (-x) = L.inv _ (pts x) := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of K)))
  have h : pts (-x) * pts x = 1 := by
    change L.mul _ (pts (-x)) (pts x) = L.one _
    rw [← hadd, neg_add_cancel, pts_zero L pts hadd]
  exact eq_inv_of_mul_eq_one_left h

theorem Induces.mul {β γ : SchemeHomOver f f} {U V : A → A} (hβ : Induces pts β U)
    (hγ : Induces pts γ V) : Induces pts (L.mul f β γ) (fun x => U x + V x) := by
  intro x
  rw [hadd, hβ, hγ, comp_mul]

theorem induces_one : Induces pts (L.one f) (fun _ => 0) := by
  intro x
  rw [pts_zero L pts hadd, comp_one]

theorem Induces.inv {β : SchemeHomOver f f} {U : A → A} (hβ : Induces pts β U) :
    Induces pts (L.inv f β) (fun x => -U x) := by
  intro x
  rw [pts_neg L pts hadd, hβ, comp_inv]

theorem Induces.zpow (hc : L.IsCommutative) {β : SchemeHomOver f f} {U : A → A}
    (hβ : Induces pts β U) (n : ℤ) :
    Induces pts (letI := L.pointCommGroup hc f; β ^ n) (fun x => n • U x) := by
  letI := L.pointCommGroup hc f
  induction n with
  | zero =>
    have h := induces_one L pts hadd
    simp only [zpow_zero, zero_smul]
    exact h
  | succ n ih =>
    have h := Induces.mul L pts hadd ih hβ
    simp only [add_smul, one_smul]
    rw [zpow_add, zpow_one]
    exact h
  | pred n ih =>
    have h := Induces.mul L pts hadd ih (Induces.inv L pts hadd hβ)
    have e1 : (β ^ (-(n : ℤ) - 1)) = L.mul f (β ^ (-(n : ℤ))) (L.inv f β) := by
      rw [zpow_sub_one]; rfl
    have e2 : (fun x => (-(n : ℤ) - 1) • U x) = fun x => -(n : ℤ) • U x + -U x := by
      funext x; rw [sub_smul, one_smul, sub_eq_add_neg]
    rw [e1, e2]
    exact h

theorem Induces.prod (hc : L.IsCommutative) {ι : Type*} (s : Finset ι) {β : ι → SchemeHomOver f f}
    {U : ι → A → A} (h : ∀ i ∈ s, Induces pts (β i) (U i)) :
    Induces pts (letI := L.pointCommGroup hc f; ∏ i ∈ s, β i) (fun x => ∑ i ∈ s, U i x) := by
  letI := L.pointCommGroup hc f
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 := induces_one L pts hadd
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact h1
  | insert a s ha ih =>
    have h' := Induces.mul L pts hadd (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact h'

def kerEquiv {β : SchemeHomOver f f} (U : A →+ A) (hβ : Induces pts β U) : U.ker ≃ KerPts L β where
  toFun x := ⟨pts x.1, by
    have hx : U x.1 = 0 := x.2
    rw [← hβ, hx, pts_zero L pts hadd]⟩
  invFun y := ⟨pts.symm y.1, by
    show U (pts.symm y.1) = 0
    apply pts.injective
    rw [hβ, Equiv.apply_symm_apply, pts_zero L pts hadd]
    exact y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem induces_endAeval (hc : L.IsCommutative) {N : SchemeHomOver f f} (T : A →+ A)
    (hN : Induces pts N T) (G : Polynomial ℤ) :
    Induces pts (L.endAeval hc N G) (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom := by
  have h := Induces.prod L pts hadd hc (Finset.range (G.natDegree + 1))
    (β := fun i => letI := L.pointCommGroup hc f; schemeHomOverNpow N i ^ G.coeff i)
    (U := fun i x => G.coeff i • (T^[i] x))
    (fun i _ => Induces.zpow L pts hadd hc (Induces.iterate pts hN i) (G.coeff i))
  intro x
  have hx : (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom x =
      ∑ i ∈ Finset.range (G.natDegree + 1), G.coeff i • (T^[i] x) := by
    rw [LinearMap.toAddMonoidHom_coe, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Module.End.pow_apply, AddMonoidHom.coe_toIntLinearMap]
  rw [hx]
  exact h x

end Induces

section Kernel

variable {K : Type u} [Field K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

def kerPtsEquiv (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (L.endKerStr β) ≃ KerPts L β where
  toFun z := ⟨⟨z.1 ≫ L.endKerι β, by
      rw [Category.assoc, RelativeGroupLaw.endKerι_comp_base]; exact z.2⟩, by
      apply Subtype.ext
      change (z.1 ≫ L.endKerι β) ≫ β.1 = (L.one _).1
      rw [Category.assoc, RelativeGroupLaw.endKerι_comp, ← Category.assoc, z.2, Category.id_comp]⟩
  invFun x := ⟨pullback.lift x.1.1 (𝟙 _) (by
      have h := congrArg Subtype.val x.2
      change x.1.1 ≫ β.1 = (L.one _).1 at h
      rw [h, Category.id_comp]), by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
      rw [pullback.lift_snd]⟩
  left_inv z := by
    apply Subtype.ext
    change pullback.lift (z.1 ≫ L.endKerι β) (𝟙 _) _ = z.1
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]; exact z.2.symm
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    change pullback.lift x.1.1 (𝟙 _) _ ≫ pullback.fst _ _ = x.1.1
    rw [pullback.lift_fst]

theorem isFinite_of_finite_points [IsAlgClosed K] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K))
    [IsProper g] (hfin : Finite {p : Spec (CommRingCat.of K) ⟶ Z // p ≫ g = 𝟙 _}) : IsFinite g := by
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace g
  have hcl : (closedPoints (Z : Type u)).Finite := by
    haveI : Finite (closedPoints (Z : Type u)) := Finite.of_equiv _ (pointEquivClosedPoint g)
    exact Set.toFinite _
  have huniv : closedPoints (Z : Type u) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints, closure_subset_iff_isClosed,
      ← (closedPoints (Z : Type u)).biUnion_of_singleton]
    exact hcl.isClosed_biUnion fun _ => id
  haveI : Finite Z := Set.finite_univ_iff.mp (huniv ▸ hcl)
  haveI : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun _ => Set.toFinite _
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

theorem isFinite_endKerStr_of_finite_kerPts [IsAlgClosed K] [IsProper f] (L : RelativeGroupLaw K f)
    (β : SchemeHomOver f f) (hfin : Finite (KerPts L β)) : IsFinite (L.endKerStr β) := by
  haveI : IsProper β.1 := by
    have : IsProper (β.1 ≫ f) := by rw [β.2]; infer_instance
    exact IsProper.of_comp β.1 f
  haveI : IsProper (L.endKerStr β) := inferInstance
  exact isFinite_of_finite_points (L.endKerStr β) (Finite.of_equiv _ (kerPtsEquiv L β).symm)

end Kernel

section Points

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem exists_point_comp_eq [IsAlgClosed K] (β : A ⟶ A) (hβ : β ≫ f = f) [LocallyOfFiniteType β]
    (hsurj : Function.Surjective β)
    (q : Spec (CommRingCat.of K) ⟶ A) (hq : q ≫ f = 𝟙 _) :
    ∃ w : Spec (CommRingCat.of K) ⟶ A, w ≫ f = 𝟙 _ ∧ w ≫ β = q := by
  obtain ⟨a, ha⟩ := hsurj (q (IsLocalRing.closedPoint K))
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := β) (g := q) a
    (IsLocalRing.closedPoint K) ha
  let g : pullback β q ⟶ Spec (CommRingCat.of K) := pullback.snd β q
  haveI : LocallyOfFiniteType g := inferInstance
  haveI := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set ↥(pullback β q))) ⟨z, trivial⟩ isClosed_univ.isLocallyClosed
  let w := (pointEquivClosedPoint g).symm ⟨c, hc⟩
  refine ⟨w.1 ≫ pullback.fst β q, ?_, ?_⟩
  · rw [Category.assoc, ← hβ, ← Category.assoc (pullback.fst β q), pullback.condition,
      Category.assoc, ← Category.assoc, w.2, Category.id_comp, hq]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, w.2, Category.id_comp]

variable {f} in

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

end Points

section Main

open IntermediateField

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

theorem main (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional K⟮x⟯ F)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (T : Pic0 K F →+ Pic0 K F)
    (hT : ∀ D : Divisor.degZero (K := K) (F := F),
      T (Pic0.mk D) = Pic0.mk ⟨Divisor.pushforwardAlong φ hφi D,
        Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (G : Polynomial ℤ)
    (hfin : Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker) :
    Function.Surjective (Polynomial.aeval (R := ℤ) T.toIntLinearMap G) := by

  haveI : PerfectField K := inferInstance
  haveI : Infinite K := inferInstance
  obtain ⟨M⟩ := AlgebraicCurve.CurveModel.nonempty_of_perfectField K F hfg

  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x₀, -, hx₀⟩ :=
    nonempty_inter_closedPoints (X := M.C) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    (pointEquivClosedPoint M.toBase).symm ⟨x₀, hx₀⟩

  obtain ⟨D, h, aj, hsm, hpr, hgc, hajs, haj, pts, hadd, hnorm⟩ :=
    AlgebraicCurve.CurveModel.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F M s
  set L : RelativeGroupLaw K D.toBase :=
    RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h with hL
  have hc : L.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative _
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    ⟨hsm, hpr, fun x => Scheme.Hom.isConnected_preimage_singleton D.toBase x, ⟨L⟩⟩

  obtain ⟨N, hNhom, hNpts⟩ :=
    AlgebraicCurve.Pic0.exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic K F M s D h aj hajs
      haj F M s D h aj hajs haj φ hφi
  have hN := hNpts pts pts hadd hnorm hadd hnorm
  have hNhom' : IsHom L N := by intro T t x y; exact hNhom t x y

  have hind : Induces pts N T := by
    intro x
    obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective x
    apply Subtype.ext
    rw [hT]
    exact hN Dv

  set β : SchemeHomOver D.toBase D.toBase := L.endAeval hc N G with hβ
  have hβhom : IsHom L β := IsHom.endAeval hc hNhom' G
  have hβind : Induces pts β (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom :=
    induces_endAeval L pts hadd hc T hind G

  have hker : Finite (KerPts L β) := Finite.of_equiv _ (kerEquiv L pts hadd _ hβind)
  haveI : IsProper D.toBase := hpr
  haveI : IsFinite (L.endKerStr β) := isFinite_endKerStr_of_finite_kerPts L β hker

  haveI : IsFinite β.1 :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_of_isFinite_endKerStr K D.toBase L β
      (fun t x y => hβhom t x y)
  haveI : Flat β.1 := GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite K hA β
  haveI := connectedSpace hA
  obtain ⟨hsurj, -, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat K
      D.toBase L β

  intro y
  obtain ⟨w, hw, hwβ⟩ := exists_point_comp_eq D.toBase β.1 β.2 hsurj (pts y).1 (pts y).2
  refine ⟨pts.symm ⟨w, hw⟩, ?_⟩
  apply pts.injective
  have e := hβind (pts.symm ⟨w, hw⟩)
  rw [LinearMap.toAddMonoidHom_coe, Equiv.apply_symm_apply] at e
  rw [e]
  exact Subtype.ext hwβ

end Main

section Glue

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem essFiniteType {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀]
    [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.EssFiniteType K F := by
  classical
  obtain ⟨s, hs⟩ := hfg
  rw [← IntermediateField.fg_top_iff]
  refine ⟨s.image (algebraMap F₀ F), ?_⟩
  rw [Finset.coe_image]
  apply top_le_iff.mp
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ IntermediateField.adjoin k (s : Set F₀) := by rw [hs]; exact IntermediateField.mem_top
  refine IntermediateField.adjoin_induction (F := k)
    (p := fun x _ => algebraMap F₀ F x ∈ IntermediateField.adjoin K (algebraMap F₀ F '' (s : Set F₀)))
    ?_ ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  · intro c
    letI := Fintype.ofFinite k
    set y := algebraMap F₀ F (algebraMap k F₀ c)
    have hy : y ^ Nat.card k = y := by
      simp only [y, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hq1 : 1 < Nat.card k := Finite.one_lt_card
    have hint : IsIntegral K y := by
      refine ⟨X ^ Nat.card k - X, (Polynomial.monic_X_pow _).sub_of_left (by
        rw [degree_X_pow, degree_X]; exact_mod_cast hq1), ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_X, hy, sub_self]
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨c', hc'⟩ := minpoly.mem_range_of_degree_eq_one K y hdeg
    rw [← hc']
    exact IntermediateField.algebraMap_mem _ c'
  · intro x y _ _ hx hy
    rw [map_add]; exact add_mem hx hy
  · intro x _ hx
    rw [map_inv₀]; exact inv_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]; exact mul_mem hx hy

end Glue

end P2mSurjLang

end

open AlgebraicCurve in

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (G : Polynomial ℤ) (hG0 : ((G.coeff 0 : ℤ) : K) ≠ 0)
    (hfin : Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker) :
    Function.Surjective (Polynomial.aeval (R := ℤ) T.toIntLinearMap G) := by
  haveI : Algebra.EssFiniteType K F := P2mSurjLang.essFiniteType hfg hgen
  haveI : PerfectField K := inferInstance
  obtain ⟨t, ht, htfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  exact P2mSurjLang.main K F ⟨t, ht, htfin⟩ φ hφi T hT G hfin

end S_AlgebraicCurve_Pic0_surjective_aeval_of_finite_ker_of_pushforwardAlong_frobenius
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_surjective_aeval_of_finite_ker_of_pushforwardAlong_frobenius (solution)
