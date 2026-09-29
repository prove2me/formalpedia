-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9401aa9b-b70b-5ce7-b621-5f6e0b616418

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Pic0_exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic
import Theorems.Thm_AlgebraicCurve_CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic
import Theorems.Thm_AlgebraicCurve_Pic0_map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
import Theorems.Thm_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base AlgebraicCurve.Divisor.congr_single"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve

universe u v

namespace P2mDfrsepQ

section EndCalculus

variable {K : Type u} [Field K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

def IsHom (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    (L.mul t x y) ⊚ β = L.mul t (x ⊚ β) (y ⊚ β)

theorem isHom_id (L : RelativeGroupLaw K f) : IsHom L (schemeHomOverId f) := by
  intro T t x y
  simp

theorem IsHom.comp {L : RelativeGroupLaw K f} {β γ : SchemeHomOver f f} (hβ : IsHom L β) (hγ : IsHom L γ) :
    IsHom L (β ⊚ γ) := by
  intro T t x y
  rw [← schemeHomOverComp_assoc, hβ, hγ, schemeHomOverComp_assoc, schemeHomOverComp_assoc]

theorem compT_mul (L : RelativeGroupLaw K f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t f) (β γ : SchemeHomOver f f) :
    z ⊚ (L.mul f β γ) = L.mul t (z ⊚ β) (z ⊚ γ) := by
  have h := L.mul_natural f t z.1 z.2 β γ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = z ⊚ δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

theorem compT_one (L : RelativeGroupLaw K f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t f) : z ⊚ (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) = z ⊚ (L.one f) := Subtype.ext rfl
  rw [e] at h
  exact h

theorem compT_inv (L : RelativeGroupLaw K f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t f) (β : SchemeHomOver f f) : z ⊚ (L.inv f β) = L.inv t (z ⊚ β) := by
  letI := L.pointGroup t
  have h1 : (z ⊚ (L.inv f β)) * (z ⊚ β) = 1 := by
    change L.mul t (z ⊚ (L.inv f β)) (z ⊚ β) = L.one t
    rw [← compT_mul, L.inv_mul_cancel, compT_one]
  exact eq_inv_of_mul_eq_one_left h1

theorem IsHom.one {L : RelativeGroupLaw K f} {β : SchemeHomOver f f} (hβ : IsHom L β)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) : (L.one t) ⊚ β = L.one t := by
  letI := L.pointGroup t
  have h : (L.one t ⊚ β) * (L.one t ⊚ β) = L.one t ⊚ β := by
    change L.mul t (L.one t ⊚ β) (L.one t ⊚ β) = L.one t ⊚ β
    rw [← hβ, L.one_mul]
  exact mul_eq_left.mp h

variable (L : RelativeGroupLaw K f) (hc : L.IsCommutative)

def homSubgroup : letI := L.pointCommGroup hc f; Subgroup (SchemeHomOver f f) :=
  letI := L.pointCommGroup hc f
  { carrier := {β | IsHom L β}
    mul_mem' := by
      intro β γ hβ hγ T t x y
      change (L.mul t x y) ⊚ (L.mul f β γ) = L.mul t (x ⊚ L.mul f β γ) (y ⊚ L.mul f β γ)
      rw [compT_mul, compT_mul, compT_mul, hβ, hγ]
      letI := L.pointCommGroup hc t
      change (x ⊚ β * (y ⊚ β)) * (x ⊚ γ * (y ⊚ γ)) = (x ⊚ β * (x ⊚ γ)) * (y ⊚ β * (y ⊚ γ))
      exact mul_mul_mul_comm _ _ _ _
    one_mem' := by
      intro T t x y
      change (L.mul t x y) ⊚ (L.one f) = L.mul t (x ⊚ L.one f) (y ⊚ L.one f)
      rw [compT_one, compT_one, compT_one, L.one_mul]
    inv_mem' := by
      intro β hβ T t x y
      change (L.mul t x y) ⊚ (L.inv f β) = L.mul t (x ⊚ L.inv f β) (y ⊚ L.inv f β)
      letI := L.pointCommGroup hc t
      rw [compT_inv, compT_inv, compT_inv, hβ]
      change (x ⊚ β * (y ⊚ β))⁻¹ = (x ⊚ β)⁻¹ * (y ⊚ β)⁻¹
      rw [mul_inv] }

def EndR : Type u := Additive (homSubgroup L hc)

scoped instance : AddCommGroup (EndR L hc) := inferInstanceAs (AddCommGroup (Additive (homSubgroup L hc)))

def EndR.val (x : EndR L hc) : SchemeHomOver f f := ((Additive.toMul x : homSubgroup L hc) : SchemeHomOver f f)

theorem EndR.isHom (x : EndR L hc) : IsHom L (EndR.val L hc x) := (Additive.toMul x : homSubgroup L hc).2

theorem EndR.ext {x y : EndR L hc} (h : EndR.val L hc x = EndR.val L hc y) : x = y :=
  Additive.toMul.injective (Subtype.ext h)

def EndR.mk (β : SchemeHomOver f f) (hβ : IsHom L β) : EndR L hc := Additive.ofMul ⟨β, hβ⟩

@[scoped simp] theorem EndR.val_mk (β : SchemeHomOver f f) (hβ : IsHom L β) : EndR.val L hc (EndR.mk L hc β hβ) = β := rfl

p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"
theorem EndR.val_add (x y : EndR L hc) : EndR.val L hc (x + y) = L.mul f (EndR.val L hc x) (EndR.val L hc y) := rfl

theorem EndR.val_zero : EndR.val L hc (0 : EndR L hc) = L.one f := rfl

scoped instance : Ring (EndR L hc) :=
  { (inferInstance : AddCommGroup (EndR L hc)) with
    mul := fun x y => EndR.mk L hc (EndR.val L hc x ⊚ EndR.val L hc y)
      (IsHom.comp (EndR.isHom L hc x) (EndR.isHom L hc y))
    one := EndR.mk L hc (schemeHomOverId f) (isHom_id L)
    mul_assoc := fun x y z => EndR.ext L hc (schemeHomOverComp_assoc _ _ _)
    one_mul := fun x => EndR.ext L hc (schemeHomOverComp_id_left _)
    mul_one := fun x => EndR.ext L hc (schemeHomOverComp_id_right _)
    left_distrib := fun x y z => EndR.ext L hc (by
      show EndR.val L hc x ⊚ L.mul f (EndR.val L hc y) (EndR.val L hc z) =
        L.mul f (EndR.val L hc x ⊚ EndR.val L hc y) (EndR.val L hc x ⊚ EndR.val L hc z)
      exact compT_mul L _ _ _)
    right_distrib := fun x y z => EndR.ext L hc (by
      show L.mul f (EndR.val L hc x) (EndR.val L hc y) ⊚ EndR.val L hc z =
        L.mul f (EndR.val L hc x ⊚ EndR.val L hc z) (EndR.val L hc y ⊚ EndR.val L hc z)
      exact EndR.isHom L hc z f _ _)
    zero_mul := fun x => EndR.ext L hc (by
      show L.one f ⊚ EndR.val L hc x = L.one f
      exact IsHom.one (EndR.isHom L hc x) f)
    mul_zero := fun x => EndR.ext L hc (by
      show EndR.val L hc x ⊚ L.one f = L.one f
      exact compT_one L _) }

theorem EndR.val_mul (x y : EndR L hc) : EndR.val L hc (x * y) = EndR.val L hc x ⊚ EndR.val L hc y := rfl

theorem EndR.val_one : EndR.val L hc (1 : EndR L hc) = schemeHomOverId f := rfl

theorem EndR.val_pow (x : EndR L hc) (i : ℕ) : EndR.val L hc (x ^ i) = schemeHomOverNpow (EndR.val L hc x) i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ, EndR.val_mul, ih, schemeHomOverNpow_succ]

theorem EndR.val_neg (x : EndR L hc) : EndR.val L hc (-x) = L.inv f (EndR.val L hc x) := rfl

theorem EndR.val_nsmul (k : ℕ) (x : EndR L hc) :
    EndR.val L hc (k • x) = (letI := L.pointCommGroup hc f; EndR.val L hc x ^ k) := by
  letI := L.pointCommGroup hc f
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ k ih => rw [succ_nsmul, EndR.val_add, ih, pow_succ]; rfl

theorem EndR.val_zsmul (n : ℤ) (x : EndR L hc) :
    EndR.val L hc (n • x) = (letI := L.pointCommGroup hc f; EndR.val L hc x ^ n) := by
  letI := L.pointCommGroup hc f
  cases n with
  | ofNat k => rw [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast, EndR.val_nsmul]
  | negSucc k => rw [negSucc_zsmul, zpow_negSucc, EndR.val_neg, EndR.val_nsmul]; rfl

theorem EndR.val_sum {ι : Type*} (s : Finset ι) (x : ι → EndR L hc) :
    EndR.val L hc (∑ i ∈ s, x i) = (letI := L.pointCommGroup hc f; ∏ i ∈ s, EndR.val L hc (x i)) := by
  letI := L.pointCommGroup hc f
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, EndR.val_add, ih]; rfl

theorem EndR.val_aeval (π : SchemeHomOver f f) (hπ : IsHom L π) (G : Polynomial ℤ) :
    EndR.val L hc (Polynomial.aeval (EndR.mk L hc π hπ) G) = L.endAeval hc π G := by
  letI := L.pointCommGroup hc f
  rw [Polynomial.aeval_eq_sum_range, EndR.val_sum, RelativeGroupLaw.endAeval]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [EndR.val_zsmul, EndR.val_pow, EndR.val_mk]

theorem isHom_endAeval (π : SchemeHomOver f f) (hπ : IsHom L π) (G : Polynomial ℤ) : IsHom L (L.endAeval hc π G) := by
  rw [← EndR.val_aeval L hc π hπ G]
  exact EndR.isHom L hc _

theorem endAeval_mul (π : SchemeHomOver f f) (hπ : IsHom L π) (G H : Polynomial ℤ) :
    L.endAeval hc π (G * H) = L.endAeval hc π G ⊚ L.endAeval hc π H := by
  rw [← EndR.val_aeval L hc π hπ, ← EndR.val_aeval L hc π hπ, ← EndR.val_aeval L hc π hπ, map_mul, EndR.val_mul]

theorem endAeval_one (π : SchemeHomOver f f) (hπ : IsHom L π) : L.endAeval hc π 1 = schemeHomOverId f := by
  rw [← EndR.val_aeval L hc π hπ, map_one, EndR.val_one]

end EndCalculus
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"

section Induces

variable {K : Type u} [Field K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

variable (L : RelativeGroupLaw K f)
variable {A : Type v} [AddCommGroup A] (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)

def Induces (β : SchemeHomOver f f) (U : A → A) : Prop := ∀ x : A, pts (U x) = (pts x) ⊚ β

def kerPts (β : SchemeHomOver f f) : Type u :=
  {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f // x ⊚ β = L.one _}

omit L in
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

theorem Induces.mul {β γ : SchemeHomOver f f} {U V : A → A} (hβ : Induces pts β U) (hγ : Induces pts γ V) :
    Induces pts (L.mul f β γ) (fun x => U x + V x) := by
  intro x
  rw [hadd, hβ, hγ, compT_mul]

theorem induces_one : Induces pts (L.one f) (fun _ => 0) := by
  intro x
  rw [pts_zero L pts hadd, compT_one]

theorem Induces.inv {β : SchemeHomOver f f} {U : A → A} (hβ : Induces pts β U) :
    Induces pts (L.inv f β) (fun x => -U x) := by
  intro x
  rw [pts_neg L pts hadd, hβ, compT_inv]

theorem Induces.zpow (hc : L.IsCommutative) {β : SchemeHomOver f f} {U : A → A} (hβ : Induces pts β U)
    (n : ℤ) : Induces pts (letI := L.pointCommGroup hc f; β ^ n) (fun x => n • U x) := by
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

def kerEquiv {β : SchemeHomOver f f} (U : A →+ A) (hβ : Induces pts β U) : U.ker ≃ kerPts L β where
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

theorem induces_endAeval (hc : L.IsCommutative) {π : SchemeHomOver f f} (T : A →+ A) (hπ : Induces pts π T)
    (G : Polynomial ℤ) :
    Induces pts (L.endAeval hc π G) (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom := by
  have h := Induces.prod L pts hadd hc (Finset.range (G.natDegree + 1))
    (β := fun i => letI := L.pointCommGroup hc f; schemeHomOverNpow π i ^ G.coeff i)
    (U := fun i x => G.coeff i • (T^[i] x))
    (fun i _ => Induces.zpow L pts hadd hc (Induces.iterate pts hπ i) (G.coeff i))
  intro x
  have hx : (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom x =
      ∑ i ∈ Finset.range (G.natDegree + 1), G.coeff i • (T^[i] x) := by
    rw [LinearMap.toAddMonoidHom_coe, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Module.End.pow_apply, AddMonoidHom.coe_toIntLinearMap]
  rw [hx]
  exact h x

end Induces
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"

section Algebra

open MvPolynomial

variable {R : Type*} [CommRing R]

theorem eval_pi_single_of_isHomogeneous {σ : Type*} [Fintype σ] [DecidableEq σ] {P : MvPolynomial σ R}
    {n : ℕ} (hP : P.IsHomogeneous n) (j : σ) :
    MvPolynomial.eval (Pi.single j 1 : σ → R) P = P.coeff (Finsupp.single j n) := by
  rw [MvPolynomial.eval_eq']
  have key : ∀ d ∈ P.support, P.coeff d * ∏ i, (Pi.single j (1 : R) : σ → R) i ^ d i =
      if d = Finsupp.single j n then P.coeff d else 0 := by
    intro d hd
    by_cases hdj : ∀ i, i ≠ j → d i = 0
    · have hd' : d = Finsupp.single j (d j) := by
        ext i
        rw [Finsupp.single_apply]
        split_ifs with hji
        · rw [hji]
        · exact hdj i (Ne.symm hji)
      have hdeg : d.degree = n := by
        rw [Finsupp.degree_eq_weight_one]; exact hP (mem_support_iff.mp hd)
      have hdjn : d j = n := by
        rw [hd', Finsupp.degree_single] at hdeg
        rw [hd', Finsupp.single_eq_same]
        exact hdeg
      have hprod : ∏ i, (Pi.single j (1 : R) : σ → R) i ^ d i = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        by_cases hij : i = j
        · rw [hij, Pi.single_eq_same, one_pow]
        · rw [hdj i hij, pow_zero]
      have hdsingle : d = Finsupp.single j n := by rw [← hdjn]; exact hd'
      rw [hprod, mul_one, if_pos hdsingle]
    · push Not at hdj
      obtain ⟨i, hij, hi⟩ := hdj
      have hprod : ∏ i, (Pi.single j (1 : R) : σ → R) i ^ d i = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [Pi.single_eq_of_ne hij, zero_pow hi]
      have hne : d ≠ Finsupp.single j n := by
        intro h
        apply hi
        rw [h, Finsupp.single_apply, if_neg (Ne.symm hij)]
      rw [hprod, mul_zero, if_neg hne]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (notMem_support_iff.mp h).symm

def dehomogenize {m : ℕ} (P : MvPolynomial (Fin (m + 2)) R) : MvPolynomial (Fin (m + 1)) R :=
  ((finSuccEquiv R (m + 1) P).sum fun _ a => a)

theorem eval_dehomogenize {m : ℕ} (P : MvPolynomial (Fin (m + 2)) R) (c : Fin (m + 1) → R) :
    MvPolynomial.eval c (dehomogenize P) = MvPolynomial.eval (Fin.cons 1 c : Fin (m + 2) → R) P := by
  rw [eval_eq_eval_mv_eval', dehomogenize, Polynomial.sum, map_sum, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem totalDegree_dehomogenize_le {m : ℕ} (P : MvPolynomial (Fin (m + 2)) R) :
    (dehomogenize P).totalDegree ≤ P.totalDegree := by
  rw [dehomogenize, Polynomial.sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
  have h := totalDegree_coeff_finSuccEquiv_add_le P i (Polynomial.mem_support_iff.mp hi)
  omega

theorem coeff_dehomogenize {m : ℕ} (P : MvPolynomial (Fin (m + 2)) R) (d : Fin (m + 1) →₀ ℕ) :
    (dehomogenize P).coeff d = ∑ i ∈ (finSuccEquiv R (m + 1) P).support, P.coeff (d.cons i) := by
  rw [dehomogenize, Polynomial.sum, coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact finSuccEquiv_coeff_coeff d P i

theorem coeff_dehomogenize_single_zero {m : ℕ} {P : MvPolynomial (Fin (m + 2)) R} {n : ℕ}
    (hP : P.IsHomogeneous n) :
    (dehomogenize P).coeff (Finsupp.single 0 n) = P.coeff (Finsupp.single 1 n) := by
  rw [coeff_dehomogenize]
  have hcons0 : (Finsupp.single (0 : Fin (m + 1)) n).cons 0 = Finsupp.single (1 : Fin (m + 2)) n := by
    rw [Finsupp.cons_zero_single_eq_single_succ, Fin.succ_zero_eq_one]
  have key : ∀ i ∈ (finSuccEquiv R (m + 1) P).support,
      P.coeff ((Finsupp.single (0 : Fin (m + 1)) n).cons i) =
        if i = 0 then P.coeff (Finsupp.single 1 n) else 0 := by
    intro i _
    split_ifs with hi
    · rw [hi, hcons0]
    · apply hP.coeff_eq_zero
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
      simp only [Finsupp.cons_zero, Finsupp.cons_succ]
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_single]
      omega
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h0
  · rfl
  · have h' : (finSuccEquiv R (m + 1) P).coeff 0 = 0 := Polynomial.notMem_support_iff.mp h0
    have := finSuccEquiv_coeff_coeff (Finsupp.single (0 : Fin (m + 1)) n) P 0
    rw [h', coeff_zero, hcons0] at this
    exact this

end Algebra
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"

section Forms

variable {K : Type u} [Field K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

theorem forms_of_homogeneous (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (π : SchemeHomOver f f)
    (hπ : IsHom L π) (n : ℕ) (deg : SchemeHomOver f f → ℕ) (hdeg1 : deg (schemeHomOverId f) = 1)
    (hforms : ∀ (m : ℕ) (α : Fin (m + 1) → SchemeHomOver f f), (∀ i, IsHom L (α i)) →
      ∃ P : MvPolynomial (Fin (m + 1)) ℚ, P.IsHomogeneous n ∧
        ∀ c : Fin (m + 1) → ℤ,
          ((deg (letI := L.pointCommGroup hc f; ∏ i, α i ^ c i) : ℕ) : ℚ) =
            MvPolynomial.eval (fun i => (c i : ℚ)) P)
    (b : ℕ) :
    ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ n ∧ N.coeff (Finsupp.single 0 n) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 →
        MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N =
          ((deg (L.endAeval hc π G) : ℕ) : ℚ) := by
  letI := L.pointCommGroup hc f

  set α : Fin (b + 2) → SchemeHomOver f f := Fin.cons (schemeHomOverNpow π (b + 1)) fun j => schemeHomOverNpow π j
    with hαdef
  have hα0 : α 0 = schemeHomOverNpow π (b + 1) := by rw [hαdef]; rfl
  have hαs : ∀ j : Fin (b + 1), α j.succ = schemeHomOverNpow π j := fun j => by rw [hαdef]; rfl
  have hnpow : ∀ e, IsHom L (schemeHomOverNpow π e) := fun e => by
    rw [← EndR.val_mk L hc π hπ, ← EndR.val_pow]
    exact EndR.isHom L hc _
  have hαhom : ∀ i, IsHom L (α i) := by
    refine Fin.cases ?_ fun j => ?_
    · rw [hα0]; exact hnpow _
    · rw [hαs]; exact hnpow _
  obtain ⟨P, hPhom, hP⟩ := hforms (b + 1) α hαhom
  refine ⟨dehomogenize P, ?_, ?_, ?_⟩
  · exact (totalDegree_dehomogenize_le P).trans hPhom.totalDegree_le
  · classical
    have h1 := hP (Pi.single (1 : Fin (b + 2)) (1 : ℤ))
    have hcast : (fun i : Fin (b + 2) => ((Pi.single (1 : Fin (b + 2)) (1 : ℤ) : Fin (b + 2) → ℤ) i : ℚ)) =
        (Pi.single (1 : Fin (b + 2)) (1 : ℚ) : Fin (b + 2) → ℚ) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Int.cast_zero]
    rw [hcast, eval_pi_single_of_isHomogeneous hPhom 1] at h1
    have hprod : (∏ i, α i ^ (Pi.single (1 : Fin (b + 2)) (1 : ℤ) : Fin (b + 2) → ℤ) i) = α 1 := by
      rw [Finset.prod_eq_single (1 : Fin (b + 2))]
      · rw [Pi.single_eq_same, zpow_one]
      · intro c _ hc'; rw [Pi.single_eq_of_ne hc', zpow_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hα1 : α 1 = schemeHomOverId f := by
      have := hαs 0
      simpa using this
    rw [hprod, hα1, hdeg1, Nat.cast_one] at h1
    rw [coeff_dehomogenize_single_zero hPhom, ← h1]
  · intro G hGm hGdeg
    have hlead : G.coeff (b + 1) = 1 := by rw [← hGdeg]; exact hGm.coeff_natDegree
    have hL : L.endAeval hc π G =
        (∏ j : Fin (b + 1), schemeHomOverNpow π j ^ G.coeff j) * schemeHomOverNpow π (b + 1) := by
      rw [RelativeGroupLaw.endAeval, hGdeg, Finset.prod_range (fun i => schemeHomOverNpow π i ^ G.coeff i),
        Fin.prod_univ_castSucc]
      simp [hlead]
    have hR : (∏ i, α i ^ (Fin.cons 1 (fun i : Fin (b + 1) => G.coeff (i : ℕ)) : Fin (b + 2) → ℤ) i) =
        schemeHomOverNpow π (b + 1) * ∏ j : Fin (b + 1), schemeHomOverNpow π j ^ G.coeff j := by
      rw [Fin.prod_univ_succ, hα0]
      simp only [Fin.cons_zero, Fin.cons_succ, zpow_one, hαs]
    have hval := hP (Fin.cons 1 fun i : Fin (b + 1) => G.coeff (i : ℕ))
    have hcast : (fun i : Fin (b + 2) => ((Fin.cons 1 (fun i : Fin (b + 1) => G.coeff (i : ℕ)) : Fin (b + 2) → ℤ) i : ℚ)) =
        (Fin.cons 1 fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ) : Fin (b + 2) → ℚ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    rw [eval_dehomogenize, ← hcast, ← hval, hR, mul_comm, ← hL]

end Forms
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"

section Isogeny

variable {K : Type u} [Field K] [IsAlgClosed K] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace J := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set J) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

variable (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  (π : SchemeHomOver f f) (hπ : IsHom L π)
  (hdπ : ∀ x : J, (IsLocalRing.maximalIdeal (J.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
    IsLocalRing.maximalIdeal (J.presheaf.stalk x) ^ 2)

include hA hdπ in

theorem etale_ker (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) : Etale (L.endKerStr (L.endAeval hc π G)) :=
  GoodReductionJacobian.RelativeGroupLaw.etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq K f L hc hA π hdπ G hG

include hA hdπ in

theorem ker_facts (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    IsFinite (L.endKerStr (L.endAeval hc π G)) ∧ Finite (kerPts L (L.endAeval hc π G)) ∧
      Nat.card (kerPts L (L.endAeval hc π G)) = L.endDegree (L.endAeval hc π G) := by
  haveI := hA.proper
  haveI := etale_ker L hc hA π hdπ G hG
  exact GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale K f L
    (L.endAeval hc π G)

include hA hdπ hπ in

theorem isFinite_flat (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    IsFinite (L.endAeval hc π G).1 ∧ Flat (L.endAeval hc π G).1 := by
  haveI := hA.proper
  haveI := (ker_facts L hc hA π hdπ G hG).1
  haveI : IsFinite (L.endAeval hc π G).1 :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L (L.endAeval hc π G)
      (fun t x y => isHom_endAeval L hc π hπ G t x y)
  exact ⟨inferInstance, GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite K hA _⟩

include hA hdπ hπ in

theorem deg_mul (G H : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) (hH : ((H.coeff 0 : ℤ) : K) ≠ 0) :
    L.endDegree (L.endAeval hc π (G * H)) = L.endDegree (L.endAeval hc π G) * L.endDegree (L.endAeval hc π H) := by
  haveI := hA.proper
  haveI := connectedSpace hA
  obtain ⟨h1, h2⟩ := isFinite_flat L hc hA π hπ hdπ G hG
  obtain ⟨h3, h4⟩ := isFinite_flat L hc hA π hπ hdπ H hH
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  rw [endAeval_mul L hc π hπ]
  exact GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat K f L _ _

include hπ in

theorem deg_one : L.endDegree (L.endAeval hc π 1) = 1 := by
  rw [endAeval_one L hc π hπ, RelativeGroupLaw.endDegree_schemeHomOverId]

end Isogeny
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"

section FiniteGeneration

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
  (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
  (φ : F →ₐ[K] F)
  (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))

theorem exists_algebraMap_eq_of_isAlgebraic {A : Type*} [Field A] [Algebra K A] {y : A} (hy : IsAlgebraic K y) :
    ∃ a : K, algebraMap K A a = y := by
  have hint : IsIntegral K y := hy.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K y hdeg
  exact ⟨c, hc⟩

theorem exists_algebraMap_eq_const (c : k) : ∃ a : K, algebraMap K F a = algebraMap F₀ F (algebraMap k F₀ c) := by
  letI := Fintype.ofFinite k
  set y := algebraMap F₀ F (algebraMap k F₀ c) with hy
  have hyq : y ^ Nat.card k = y := by
    simp only [y, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hint : IsIntegral K y := by
    refine ⟨X ^ Nat.card k - X, (monic_X_pow _).sub_of_left (by
      rw [degree_X_pow, degree_X]; exact_mod_cast hq1), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_X, hyq, sub_self]
  exact exists_algebraMap_eq_of_isAlgebraic hint.isAlgebraic

include hfg hgen in

theorem essFiniteType : Algebra.EssFiniteType K F := by
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
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_const (K := K) (F₀ := F₀) (F := F) c
    rw [← ha]
    exact IntermediateField.algebraMap_mem _ a
  · intro x y _ _ hx hy
    rw [map_add]; exact add_mem hx hy
  · intro x _ hx
    rw [map_inv₀]; exact inv_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]; exact mul_mem hx hy

end FiniteGeneration
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR"

end P2mDfrsepQ
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ.EndR P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.P2mDfrsepQ"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve P2mDfrsepQ in

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
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * AlgebraicCurve.genusFF K F ∧
      ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ∧
        ((Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker : ℕ) : ℚ) =
          (G.map (Int.castRingHom ℚ)).resultant P := by

  haveI : Algebra.EssFiniteType K F := essFiniteType hfg hgen
  obtain ⟨x, hxt, hxfin, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hfgK : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    ⟨x, hxt, hxfin⟩

  obtain ⟨M⟩ := AlgebraicCurve.CurveModel.nonempty_of_perfectField K F hfgK
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x₀, -, hx₀⟩ :=
    nonempty_inter_closedPoints (X := M.C) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    (pointEquivClosedPoint M.toBase).symm ⟨x₀, hx₀⟩

  obtain ⟨D, h, aj, hsm, hpr, hgc, hajs, haj, pts, hadd, hnorm⟩ :=
    AlgebraicCurve.CurveModel.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F M s
  set L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h with hL
  have hc : L.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative _
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    ⟨hsm, hpr, fun y => Scheme.Hom.isConnected_preimage_singleton D.toBase y, ⟨L⟩⟩

  obtain ⟨π, hπhom, hπpts⟩ :=
    AlgebraicCurve.Pic0.exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic K F M s D h aj hajs haj
      F M s D h aj hajs haj φ hφi
  have hπ := hπpts pts pts hadd hnorm hadd hnorm
  have hπhom' : IsHom L π := fun t a b => hπhom t a b

  haveI := AlgebraicCurve.CurveModel.smoothOfRelativeDimension_genusFF_of_representsRelSubPic K F hfgK M s D h

  have hdπ := AlgebraicCurve.Pic0.map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic
    k K F₀ F hfg hgen φ hφi hφ M s D h aj hajs haj pts hadd hnorm π hπhom hπ

  have hind : Induces pts π T := by
    intro y
    obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective y
    apply Subtype.ext
    rw [hT]
    exact hπ Dv

  let Dg : Polynomial ℤ → ℚ := fun G => ((L.endDegree (L.endAeval hc π G) : ℕ) : ℚ)
  have h1 : Dg 1 = 1 := by
    show ((L.endDegree (L.endAeval hc π 1) : ℕ) : ℚ) = 1
    rw [deg_one L hc π hπhom', Nat.cast_one]
  have hmul : ∀ G H : Polynomial ℤ, G.Monic → H.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
      ((H.coeff 0 : ℤ) : K) ≠ 0 → Dg (G * H) = Dg G * Dg H := by
    intro G H _ _ hG hH
    show ((L.endDegree (L.endAeval hc π (G * H)) : ℕ) : ℚ) =
      ((L.endDegree (L.endAeval hc π G) : ℕ) : ℚ) * ((L.endDegree (L.endAeval hc π H) : ℕ) : ℚ)
    rw [deg_mul L hc hA π hπhom' hdπ G H hG hH, Nat.cast_mul]

  have hforms : ∀ (m : ℕ) (α : Fin (m + 1) → SchemeHomOver D.toBase D.toBase), (∀ i, IsHom L (α i)) →
      ∃ P : MvPolynomial (Fin (m + 1)) ℚ, P.IsHomogeneous (2 * genusFF K F) ∧
        ∀ c : Fin (m + 1) → ℤ,
          ((L.endDegree (letI := L.pointCommGroup hc D.toBase; ∏ i, α i ^ c i) : ℕ) : ℚ) =
            MvPolynomial.eval (fun i => (c i : ℚ)) P := fun m α hα =>
    GoodReductionJacobian.RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
      K D.toBase L hc hA (genusFF K F) α (fun i => hα i)
  have hpoly : ∀ b : ℕ, ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ 2 * genusFF K F ∧
      N.coeff (Finsupp.single 0 (2 * genusFF K F)) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N = Dg G := by
    intro b
    obtain ⟨N, hN1, hN2, hN3⟩ := forms_of_homogeneous L hc π hπhom' (2 * genusFF K F) L.endDegree
      L.endDegree_schemeHomOverId hforms b
    exact ⟨N, hN1, hN2, fun G hG hGdeg _ => hN3 G hG hGdeg⟩

  obtain ⟨P, hPm, hPdeg, hP⟩ :=
    Polynomial.exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial K Dg (2 * genusFF K F)
      (even_two_mul _) h1 hmul hpoly
  refine ⟨P, hPm, hPdeg, fun G hG hG0 => ?_⟩

  obtain ⟨-, hfin, hcard⟩ := ker_facts L hc hA π hdπ G hG0
  have e := kerEquiv L pts hadd (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom
    (induces_endAeval L pts hadd hc T hind G)
  haveI := hfin
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard]
  exact hP G hG hG0

end S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius (solution)
