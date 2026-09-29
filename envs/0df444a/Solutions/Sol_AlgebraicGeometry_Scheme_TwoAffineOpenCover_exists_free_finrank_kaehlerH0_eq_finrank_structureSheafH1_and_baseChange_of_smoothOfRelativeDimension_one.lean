-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6bc2e881-2d1a-53cd-9948-469c38b86868

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_structureSheaf
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_kaehlerSections
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_sub_finrank_coker_baseChange_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_isProper_of_geometricallyReduced_of_connected
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~genus~cechDiff"

theorem fibreRank_H1_eq
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (𝒱 : X.TwoAffineOpenCover)
    (g : ℕ)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (L : Type) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (𝔭 : PrimeSpectrum ↥(GaloisRep.ratLocalizedAt p)) :
    Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = g := by
  classical

  haveI hloc : IsLocalization.AtPrime ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) := IsLocalization.AtPrime.isLocalRing ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)})
  haveI : IsNoetherianRing ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalization.isNoetherianRing (Ideal.span {(p : ℤ)}).primeCompl ↥(GaloisRep.ratLocalizedAt p) inferInstance
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  obtain ⟨hfin0, hfin1⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_structureSheaf 𝒱 c
  haveI := hfin0; haveI := hfin1

  have h0 : ∀ (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F],
      Module.finrank F (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange F)) = 1 :=
    fun F _ _ =>
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_cechDiff_baseChange_eq_one_of_isProper_of_geometricallyReduced_of_connected
        𝒱 c (fun L _ _ _ => inferInstance) (fun L _ _ _ => inferInstance) F

  let κ : Type := 𝔭.asIdeal.ResidueField
  let K : Type := AlgebraicClosure κ
  have hchi := AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_sub_finrank_coker_baseChange_eq ↥(GaloisRep.ratLocalizedAt p) 𝒱 c κ K

  obtain ⟨-, -, hK1⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 c K

  obtain ⟨L, _, _, M, e, he, Kc, g', hRR⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed ↥(GaloisRep.ratLocalizedAt p) c K
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) K)
  have hg' : g' = g := hg K (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) K) L M e he Kc g' hRR
  have h1 : g' = genusFF K L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
  have h2 : genusFF K L = (by
      letI := (baseToFunctionField
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) K))).toAlgebra
      exact genusFF K (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) K)).functionField) := by
    letI := M.functionFieldAlgebra
    letI := (baseToFunctionField
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) K))).toAlgebra
    obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) K)) e he
    exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)

  rw [h0 κ, h0 K] at hchi
  have hbc : Module.finrank κ ((κ ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange κ)) =
      Module.finrank K ((K ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange K)) := by
    omega
  rw [hbc, hK1, ← hg', h1]
  exact h2.symm

theorem fibreRank_H0_kaehler_eq
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (𝒱 : X.TwoAffineOpenCover)
    (g : ℕ)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (L : Type) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (𝔭 : PrimeSpectrum ↥(GaloisRep.ratLocalizedAt p)) :
    Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = g := by
  classical

  obtain ⟨e0, e1, e01, eH0', eH1', -, -, -, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections 𝒱 c 𝔭.asIdeal.ResidueField
  obtain ⟨f0, f1, f01, fH0', fH1', -, -, -, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c 𝔭.asIdeal.ResidueField
  haveI : IsProper (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) 𝔭.asIdeal.ResidueField)) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) 𝔭.asIdeal.ResidueField)) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c _ inferInstance
  have hL3 := AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
    (𝒱.pullback c 𝔭.asIdeal.ResidueField) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) 𝔭.asIdeal.ResidueField))
  rw [LinearEquiv.finrank_eq eH0', hL3, ← LinearEquiv.finrank_eq fH1']
  exact fibreRank_H1_eq p c 𝒱 g hg 𝔭

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (𝒱 : X.TwoAffineOpenCover) :
    ∃ g : ℕ,
      Module.Free ↥(GaloisRep.ratLocalizedAt p) (𝒱.kaehlerSections c).H0 ∧ Module.Finite ↥(GaloisRep.ratLocalizedAt p) (𝒱.kaehlerSections c).H0 ∧
      Module.finrank ↥(GaloisRep.ratLocalizedAt p) (𝒱.kaehlerSections c).H0 = g ∧
      Module.Free ↥(GaloisRep.ratLocalizedAt p) (𝒱.structureSheafSections c).H1 ∧ Module.Finite ↥(GaloisRep.ratLocalizedAt p) (𝒱.structureSheafSections c).H1 ∧
      Module.finrank ↥(GaloisRep.ratLocalizedAt p) (𝒱.structureSheafSections c).H1 = g ∧
      ∀ (A : Type) [CommRing A] [Algebra ↥(GaloisRep.ratLocalizedAt p) A],
        (∃ eH0 : A ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.kaehlerSections c).H0 ≃ₗ[A]
            ((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) A))).H0,
          ∀ ω, eH0 (1 ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] ω) = Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c A ω) ∧
        (∃ eH1 : A ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.structureSheafSections c).H1 ≃ₗ[A]
            ((𝒱.pullback c A).structureSheafSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) A))).H1,
          ∀ x, eH1 (1 ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] x) = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c A x) := by
  classical

  haveI hloc : IsLocalization.AtPrime ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) := IsLocalization.AtPrime.isLocalRing ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)})
  haveI : IsNoetherianRing ↥(GaloisRep.ratLocalizedAt p) := IsLocalization.isNoetherianRing (Ideal.span {(p : ℤ)}).primeCompl ↥(GaloisRep.ratLocalizedAt p) inferInstance
  haveI : _root_.IsReduced ↥(GaloisRep.ratLocalizedAt p) := inferInstance
  haveI : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)

  obtain ⟨hfl0, hfl1, hfl01⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_kaehlerDifferential_cover_of_smooth 𝒱 c
  haveI := hfl0; haveI := hfl1; haveI := hfl01

  have hfinO := AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_structureSheaf 𝒱 c
  have hfinΩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_kaehlerSections 𝒱 c

  obtain ⟨g, hg⟩ := AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
    ↥(GaloisRep.ratLocalizedAt p) c 𝒱
  have hH1 : ∀ 𝔭 : PrimeSpectrum ↥(GaloisRep.ratLocalizedAt p), Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = g :=
    fun 𝔭 => fibreRank_H1_eq p c 𝒱 g hg 𝔭
  have hH0 : ∀ 𝔭 : PrimeSpectrum ↥(GaloisRep.ratLocalizedAt p), Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = g :=
    fun 𝔭 => fibreRank_H0_kaehler_eq p c 𝒱 g hg 𝔭

  obtain ⟨hfree1, hrank1, hbc1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const 𝒱 c hfinO.2 hH1
  obtain ⟨hfree0, hrank0, hbc0⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const 𝒱 c hfinΩ hH0
  refine ⟨g, hfree0, hfinΩ.1, hrank0, hfree1, hfinO.2, hrank1, ?_⟩
  intro A _ _
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨e0, e1, e01, eH0', eH1', he0, he1, he01, heH0', heH1'⟩ :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections 𝒱 c A
    refine ⟨(LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (𝒱.kaehlerSections c).cechDiff A) (hbc0 A)).trans eH0', ?_⟩
    intro ω

    apply Subtype.ext
    rw [LinearEquiv.trans_apply, heH0']
    have hk : ((LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (𝒱.kaehlerSections c).cechDiff A) (hbc0 A))
        ((1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] ω)).1 = (1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] ω.1 := by
      rw [LinearEquiv.ofBijective_apply, TwoChartCech.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul]
      rfl
    rw [hk, TensorProduct.prodRight_tmul, he0, he1, one_smul, one_smul]
    exact (Scheme.TwoAffineOpenCover.HomOver.kaehlerH0map_apply_coe _ ω).symm
  ·
    obtain ⟨e01, e, he01, he⟩ := hbc1 A
    refine ⟨e, ?_⟩
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [he 1 y, he01 y, Scheme.TwoAffineOpenCover.H1baseChangeMap_mk, Scheme.TwoAffineOpenCover.baseChange_map01_apply]

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one (solution)
