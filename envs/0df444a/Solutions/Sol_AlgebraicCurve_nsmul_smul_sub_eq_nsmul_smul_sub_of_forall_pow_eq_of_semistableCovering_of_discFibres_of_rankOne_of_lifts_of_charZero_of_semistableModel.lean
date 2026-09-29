-- Prove2me | solution 1 for AlgebraicCurve.nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f9e7d62d-e372-5f2b-b4a5-f3912798aa71

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
import Theorems.Thm_AlgebraicCurve_smul_smul_sub_eq_smul_sub_of_isUnit_natCast_of_nsmul_eq_zero_of_genusFF_of_semistableCovering_of_charZero_of_semistableModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus"
open scoped TensorProduct

namespace KummerCongAux

open IsLocalRing

theorem pow_smul_eq_add_nsmul {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (s : G) (P : M) (h : s • (s • P - P) = s • P - P) (a : ℕ) : s ^ a • P = P + a • (s • P - P) := by
  induction a with
  | zero => simp
  | succ a ih =>
      have h2 : s • (a • (s • P - P)) = a • (s • P - P) := by
        rw [smul_comm, h]
      rw [pow_succ', mul_smul, ih, smul_add, h2, succ_nsmul]
      abel

theorem baseAut_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F) (a : ℕ) :
    SemilinearAut.baseAut (g ^ a) = SemilinearAut.baseAut g ^ a := by
  induction a with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ a ih => rw [pow_succ, pow_succ, SemilinearAut.baseAut_mul, ih]

section Law

variable {L : Type} [Field L] (A : ValuationSubring L) (π : A) {F : Type} [Field F] [Algebra L F]
  {n m : ℕ} {Fbar : Fin n → Type} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
  (C : ∀ i, ComponentChart A F (Fbar i)) (An An' : Fin m → Annulus A F)

def NineLaw (g : SemilinearAut L F) : Prop :=
  (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A) ∧ SemilinearAut.baseAut g (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut g (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut g (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, g • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, g • P ∈ (An e).dom) ∧
      (∀ e, g • (An e).param = (An e).param) ∧ (∀ e, g • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : g • f ∈ (C i).integers,
        (C i).residue ⟨g • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = (C i).placeMap P)

variable {A π C An An'}

theorem nineLaw_one : NineLaw A π C An An' 1 := by
  refine ⟨fun a => Iff.rfl, rfl, fun a h => rfl, fun i P hP => by rwa [one_smul], fun e P hP => by rwa [one_smul],
    fun e => one_smul _ _, fun e => one_smul _ _, fun i f hf => ⟨by rwa [one_smul], by simp only [one_smul]⟩,
    fun i P _ => by rw [one_smul]⟩

theorem nineLaw_mul {g h : SemilinearAut L F} (hg : NineLaw A π C An An' g) (hh : NineLaw A π C An An' h) :
    NineLaw A π C An An' (g * h) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hh
  have hb : ∀ a : L, SemilinearAut.baseAut (g * h) a = SemilinearAut.baseAut g (SemilinearAut.baseAut h a) :=
    fun a => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hb]; exact (h1 a).trans (g1 _)
  · rw [hb, h2, g2]
  · intro a ha
    have hha : SemilinearAut.baseAut h (a : L) ∈ A := (h1 a).mp a.2
    have hga : SemilinearAut.baseAut g (SemilinearAut.baseAut h (a : L)) ∈ A := by rwa [hb] at ha
    have e1 := g3 ⟨_, hha⟩ hga
    have e2 := h3 a hha
    exact (e1.trans e2 : _)
  · intro i P hP; rw [mul_smul]; exact g4 i _ (h4 i P hP)
  · intro e P hP; rw [mul_smul]; exact g5 e _ (h5 e P hP)
  · intro e; rw [mul_smul, h6, g6]
  · intro e; rw [mul_smul, h7, g7]
  · intro i f hf
    obtain ⟨hf1, e1⟩ := h8 i f hf
    obtain ⟨hf2, e2⟩ := g8 i (h • f) hf1
    refine ⟨by rw [mul_smul]; exact hf2, ?_⟩
    have : (⟨(g * h) • f, by rw [mul_smul]; exact hf2⟩ : (C i).integers) = ⟨g • (h • f), hf2⟩ :=
      Subtype.ext (mul_smul g h f)
    rw [this, e2, e1]
  · intro i P hP; rw [mul_smul, g9 i _ (h4 i P hP), h9 i P hP]

theorem nineLaw_pow {g : SemilinearAut L F} (hg : NineLaw A π C An An' g) (a : ℕ) :
    NineLaw A π C An An' (g ^ a) := by
  induction a with
  | zero => rw [pow_zero]; exact nineLaw_one
  | succ a ih => rw [pow_succ]; exact nineLaw_mul ih hg

theorem nineLaw_inv
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    {g : SemilinearAut L F} (hg : NineLaw A π C An An' g) : NineLaw A π C An An' g⁻¹ := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  have hbi : ∀ a : L, SemilinearAut.baseAut g (SemilinearAut.baseAut g⁻¹ a) = a := fun a => by
    rw [SemilinearAut.baseAut_inv]; exact (SemilinearAut.baseAut g).apply_symm_apply a
  have i1 : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g⁻¹ a ∈ A := fun a => by
    rw [g1 (SemilinearAut.baseAut g⁻¹ a), hbi]

  have i4 : ∀ i, ∀ P ∈ (C i).dom, g⁻¹ • P ∈ (C i).dom := by
    intro i P hP
    rcases hcover (g⁻¹ • P) with ⟨j, hj, -, -⟩ | ⟨e, he, -, hno⟩
    · have h1 : P ∈ (C j).dom := by simpa using g4 j _ hj
      rcases hcover P with ⟨i', -, huniq, -⟩ | ⟨e, -, -, hno'⟩
      · rw [huniq i hP, ← huniq j h1]; exact hj
      · exact absurd hP (hno' i)
    · have h1 : P ∈ (An e).dom := by simpa using g5 e _ he
      rcases hcover P with ⟨i', -, -, hno'⟩ | ⟨e', -, -, hno''⟩
      · exact absurd h1 (hno' e)
      · exact absurd hP (hno'' i)
  have i5 : ∀ e, ∀ P ∈ (An e).dom, g⁻¹ • P ∈ (An e).dom := by
    intro e P hP
    rcases hcover (g⁻¹ • P) with ⟨j, hj, -, hno⟩ | ⟨e', he', -, -⟩
    · have h1 : P ∈ (C j).dom := by simpa using g4 j _ hj
      rcases hcover P with ⟨i', -, -, hno'⟩ | ⟨e'', -, -, hno''⟩
      · exact absurd hP (hno' e)
      · exact absurd h1 (hno'' j)
    · have h1 : P ∈ (An e').dom := by simpa using g5 e' _ he'
      rcases hcover P with ⟨i', -, -, hno'⟩ | ⟨e'', -, huniq, -⟩
      · exact absurd hP (hno' e)
      · rw [huniq e hP, ← huniq e' h1]; exact he'
  refine ⟨i1, ?_, ?_, i4, i5, ?_, ?_, ?_, ?_⟩
  · rw [SemilinearAut.baseAut_inv, RingEquiv.symm_apply_eq, g2]
  · intro a ha
    have e := g3 ⟨_, ha⟩ (by rw [hbi]; exact a.2)
    have : (⟨SemilinearAut.baseAut g (SemilinearAut.baseAut g⁻¹ (a : L)), by rw [hbi]; exact a.2⟩ : A) = a :=
      Subtype.ext (hbi a)
    rw [this] at e
    exact e.symm
  · intro e; rw [inv_smul_eq_iff, g6]
  · intro e; rw [inv_smul_eq_iff, g7]
  · intro i f hf
    have key : g⁻¹ • f ∈ (C i).integers := by
      by_contra hnot
      have hx : (g⁻¹ • f)⁻¹ ∈ (C i).integers := ((C i).integers.mem_or_inv_mem _).resolve_left hnot
      obtain ⟨hgx, egx⟩ := g8 i _ hx
      have hgx' : g • (g⁻¹ • f)⁻¹ = f⁻¹ := by rw [smul_inv'', smul_inv_smul]

      have hxm : (C i).residue ⟨(g⁻¹ • f)⁻¹, hx⟩ = 0 := by
        have hmem : (⟨(g⁻¹ • f)⁻¹, hx⟩ : (C i).integers) ∈ RingHom.ker (C i).residue := by
          rw [(C i).ker_residue, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          rintro ⟨u, hu⟩
          apply hnot
          have hval : ((u⁻¹ : (C i).integersˣ) : (C i).integers).val = g⁻¹ • f := by
            have h1 : ((u⁻¹ : (C i).integersˣ) : (C i).integers).val * (g⁻¹ • f)⁻¹ = 1 := by
              have := congrArg (fun z : (C i).integers => (z : F)) u.inv_mul
              simpa [hu] using this
            rw [eq_inv_of_mul_eq_one_left h1, inv_inv]
          rw [← hval]; exact ((u⁻¹ : (C i).integersˣ) : (C i).integers).2
        exact hmem
      have hfm : (C i).residue ⟨f⁻¹, hgx' ▸ hgx⟩ = 0 := by
        have : (⟨f⁻¹, hgx' ▸ hgx⟩ : (C i).integers) = ⟨g • (g⁻¹ • f)⁻¹, hgx⟩ := Subtype.ext hgx'.symm
        rw [this, egx, hxm]

      have hf0 : f ≠ 0 := by
        rintro rfl; apply hnot; rw [smul_zero]; exact zero_mem _
      have h1 : (C i).residue (⟨f, hf⟩ * ⟨f⁻¹, hgx' ▸ hgx⟩) = 1 := by
        have : (⟨f, hf⟩ * ⟨f⁻¹, hgx' ▸ hgx⟩ : (C i).integers) = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
        rw [this, map_one]
      rw [map_mul, hfm, mul_zero] at h1
      exact zero_ne_one h1
    obtain ⟨hgk, egk⟩ := g8 i _ key
    refine ⟨key, ?_⟩
    have : (⟨g • (g⁻¹ • f), hgk⟩ : (C i).integers) = ⟨f, hf⟩ := Subtype.ext (smul_inv_smul g f)
    rw [this] at egk
    exact egk.symm
  · intro i P hP
    have := g9 i _ (i4 i P hP)
    rw [smul_inv_smul] at this
    exact this.symm

end Law

end KummerCongAux

open KummerCongAux in

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ s ∈ S, ∀ s' ∈ S, ∀ (k a b : ℕ),
      (∀ r : L, r ^ (ℓ ^ k) = (π : L) →
        ((SemilinearAut.baseAut s) ^ a) r = ((SemilinearAut.baseAut s') ^ b) r) →
      ∀ P : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • P = 0 → a • (s • P - P) = b • (s' • P - P) := by
  classical
  intro s hs s' hs' k a b hab P hP
  have hℓk : IsUnit (((ℓ ^ k : ℕ) : ℕ) : IsLocalRing.ResidueField A) := by
    rw [Nat.cast_pow]; exact hℓ.pow k

  have hS10 : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P) ∧
      (∀ a : L, a ≠ 0 → ∃ u : Aˣ, SemilinearAut.baseAut s a = u * a) := by
    intro s hs
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hS s hs
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
      ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne A π hπ hπ0 hrk _ h1 h2⟩

  have hP' : (ℓ ^ k : ℕ) • P = 0 := by rw [← natCast_zsmul]; exact hP
  have hlev : ∀ s ∈ S, s • (s • P - P) = s • P - P := fun s hs =>
    AlgebraicCurve.smul_smul_sub_eq_smul_sub_of_isUnit_natCast_of_nsmul_eq_zero_of_genusFF_of_semistableCovering_of_charZero_of_semistableModel A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w
      hpair hw hatt hnodes hcover hdisc hgenus M D S hS10 s hs s hs P (ℓ ^ k) hℓk hP'

  set g : SemilinearAut L F := (s' ^ b)⁻¹ * s ^ a with hgdef
  have hfix : ∀ r : L, r ^ (ℓ ^ k) = (π : L) → SemilinearAut.baseAut g r = r := by
    intro r hr
    show SemilinearAut.baseAut ((s' ^ b)⁻¹ * s ^ a) r = r
    rw [SemilinearAut.baseAut_mul, SemilinearAut.baseAut_inv, baseAut_pow, baseAut_pow]
    show ((SemilinearAut.baseAut s' ^ b).symm) ((SemilinearAut.baseAut s ^ a) r) = r
    rw [hab r hr, RingEquiv.symm_apply_apply]
  have hlaw : KummerCongAux.NineLaw A π C An An' g :=
    nineLaw_mul (nineLaw_inv hcover (nineLaw_pow (hS s' hs') b)) (nineLaw_pow (hS s hs) a)
  have hgP : g • P = P :=
    AlgebraicCurve.smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w
      hpair hw hatt hnodes hcover hdisc hgenus g hlaw ℓ hℓ k hfix M D P hP
  have hab' : s ^ a • P = s' ^ b • P := by
    rw [← inv_smul_eq_iff, ← mul_smul]; exact hgP
  rw [pow_smul_eq_add_nsmul s P (hlev s hs) a, pow_smul_eq_add_nsmul s' P (hlev s' hs') b] at hab'
  exact add_left_cancel hab'

#print axioms solution

end S_AlgebraicCurve_nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
