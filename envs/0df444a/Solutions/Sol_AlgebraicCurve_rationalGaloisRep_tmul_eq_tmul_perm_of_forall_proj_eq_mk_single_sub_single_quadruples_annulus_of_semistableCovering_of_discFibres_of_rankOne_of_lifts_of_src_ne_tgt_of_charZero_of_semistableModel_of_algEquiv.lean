-- Prove2me | solution 1 for AlgebraicCurve.rationalGaloisRep_tmul_eq_tmul_perm_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8843faa5-8900-5bc7-bd8b-91f3a918a7e9

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
import Theorems.Thm_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres
import Theorems.Thm_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
import Theorems.Thm_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_rationalGaloisRep_tmul_eq_tmul_perm_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_algEquiv
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

namespace NAT

theorem mem_of_pow_eq_one {L : Type} [Field L] (A : ValuationSubring L) {ζ : L} {N : ℕ} (hN : 0 < N)
    (hζ : ζ ^ N = 1) : ζ ∈ A := by
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have hζ' : ζ ^ (N - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hN, hζ]
    have : ζ = (ζ⁻¹) ^ (N - 1) := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right hζ'
    rw [this]
    exact pow_mem h _

theorem xi_pow_eq_one {L : Type} [Field L] {ℓ : ℕ} (ξ : ℕ → L) (hξ0 : ξ 0 = 1)
    (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (k : ℕ) : ξ k ^ ℓ ^ k = 1 := by
  induction k with
  | zero => simpa using hξ0
  | succ k ih => rw [pow_succ', pow_mul, hξ k, ih]

theorem mk_eq_mk_iff {K F : Type} [Field K] [Field F] [Algebra K F]
    (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ ((D : Divisor K F) - E) ∈ Divisor.principal (K := K) (F := F) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem mk_sub' {K F : Type} [Field K] [Field F] [Algebra K F]
    (D E : Divisor.degZero (K := K) (F := F)) : Pic0.mk (D - E) = Pic0.mk D - Pic0.mk E := rfl

theorem mk_zsmul' {K F : Type} [Field K] [Field F] [Algebra K F]
    (m : ℤ) (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk (m • D) = m • Pic0.mk D := rfl

theorem mk_eq_zero_iff {K F : Type} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ (D : Divisor K F) ∈ Divisor.principal (K := K) (F := F) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem degree_eq_sum {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (D : Divisor K F) : Divisor.degree D = D.sum (fun _ n => n) := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro v _
  simp [IsCurveOver.deg_eq_one_of_isAlgClosed v]

theorem degree_eq_zero_of_mapDomain_eq_zero {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] {β : Type} (f : Place K F → β) (D : Divisor K F) (h : Finsupp.mapDomain f D = 0) :
    Divisor.degree D = 0 := by
  rw [degree_eq_sum]
  have := congrArg (fun E : β →₀ ℤ => E.sum (fun _ n => n)) h
  simp only [Finsupp.sum_zero_index] at this
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)] at this
  exact this

theorem degree_single_eq_one {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (P : Place K F) : Divisor.degree (Finsupp.single P 1) = 1 := by
  rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed P]; simp

theorem coe_unit_inv_mul {L : Type} [Field L] (A : ValuationSubring L) (b : Aˣ) :
    (((b⁻¹ : Aˣ) : A) : L) * ((b : A) : L) = 1 := by
  have h : (((b⁻¹ : Aˣ) : A) * (b : A) : A) = 1 := Units.inv_mul b
  exact_mod_cast congrArg (fun a : A => (a : L)) h

theorem coe_unit_ne_zero {L : Type} [Field L] (A : ValuationSubring L) (b : Aˣ) : ((b : A) : L) ≠ 0 := by
  intro h
  have := coe_unit_inv_mul A b
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem sub_one_mem_maximalIdeal {L : Type} [Field L] (A : ValuationSubring L) (a : A)
    (h : IsLocalRing.residue A a = 1) : a - 1 ∈ IsLocalRing.maximalIdeal A := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, h, sub_self]

theorem level_eq
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (π : A) (hπ0 : π ≠ 0)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    {n m : ℕ} {Fbar : Fin n → Type} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (hmod0 : ∀ e, (((An e).modulus : A) : L) ≠ 0)
    (w : Fin m → ℕ) (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k)
    (x : Fin m → TateModule ℓ (Pic0 L F))
    (hx : ∀ e : Fin m,
      ∀ (k : ℕ) (Q Q' : Place L F), Q ∈ (An e).dom → Q' ∈ (An e).dom →
        (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (Q.evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d) →
        Q'.evalAt (An e).param = ξ k * Q.evalAt (An e).param →
        ∃ (Di : Fin n → Divisor L F) (r : ℕ) (eq : Fin r → Fin m) (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F),
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
          (∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0) ∧
          (∀ j l, Qq j l ∈ (An (eq j)).dom) ∧
          (∀ j, (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 0).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d) ∧
            (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 1).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d)) ∧
          (∀ j, ∃ u : Aˣ,
            (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) ∧
          (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
            (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
              (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) ∧
          ∀ hD : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈
              Divisor.degZero (K := L) (F := F),
            TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F), hD⟩)
    (τ : F ≃ₐ[L] F) (σ₀ : Equiv.Perm (Fin n)) (σ₁ : Equiv.Perm (Fin m))
    (hCdom : ∀ i, ∀ P : Place L F, P ∈ (C i).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (C (σ₀ i)).dom)
    (hAdom : ∀ e, ∀ P : Place L F, P ∈ (An e).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (An (σ₁ e)).dom)
    (Θ : ∀ i, Place (IsLocalRing.ResidueField A) (Fbar i) → Place (IsLocalRing.ResidueField A) (Fbar (σ₀ i)))
    (hΘ : ∀ i, ∀ P ∈ (C i).dom, (C (σ₀ i)).placeMap (SemilinearAut.ofAlgAut τ • P) = Θ i ((C i).placeMap P))
    (r : Fin m → IsLocalRing.ResidueField A) (hr : ∀ e, r e ≠ 0)
    (hPar : ∀ e, ∀ P ∈ (An e).dom,
      ∃ h : (SemilinearAut.ofAlgAut τ • P).evalAt (An (σ₁ e)).param * (P.evalAt (An e).param)⁻¹ ∈ A,
        IsUnit (⟨_, h⟩ : A) ∧ IsLocalRing.residue A ⟨_, h⟩ = r e)
    (e : Fin m) (k : ℕ)
    (hKT : ∀ (G : Fin n → Divisor L F) {ι : Type} [Fintype ι] (eq : ι → Fin m) (nq : ι → ℤ) (Qq : ι → Fin 4 → Place L F),
        (∀ i, ∀ P ∈ (G i).support, P ∈ (C i).dom) →
        (∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0) →
        (∀ j l, Qq j l ∈ (An (eq j)).dom) →
        (∀ j, ∃ u : Aˣ, (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) →
        (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
          (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
            (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) →
        ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈
          Divisor.principal (K := L) (F := F) →
        (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈ Divisor.principal (K := L) (F := F)) :
    SemilinearAut.ofAlgAut τ • ((x e : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k =
      ((x (σ₁ e) : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k := by
  classical
  set g : SemilinearAut L F := SemilinearAut.ofAlgAut τ with hg
  have hℓpos : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k
  have hξk : ξ k ^ ℓ ^ k = 1 := xi_pow_eq_one ξ hξ0 hξ k
  have hξA : ξ k ∈ A := mem_of_pow_eq_one A hℓpos hξk
  have hξ0' : ξ k ≠ 0 := by
    intro h; rw [h, zero_pow hℓpos.ne'] at hξk; exact zero_ne_one hξk
  have hξinvA : (ξ k)⁻¹ ∈ A := by
    have : (ξ k)⁻¹ ^ ℓ ^ k = 1 := by rw [inv_pow, hξk, inv_one]
    exact mem_of_pow_eq_one A hℓpos this

  have hU : ∀ e', ∀ P ∈ (An e').dom, ∃ v : Aˣ, IsLocalRing.residue A (v : A) = r e' ∧
      (g • P).evalAt (An (σ₁ e')).param = ((v : A) : L) * P.evalAt (An e').param := by
    intro e' P hP
    have hz0 : P.evalAt (An e').param ≠ 0 := ((An e').mem_dom P hP).2.2.2.1
    obtain ⟨hA', hunit, hres⟩ := hPar e' P hP
    refine ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hres, ?_⟩
    rw [IsUnit.unit_spec, Subtype.coe_mk, inv_mul_cancel_right₀ hz0]

  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (((An e).modulus : A) : L) two_pos
  have hc0 : c ≠ 0 := by rintro rfl; exact hmod0 e (by rw [← hc]; simp)
  have hcA : c ∈ A := by
    rcases A.mem_or_inv_mem c with h | h
    · exact h
    · have : c = (((An e).modulus : A) : L) * c⁻¹ := by
        rw [← hc]; field_simp
      rw [this]; exact mul_mem ((An e).modulus).2 h
  have hcm : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem 2
    have : (⟨c, hcA⟩ : A) ^ 2 = (An e).modulus := Subtype.ext (by push_cast; exact hc)
    rw [this]; exact (An e).modulus_mem
  obtain ⟨u, hu⟩ := hw e
  have hmodL : (((An e).modulus : A) : L) = ((u : A) : L) * (π : L) ^ w e := by
    rw [hu]; push_cast; rfl
  obtain ⟨Q, ⟨hQdom, hQval⟩, -⟩ := (An e).existsUnique_evalAt_eq ⟨c, hcA⟩ hcm (by exact hc0)
    ⟨⟨c, hcA⟩, hcm, by push_cast; rw [← hc, pow_two]⟩
  have hc'A : ξ k * c ∈ A := mul_mem hξA hcA
  have hc'm : (⟨ξ k * c, hc'A⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (⟨ξ k * c, hc'A⟩ : A) = ⟨ξ k, hξA⟩ * ⟨c, hcA⟩ := rfl
    rw [this]; exact Ideal.mul_mem_left _ _ hcm
  obtain ⟨Q', ⟨hQ'dom, hQ'val⟩, -⟩ := (An e).existsUnique_evalAt_eq ⟨ξ k * c, hc'A⟩ hc'm
    (by push_cast; exact mul_ne_zero hξ0' hc0)
    ⟨⟨(ξ k)⁻¹ * c, mul_mem hξinvA hcA⟩, by
      have : (⟨(ξ k)⁻¹ * c, mul_mem hξinvA hcA⟩ : A) = ⟨(ξ k)⁻¹, hξinvA⟩ * ⟨c, hcA⟩ := rfl
      rw [this]; exact Ideal.mul_mem_left _ _ hcm, by
      push_cast; rw [← hc]; field_simp⟩

  obtain ⟨Di, r₁, eq, nq, Qq, hDidom, hDipush, hQqdom, -, hQqrad, hQqbal, hDi⟩ := hx e k Q Q' hQdom hQ'dom
    ⟨2, w e, u, two_pos, by rw [hQval]; push_cast; rw [hc, hmodL]⟩ (by rw [hQval, hQ'val])

  have hgQdom : g • Q ∈ (An (σ₁ e)).dom := (hAdom e Q).1 hQdom
  have hgQ'dom : g • Q' ∈ (An (σ₁ e)).dom := (hAdom e Q').1 hQ'dom
  obtain ⟨vQ, hvQres, hvQ⟩ := hU e Q hQdom
  obtain ⟨vQ', hvQ'res, hvQ'⟩ := hU e Q' hQ'dom
  have hzgQ : (g • Q).evalAt (An (σ₁ e)).param = ((vQ : A) : L) * c := by rw [hvQ, hQval]
  have hzgQ' : (g • Q').evalAt (An (σ₁ e)).param = ((vQ' : A) : L) * (ξ k * c) := by rw [hvQ', hQ'val]
  obtain ⟨-, -, ⟨hzgQA, hzgQm⟩, hzgQ0, mQ, hmQ, hmodQ⟩ := (An (σ₁ e)).mem_dom (g • Q) hgQdom
  have hξzA : ξ k * (g • Q).evalAt (An (σ₁ e)).param ∈ A := mul_mem hξA hzgQA
  have hξzm : (⟨_, hξzA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (⟨_, hξzA⟩ : A) = ⟨ξ k, hξA⟩ * ⟨_, hzgQA⟩ := rfl
    rw [this]; exact Ideal.mul_mem_left _ _ hzgQm
  obtain ⟨R, ⟨hRdom, hRval⟩, -⟩ := (An (σ₁ e)).existsUnique_evalAt_eq ⟨_, hξzA⟩ hξzm
    (by push_cast; exact mul_ne_zero hξ0' hzgQ0)
    ⟨⟨(ξ k)⁻¹ * (mQ : L), mul_mem hξinvA mQ.2⟩, by
      have : (⟨(ξ k)⁻¹ * (mQ : L), mul_mem hξinvA mQ.2⟩ : A) = ⟨(ξ k)⁻¹, hξinvA⟩ * mQ := rfl
      rw [this]; exact Ideal.mul_mem_left _ _ hmQ, by
      push_cast; rw [hmodQ]; field_simp⟩
  have hzR : R.evalAt (An (σ₁ e)).param = ξ k * ((vQ : A) : L) * c := by
    rw [hRval]; push_cast; rw [hzgQ]; ring

  obtain ⟨Di', r₂, eq', nq', Qq', hDi'dom, hDi'push, hQq'dom, -, hQq'rad, hQq'bal, hDi'⟩ :=
    hx (σ₁ e) k (g • Q) R hgQdom hRdom
      ⟨2, w e, vQ ^ 2 * u, two_pos, by rw [hzgQ, mul_pow, hc, hmodL]; push_cast; ring⟩
      (by rw [hRval])

  set Dq : Fin 4 → Place L F := ![g • Q', g • Q, R, g • Q] with hDq
  have hDq0 : Dq 0 = g • Q' := rfl
  have hDq1 : Dq 1 = g • Q := rfl
  have hDq2 : Dq 2 = R := rfl
  have hDq3 : Dq 3 = g • Q := rfl
  have hDqdom : ∀ l, Dq l ∈ (An (σ₁ e)).dom := by
    intro l
    fin_cases l
    · exact hgQ'dom
    · exact hgQdom
    · exact hRdom
    · exact hgQdom
  have hDqrad : ∃ v : Aˣ, (Dq 0).evalAt (An (σ₁ e)).param = ((v : A) : L) * (Dq 2).evalAt (An (σ₁ e)).param := by
    refine ⟨vQ' * vQ⁻¹, ?_⟩
    rw [hDq0, hDq2, hzgQ', hzR]; push_cast
    linear_combination (-(((vQ' : A) : L) * ξ k * c)) * coe_unit_inv_mul A vQ
  have hDqbal : ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Dq 0).evalAt (An (σ₁ e)).param * (Dq 1).evalAt (An (σ₁ e)).param =
        (Dq 2).evalAt (An (σ₁ e)).param * (Dq 3).evalAt (An (σ₁ e)).param * (1 + ((t : A) : L)) := by
    have hres1 : IsLocalRing.residue A ((vQ' * vQ⁻¹ : Aˣ) : A) = 1 := by
      rw [Units.val_mul, map_mul, map_units_inv, hvQ'res, hvQres, mul_inv_cancel₀ (hr e)]
    refine ⟨((vQ' * vQ⁻¹ : Aˣ) : A) - 1, sub_one_mem_maximalIdeal A _ hres1, ?_⟩
    rw [hDq0, hDq1, hDq2, hDq3, hzgQ', hzgQ, hzR]; push_cast
    linear_combination (-(((vQ' : A) : L) * ξ k * c * (((vQ : A) : L) * c))) * coe_unit_inv_mul A vQ

  have hTchart : ∀ i j, σ₀ i = j →
      (∀ P ∈ (g • Di i).support, P ∈ (C j).dom) ∧ Finsupp.mapDomain (C j).placeMap (g • Di i) = 0 := by
    rintro i j rfl
    refine ⟨fun P hP => ?_, ?_⟩
    · rw [Finsupp.mem_support_iff, SemilinearAut.divisor_smul_apply] at hP
      have h := (hCdom i _).1 (hDidom i _ (Finsupp.mem_support_iff.mpr hP))
      rwa [smul_inv_smul] at h
    · have hcongr : Finsupp.mapDomain ((C (σ₀ i)).placeMap ∘ (g • ·)) (Di i) =
          Finsupp.mapDomain (Θ i ∘ (C i).placeMap) (Di i) := by
        unfold Finsupp.mapDomain
        apply Finsupp.sum_congr
        intro P hP
        simp only [Function.comp_apply, hΘ i P (hDidom i P hP)]
      rw [SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, hcongr, Finsupp.mapDomain_comp, hDipush i,
        Finsupp.mapDomain_zero]
  set G : Fin n → Divisor L F := fun j => g • Di (σ₀.symm j) - Di' j with hG
  have hGdom : ∀ j, ∀ P ∈ (G j).support, P ∈ (C j).dom := by
    intro j P hP
    have hP' : P ∈ (g • Di (σ₀.symm j)).support ∪ (Di' j).support := Finsupp.support_sub hP
    rcases Finset.mem_union.mp hP' with h | h
    · exact (hTchart (σ₀.symm j) j (Equiv.apply_symm_apply σ₀ j)).1 P h
    · exact hDi'dom j P h
  have hGpush : ∀ j, Finsupp.mapDomain (C j).placeMap (G j) = 0 := by
    intro j
    simp only [hG, Finsupp.mapDomain_sub, hDi'push j,
      (hTchart (σ₀.symm j) j (Equiv.apply_symm_apply σ₀ j)).2, sub_zero]

  set sQq : Fin r₁ → Fin 4 → Place L F := fun j l => g • Qq j l with hsQq
  have hsQqdom : ∀ j l, sQq j l ∈ (An (σ₁ (eq j))).dom := fun j l => (hAdom _ _).1 (hQqdom j l)
  have hsQqrad : ∀ j, ∃ v : Aˣ,
      (sQq j 0).evalAt (An (σ₁ (eq j))).param = ((v : A) : L) * (sQq j 2).evalAt (An (σ₁ (eq j))).param := by
    intro j
    obtain ⟨v, hv⟩ := hQqrad j
    obtain ⟨v0, -, h0⟩ := hU (eq j) (Qq j 0) (hQqdom j 0)
    obtain ⟨v2, -, h2⟩ := hU (eq j) (Qq j 2) (hQqdom j 2)
    refine ⟨v0 * v * v2⁻¹, ?_⟩
    simp only [hsQq]
    rw [h0, h2, hv]; push_cast
    linear_combination (-(((v0 : A) : L) * ((v : A) : L) * (Qq j 2).evalAt (An (eq j)).param)) * coe_unit_inv_mul A v2
  have hsQqbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (sQq j 0).evalAt (An (σ₁ (eq j))).param * (sQq j 1).evalAt (An (σ₁ (eq j))).param =
        (sQq j 2).evalAt (An (σ₁ (eq j))).param * (sQq j 3).evalAt (An (σ₁ (eq j))).param * (1 + ((t : A) : L)) := by
    intro j
    obtain ⟨t, ht, htv⟩ := hQqbal j
    obtain ⟨v0, h0r, h0⟩ := hU (eq j) (Qq j 0) (hQqdom j 0)
    obtain ⟨v1, h1r, h1⟩ := hU (eq j) (Qq j 1) (hQqdom j 1)
    obtain ⟨v2, h2r, h2⟩ := hU (eq j) (Qq j 2) (hQqdom j 2)
    obtain ⟨v3, h3r, h3⟩ := hU (eq j) (Qq j 3) (hQqdom j 3)
    have ht1 : IsLocalRing.residue A (1 + t) = 1 := by
      rw [map_add, map_one, (IsLocalRing.residue_eq_zero_iff t).2 ht, add_zero]
    have hres1 : IsLocalRing.residue A (((v0 * v1 * (v2 * v3)⁻¹ : Aˣ) : A) * (1 + t)) = 1 := by
      rw [map_mul, ht1, mul_one, Units.val_mul, map_mul, map_units_inv, Units.val_mul, Units.val_mul, map_mul,
        map_mul, h0r, h1r, h2r, h3r, mul_inv_cancel₀ (mul_ne_zero (hr (eq j)) (hr (eq j)))]
    refine ⟨((v0 * v1 * (v2 * v3)⁻¹ : Aˣ) : A) * (1 + t) - 1, sub_one_mem_maximalIdeal A _ hres1, ?_⟩
    simp only [hsQq]
    rw [h0, h1, h2, h3]; push_cast
    have hW := coe_unit_inv_mul A (v2 * v3)
    push_cast at hW
    linear_combination (((v0 : A) : L) * ((v1 : A) : L)) * htv -
      (((v0 : A) : L) * ((v1 : A) : L) * (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param *
        (1 + ((t : A) : L))) * hW

  set EQ : (Fin r₁ ⊕ Fin r₂) ⊕ Unit → Fin m := Sum.elim (Sum.elim (fun j => σ₁ (eq j)) eq') (fun _ => σ₁ e) with hEQ
  set NQ : (Fin r₁ ⊕ Fin r₂) ⊕ Unit → ℤ := Sum.elim (Sum.elim nq (fun j => -nq' j)) (fun _ => 1) with hNQ
  set QQ : (Fin r₁ ⊕ Fin r₂) ⊕ Unit → Fin 4 → Place L F := Sum.elim (Sum.elim sQq Qq') (fun _ => Dq) with hQQ
  have hQQdom : ∀ j l, QQ j l ∈ (An (EQ j)).dom := by
    rintro ((j | j) | j) l
    · exact hsQqdom j l
    · exact hQq'dom j l
    · exact hDqdom l
  have hQQrad : ∀ j, ∃ v : Aˣ, (QQ j 0).evalAt (An (EQ j)).param = ((v : A) : L) * (QQ j 2).evalAt (An (EQ j)).param := by
    rintro ((j | j) | j)
    · exact hsQqrad j
    · exact hQq'rad j
    · exact hDqrad
  have hQQbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A, (QQ j 0).evalAt (An (EQ j)).param * (QQ j 1).evalAt (An (EQ j)).param =
      (QQ j 2).evalAt (An (EQ j)).param * (QQ j 3).evalAt (An (EQ j)).param * (1 + ((t : A) : L)) := by
    rintro ((j | j) | j)
    · exact hsQqbal j
    · exact hQq'bal j
    · exact hDqbal

  have hdegq : ∀ (a b c' d : Place L F), Divisor.degree (Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single c' 1 - Finsupp.single d 1 : Divisor L F) = 0 := by
    intro a b c' d
    rw [map_sub, map_sub, map_add, degree_single_eq_one, degree_single_eq_one,
      degree_single_eq_one, degree_single_eq_one]; ring
  have hdegD : ∀ (G : Fin n → Divisor L F), (∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0) →
      ∀ {r : ℕ} (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F) (P P' : Place L F),
      (Finsupp.single P 1 - Finsupp.single P' 1 - ∑ i, G i -
        ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) ∈ Divisor.degZero (K := L) (F := F) := by
    intro G hG r nq Qq P P'
    rw [Divisor.mem_degZero, map_sub, map_sub, map_sub, map_sum, map_sum, degree_single_eq_one, degree_single_eq_one,
      Finset.sum_eq_zero (fun i _ => degree_eq_zero_of_mapDomain_eq_zero _ _ (hG i)),
      Finset.sum_eq_zero (fun j _ => by rw [map_zsmul, hdegq, smul_zero])]
    simp
  have e1 := hDi (hdegD Di hDipush nq Qq Q Q')
  have e2 := hDi' (hdegD Di' hDi'push nq' Qq' (g • Q) R)

  have hsquad : ∀ j, g • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) = (Finsupp.single (sQq j 0) 1 + Finsupp.single (sQq j 1) 1 - Finsupp.single (sQq j 2) 1 - Finsupp.single (sQq j 3) 1 : Divisor L F) := by
    intro j
    simp only [hsQq, smul_sub, smul_add, SemilinearAut.smul_single]
  have hreidx : ∑ i, g • Di i = ∑ j, g • Di (σ₀.symm j) :=
    Fintype.sum_equiv σ₀ _ _ (fun i => by rw [Equiv.symm_apply_apply])
  have hsD1 : g • (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i -
      ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) =
      Finsupp.single (g • Q) 1 - Finsupp.single (g • Q') 1 - ∑ j, g • Di (σ₀.symm j) -
      ∑ j, nq j • (Finsupp.single (sQq j 0) 1 + Finsupp.single (sQq j 1) 1 - Finsupp.single (sQq j 2) 1 - Finsupp.single (sQq j 3) 1 : Divisor L F) := by
    rw [smul_sub, smul_sub, smul_sub, Finset.smul_sum, Finset.smul_sum, SemilinearAut.smul_single,
      SemilinearAut.smul_single, hreidx]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, hsquad]

  have hdiff : (Finsupp.single (g • Q) 1 - Finsupp.single R 1 - ∑ i, Di' i -
        ∑ j, nq' j • (Finsupp.single (Qq' j 0) 1 + Finsupp.single (Qq' j 1) 1 - Finsupp.single (Qq' j 2) 1 - Finsupp.single (Qq' j 3) 1 : Divisor L F) : Divisor L F) -
      g • (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i -
        ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) =
      ∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F) := by
    rw [hsD1, hG, hNQ, hQQ, Finset.sum_sub_distrib, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, one_smul,
      hDq0, hDq1, hDq2, hDq3]
    abel
  set X₁ : Divisor.degZero (K := L) (F := F) :=
    SemilinearAut.degZeroSMulHom g ⟨_, hdegD Di hDipush nq Qq Q Q'⟩ with hX₁
  set X₂ : Divisor.degZero (K := L) (F := F) := ⟨_, hdegD Di' hDi'push nq' Qq' (g • Q) R⟩ with hX₂
  have hy1 : g • ((x e : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k = Pic0.mk X₁ := by
    show g • TateModule.proj ℓ (Pic0 L F) k (x e) = _
    rw [e1, SemilinearAut.pic0_smul_mk]
  have hy2 : ((x (σ₁ e) : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k = Pic0.mk X₂ := e2
  have hX : ((X₂ : Divisor L F) - X₁) = ∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F) := by
    rw [hX₂, hX₁, SemilinearAut.coe_degZeroSMulHom]; exact hdiff
  have htor : ((ℓ ^ k : ℕ) : ℤ) • (Pic0.mk X₂ - Pic0.mk X₁) = 0 := by
    have h1 : ((ℓ ^ k : ℕ) : ℤ) • ((x (σ₁ e) : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k = 0 :=
      TateModule.torsion (x (σ₁ e)) k
    have h2 : ((ℓ ^ k : ℕ) : ℤ) • (g • ((x e : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k) = 0 := by
      rw [← SemilinearAut.smul_zsmul, TateModule.torsion (x e) k]; exact smul_zero (A := Pic0 L F) g
    rw [← hy1, ← hy2, zsmul_sub, h1, h2, sub_zero]
  have hprin : ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F)) ∈
      Divisor.principal (K := L) (F := F) := by
    rw [← mk_sub', ← mk_zsmul', mk_eq_zero_iff] at htor
    have hc : (((((ℓ ^ k : ℕ) : ℤ) • (X₂ - X₁)) : Divisor.degZero (K := L) (F := F)) : Divisor L F) =
        ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F)) := by
      rw [← hX]; push_cast; rfl
    rwa [hc] at htor
  have hGprin := hKT G EQ NQ QQ hGdom hGpush hQQdom hQQrad hQQbal hprin
  rw [hy1, hy2, eq_comm, mk_eq_mk_iff, hX]
  exact hGprin

end NAT

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
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (hξ1 : ξ 1 ≠ 1)
    (x : Fin m → TateModule ℓ (Pic0 L F))
    (hx : ∀ e : Fin m,
      ∀ (k : ℕ) (Q Q' : Place L F), Q ∈ (An e).dom → Q' ∈ (An e).dom →
        (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (Q.evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d) →
        Q'.evalAt (An e).param = ξ k * Q.evalAt (An e).param →
        ∃ (Di : Fin n → Divisor L F) (r : ℕ) (eq : Fin r → Fin m) (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F),
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
          (∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0) ∧
          (∀ j l, Qq j l ∈ (An (eq j)).dom) ∧
          (∀ j, (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 0).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d) ∧
            (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 1).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d)) ∧
          (∀ j, ∃ u : Aˣ,
            (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) ∧
          (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
            (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
              (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) ∧
          ∀ hD : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1) : Divisor L F) ∈
              Divisor.degZero (K := L) (F := F),
            TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1), hD⟩)
    :
      ∀ (τ : F ≃ₐ[L] F) (σ₀ : Equiv.Perm (Fin n)) (σ₁ : Equiv.Perm (Fin m)),
        (∀ e, src (σ₁ e) = σ₀ (src e)) → (∀ e, tgt (σ₁ e) = σ₀ (tgt e)) →
        (∀ i, ∀ P : Place L F, P ∈ (C i).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (C (σ₀ i)).dom) →
        (∀ i, ∀ f : F, f ∈ (C i).integers ↔ τ f ∈ (C (σ₀ i)).integers) →
        (∀ e, ∀ P : Place L F, P ∈ (An e).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (An (σ₁ e)).dom) →
        (∀ e, src e ≠ tgt e) →
        ∀ e, ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (SemilinearAut.ofAlgAut τ) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e) =
          (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x (σ₁ e) := by
  classical
  intro τ σ₀ σ₁ hsrc htgt hCdom hInt hAdom hloop e
  set g : SemilinearAut L F := SemilinearAut.ofAlgAut τ with hg
  have hgP : ∀ P : Place L F, g • P = τ • P := fun P => rfl
  have hgA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A := by
    intro a; rw [hg, SemilinearAut.baseAut_ofAlgAut]; exact Iff.rfl
  have hInt' : ∀ i (f : F), f ∈ (C i).integers ↔ g • f ∈ (C (σ₀ i)).integers := by
    intro i f; rw [hg, SemilinearAut.ofAlgAut_smul]; exact hInt i f

  have hKT : ∀ (k : ℕ) (G : Fin n → Divisor L F) {ι : Type} [Fintype ι] (eq : ι → Fin m) (nq : ι → ℤ) (Qq : ι → Fin 4 → Place L F),
      (∀ i, ∀ P ∈ (G i).support, P ∈ (C i).dom) →
      (∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0) →
      (∀ j l, Qq j l ∈ (An (eq j)).dom) →
      (∀ j, ∃ u : Aˣ, (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) →
      (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
        (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
          (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) →
      ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈
        Divisor.principal (K := L) (F := F) →
      (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈ Divisor.principal (K := L) (F := F) := by
    intro k G ι _ eq nq Qq hGdom hGpush hQdom hrad hbal hkG
    have hk : IsUnit (((ℓ ^ k : ℕ) : ℕ) : IsLocalRing.ResidueField A) := by
      rw [Nat.cast_pow]; exact hℓ.pow k
    exact AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc
      (by simpa [Fintype.card_fin] using hgenus) M D (ℓ ^ k) hk G hGdom hGpush
      eq nq Qq hQdom hrad hbal hkG

  have hΘex : ∀ i, ∃ Θ : Place (IsLocalRing.ResidueField A) (Fbar i) → Place (IsLocalRing.ResidueField A) (Fbar (σ₀ i)),
      ∀ P ∈ (C i).dom, (C (σ₀ i)).placeMap (g • P) = Θ ((C i).placeMap P) := by
    intro i
    obtain ⟨θ, Θ, -, -, -, hΘ⟩ := AlgebraicCurve.ComponentChart.exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres A hrk F (hratBar i) (hratBar (σ₀ i)) (C i) (C (σ₀ i)) (hratF i) (hratF (σ₀ i))
      (hdisc i) (hdisc (σ₀ i)) g hgA (hInt' i) (hCdom i)
    exact ⟨Θ, hΘ⟩
  choose Θ hΘ using hΘex

  have hParEx : ∀ e₁ : Fin m, ∃ r : IsLocalRing.ResidueField A, r ≠ 0 ∧ ∀ P ∈ (An e₁).dom,
      ∃ h : (g • P).evalAt (An (σ₁ e₁)).param * (P.evalAt (An e₁).param)⁻¹ ∈ A,
        IsUnit (⟨_, h⟩ : A) ∧ IsLocalRing.residue A ⟨_, h⟩ = r := by
    intro e₁

    set An₁ : Annulus A F := (An e₁).comap τ.symm with hAn₁
    set C₁ : ComponentChart A F (Fbar (src e₁)) := (C (src e₁)).comap τ.symm with hC₁
    have hττ : ∀ P : Place L F, τ • τ.symm • P = P := fun P => by
      rw [← AlgEquiv.aut_inv, smul_inv_smul]
    have hdom₁ : (An (σ₁ e₁)).dom = An₁.dom := by
      ext P
      rw [hAn₁, Annulus.mem_comap_dom, hAdom e₁, hgP, hττ]
    have hatt₁ : An₁.IsAttached C₁ (xs e₁) := by
      rw [hAn₁, hC₁]; exact Annulus.IsAttached.comap τ.symm (An e₁) (hatt e₁).1
    have hz' : (An (σ₁ e₁)).param ∈ (C (src (σ₁ e₁))).integers := (hatt (σ₁ e₁)).1.2.1
    have hz'C₁ : (An (σ₁ e₁)).param ∈ C₁.integers := by
      rw [hC₁, ComponentChart.mem_comap_integers, hInt (src e₁), AlgEquiv.apply_symm_apply, ← hsrc e₁]; exact hz'
    have hz₂ : ∃ h : (An (σ₁ e₁)).param ∈ C₁.integers, C₁.residue ⟨(An (σ₁ e₁)).param, h⟩ ≠ 0 := by
      refine ⟨hz'C₁, ?_⟩
      set z' : F := (An (σ₁ e₁)).param with hz'def

      have hord := (hatt (σ₁ e₁)).1.2.2.1
      have hres' : (C (src (σ₁ e₁))).residue ⟨z', hz'⟩ ≠ 0 := by
        intro h0; rw [h0, Place.ord_zero] at hord; exact zero_ne_one hord
      have hunit' : IsUnit (⟨z', hz'⟩ : (C (src (σ₁ e₁))).integers) := by
        by_contra hnu
        apply hres'
        have hm : (⟨z', hz'⟩ : (C (src (σ₁ e₁))).integers) ∈ IsLocalRing.maximalIdeal _ := hnu
        rw [← (C (src (σ₁ e₁))).ker_residue] at hm
        exact hm
      obtain ⟨u, hu⟩ := hunit'
      have huF : (((u : (C (src (σ₁ e₁))).integers)) : F) = z' := congrArg Subtype.val hu
      have hzi : z'⁻¹ ∈ (C (src (σ₁ e₁))).integers := by
        have h1 : (((u⁻¹ : ((C (src (σ₁ e₁))).integers)ˣ) : (C (src (σ₁ e₁))).integers) : F) * z' = 1 := by
          rw [← huF]; push_cast; rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
        rw [← eq_inv_of_mul_eq_one_left h1]; exact ((u⁻¹ : ((C (src (σ₁ e₁))).integers)ˣ) : (C (src (σ₁ e₁))).integers).2

      have h2 : τ.symm z' ∈ (C (src e₁)).integers := by
        rw [hInt (src e₁), AlgEquiv.apply_symm_apply, ← hsrc e₁]; exact hz'
      have h2i : (τ.symm z')⁻¹ ∈ (C (src e₁)).integers := by
        rw [← map_inv₀, hInt (src e₁), AlgEquiv.apply_symm_apply, ← hsrc e₁]; exact hzi

      change ((C (src e₁)).comap τ.symm).residue ⟨z', hz'C₁⟩ ≠ 0
      rw [ComponentChart.comap_residue_apply]
      intro h0
      have hker : (⟨τ.symm z', h2⟩ : (C (src e₁)).integers) ∈ RingHom.ker (C (src e₁)).residue := by
        rw [RingHom.mem_ker]; convert h0 using 2
      rw [(C (src e₁)).ker_residue] at hker
      apply hker
      refine IsUnit.of_mul_eq_one (b := ⟨(τ.symm z')⁻¹, h2i⟩) (Subtype.ext ?_)
      push_cast
      have hz'0 : τ.symm z' ≠ 0 := by
        intro h; apply hres'
        have : z' = 0 := by simpa using congrArg τ h
        exfalso; rw [this] at huF
        exact u.ne_zero (Subtype.ext (by simpa using huF))
      exact mul_inv_cancel₀ hz'0
    obtain ⟨r, hr0, hr⟩ := AlgebraicCurve.Annulus.exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne A hrk F An₁ (An (σ₁ e₁)) hdom₁ C₁ (xs e₁) (hratBar (src e₁) (xs e₁)) hatt₁ hz₂
    refine ⟨r, hr0, fun P hP => ?_⟩
    have hP₁ : g • P ∈ An₁.dom := by rw [← hdom₁]; exact (hAdom e₁ P).1 hP
    have hev : (g • P).evalAt An₁.param = P.evalAt (An e₁).param := by
      rw [hgP, hAn₁, Annulus.comap_param, AlgEquiv.symm_symm]
      exact Place.Transport.evalAt_smul τ P ((An e₁).mem_dom P hP).1 (An e₁).param
    have := hr (g • P) hP₁
    rwa [hev] at this
  choose r hr0 hPar using hParEx

  have hlevel : ∀ k, g • ((x e : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k = ((x (σ₁ e) : TateModule ℓ (Pic0 L F)) : ℕ → Pic0 L F) k :=
    fun k => NAT.level_eq A π hπ0 C An (fun e₁ => (hpair e₁).2.2.1) w hw ℓ hℓ ξ hξ0 hξ x hx τ σ₀ σ₁ hCdom hAdom Θ hΘ r hr0
      (fun e₁ P hP => hPar e₁ P hP) e k (fun G ι _ eq nq Qq => hKT k G eq nq Qq)
  have hrep : TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) g (x e) = x (σ₁ e) :=
    Subtype.ext (funext fun k => by rw [TateModule.rep_apply]; exact hlevel k)
  rw [ModularCurve.rationalGaloisRep_tmul, hrep]

end S_AlgebraicCurve_rationalGaloisRep_tmul_eq_tmul_perm_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_algEquiv
end P2MW
export P2MW.S_AlgebraicCurve_rationalGaloisRep_tmul_eq_tmul_perm_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_algEquiv (solution)
