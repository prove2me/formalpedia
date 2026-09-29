-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.exists_isInvertible_pullback_oneProdNsmul_iso_of_forall_torsion_pullback_oneProdTranslation_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6ce3cbab-fef9-555c-9a79-48017466f178

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
import Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split
import Theorems.Thm_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_isInvertible_pullback_oneProdNsmul_iso_of_forall_torsion_pullback_oneProdTranslation_iso
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType MvFormalGroup.instIsCommAddMv CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction CerednikDrinfeld.FormalODModule.isComm MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec AlgebraicGeometry.Scheme.nilpPoints_map_val LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one"
p2m_attr_erase "simp" "LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply CerednikDrinfeld.SpecialFormal.Rigidified.mk.injEq CerednikDrinfeld.FormalODModule.actRingHom_apply CerednikDrinfeld.SpecialFormalODModule.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.Hom.mk.injEq CerednikDrinfeld.FormalODModule.map_id CerednikDrinfeld.SpecialFormal.Series.map_id CerednikDrinfeld.SpecialFormal.Rigidified.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.twist_obj CerednikDrinfeld.SpecialFormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.map_varpi CerednikDrinfeld.FormalODModule.map_act CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.injEq CerednikDrinfeld.FormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.Hom.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.map_F CerednikDrinfeld.SpecialFormal.Rigidified.map_n CerednikDrinfeld.SpecialFormal.Rigidified.map_ρ CerednikDrinfeld.SpecialFormal.IsLawHom.toHom_toPowerSeries CerednikDrinfeld.SpecialFormal.Series.map_ringHom_id CerednikDrinfeld.FormalODModule.actEnd_toPowerSeries CerednikDrinfeld.SpecialFormal.Rigidified.map_X CerednikDrinfeld.FormalODModule.varpiEnd_toPowerSeries"
p2m_attr_erase "simp" "CerednikDrinfeld.FormalODModule.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe"
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd GoodReductionJacobian.BareDeformation.mk.sizeOf_spec GoodReductionJacobian.BareDeformation.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (hrig : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓠) ≅ 𝟙_ _))
    (hinv : ∀ Q : L.AlgPoints hc k, ℓ • Q = 0 →
      Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj 𝓠 ≅ 𝓠)) :
    ∃ 𝓟 : (pullback f f).Modules, Scheme.Modules.IsInvertible 𝓟 ∧
      Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟 ≅ 𝓠) := by
  classical

  have hunit : IsUnit (ℓ : k) := isUnit_iff_ne_zero.2 hℓ
  obtain ⟨hfin, hflat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit L hA (fun t x y => hc t x y) ℓ hunit
  haveI := hfin
  haveI := hflat
  haveI : Smooth f := hA.smooth
  let s₀ : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
  have hfib : f.base ⁻¹' {s₀} = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    show f.base a = s₀
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace ↥A := ⟨by rw [← hfib]; exact (hA.connectedFibres s₀).isPreconnected⟩
  haveI : Nonempty ↥A := by
    obtain ⟨a, -⟩ := (hA.connectedFibres s₀).nonempty
    exact ⟨a⟩
  haveI : IsIntegral A := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
  haveI : Surjective (L.schemeNsmul ℓ) :=
    GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field L hc ℓ

  set q : pullback f f ⟶ pullback f f := pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
      (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition) with hqdef
  have hq_fst : q ≫ pullback.fst f f = pullback.fst f f := by rw [hqdef]; exact pullback.lift_fst _ _ _
  have hq_snd : q ≫ pullback.snd f f = pullback.snd f f ≫ L.schemeNsmul ℓ := by rw [hqdef]; exact pullback.lift_snd _ _ _
  have sq : IsPullback q (pullback.snd f f) (pullback.snd f f) (L.schemeNsmul ℓ) := by
    refine IsPullback.of_right ?_ hq_snd (IsPullback.of_hasPullback f f)
    rw [hq_fst, RelativeGroupLaw.schemeNsmul_over]
    exact IsPullback.of_hasPullback f f
  haveI : IsFinite q := MorphismProperty.of_isPullback sq.flip hfin
  haveI : Flat q := MorphismProperty.of_isPullback sq.flip hflat
  haveI : Surjective q := MorphismProperty.of_isPullback sq.flip inferInstance

  let Hn : AddSubgroup (L.AlgPoints hc k) :=
    { carrier := {P | ℓ • P = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [smul_neg, ha, neg_zero] }
  let σ : ↥Hn → (pullback f f ⟶ pullback f f) := fun P =>
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (P : L.AlgPoints hc k)))
      (by rw [Category.assoc, translation_over]; exact pullback.condition)
  have hσ_fst : ∀ P, σ P ≫ pullback.fst f f = pullback.fst f f := fun P => pullback.lift_fst _ _ _
  have hσ_snd : ∀ P, σ P ≫ pullback.snd f f =
      pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (P : L.AlgPoints hc k)) :=
    fun P => pullback.lift_snd _ _ _
  have hσ0 : σ 0 = 𝟙 (pullback f f) := by
    apply pullback.hom_ext
    · rw [hσ_fst, Category.id_comp]
    · rw [hσ_snd, Category.id_comp]
      change pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) = _
      rw [translation_toPoint_zero, Category.comp_id]
  have hσadd : ∀ P Q : ↥Hn, σ (P + Q) = σ P ≫ σ Q := by
    intro P Q
    apply pullback.hom_ext
    · rw [hσ_fst, Category.assoc, hσ_fst, hσ_fst]
    · rw [hσ_snd, Category.assoc, hσ_snd, ← Category.assoc, hσ_snd, Category.assoc]
      change pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint ((P : L.AlgPoints hc k) + (Q : L.AlgPoints hc k))) = _
      rw [translation_toPoint_add]

  obtain ⟨ψ, hψ0, hψadd⟩ :=
    AlgebraicGeometry.RiemannForm.exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
      k f L hc hA g hdim ℓ 𝓠 h𝓠 hrig hinv

  have hfree : ∀ ⦃Z : Scheme.{0}⦄ (v : Z ⟶ pullback f f) (P : ↥Hn), Nonempty ↥Z → v ≫ σ P = v → P = 0 := by
    intro Z v P hZ hv
    have h1 : (v ≫ pullback.snd f f) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (P : L.AlgPoints hc k)) =
        v ≫ pullback.snd f f := by
      rw [Category.assoc, ← hσ_snd, ← Category.assoc, hv]
    have := AlgebraicGeometry.RiemannForm.eq_zero_of_comp_translation_eq_of_nonempty k f L hc hZ _ _ h1
    exact Subtype.ext this
  have hsplit : ∀ ⦃Z : Scheme.{0}⦄ (g₁ g₂ : Z ⟶ pullback f f), g₁ ≫ q = g₂ ≫ q →
      ∃ U : ↥Hn → Z.Opens, ⨆ P, U P = ⊤ ∧ ∀ P, (U P).ι ≫ g₂ = (U P).ι ≫ g₁ ≫ σ P := by
    intro Z g₁ g₂ h
    have h1 : g₁ ≫ pullback.fst f f = g₂ ≫ pullback.fst f f := by
      rw [← hq_fst, ← Category.assoc, h, Category.assoc]
    have h2 : (g₁ ≫ pullback.snd f f) ≫ L.schemeNsmul ℓ = (g₂ ≫ pullback.snd f f) ≫ L.schemeNsmul ℓ := by
      rw [Category.assoc, ← hq_snd, ← Category.assoc, h, Category.assoc, hq_snd, Category.assoc]
    obtain ⟨U, hU, hUP⟩ :=
      GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
        k f L hc hA g hdim ℓ hℓ (g₁ ≫ pullback.snd f f) (g₂ ≫ pullback.snd f f) h2
    refine ⟨fun P => U ⟨P.1, P.2⟩, ?_, ?_⟩
    · refine le_antisymm le_top ?_
      rw [← hU]
      exact iSup_le fun P => le_iSup_of_le (⟨P.1, P.2⟩ : ↥Hn) le_rfl
    · intro P
      dsimp only
      apply pullback.hom_ext
      · simp only [Category.assoc, hσ_fst]
        rw [h1]
      · simp only [Category.assoc, hσ_snd]
        have := hUP ⟨P.1, P.2⟩
        simp only [Category.assoc] at this
        exact this

  obtain ⟨D, hD⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split
      q (↥Hn) σ hσ0 hσadd hfree hsplit 𝓠 (fun P => ψ (P : L.AlgPoints hc k) P.2)
      (hψ0 Hn.zero_mem hσ0) (fun P Q => hψadd _ _ P.2 Q.2 (P + Q).2 (hσadd P Q))

  obtain ⟨𝓟, h𝓟, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
      q D (fun i => by rw [hD i]; exact h𝓠)
  refine ⟨𝓟, h𝓟, ⟨?_⟩⟩
  have h₁ := congrArg (fun φ => Pseudofunctor.DescentData.Hom.hom φ ()) e.hom_inv_id
  have h₂ := congrArg (fun φ => Pseudofunctor.DescentData.Hom.hom φ ()) e.inv_hom_id
  simp only [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.id_hom] at h₁ h₂
  have e₁ : (Scheme.Modules.pullback q).obj 𝓟 ≅ D.obj () := ⟨(e.hom).hom (), (e.inv).hom (), h₁, h₂⟩
  exact e₁ ≪≫ eqToIso (hD ())

end S_AlgebraicGeometry_RiemannForm_exists_isInvertible_pullback_oneProdNsmul_iso_of_forall_torsion_pullback_oneProdTranslation_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_exists_isInvertible_pullback_oneProdNsmul_iso_of_forall_torsion_pullback_oneProdTranslation_iso (solution)
