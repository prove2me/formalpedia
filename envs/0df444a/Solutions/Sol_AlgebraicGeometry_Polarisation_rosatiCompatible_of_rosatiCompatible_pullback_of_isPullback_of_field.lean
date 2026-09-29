-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/97c2cd2a-bb39-5331-bf79-3f8692a09f7b

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv"
p2m_attr_erase "instance" "AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.mk.sizeOf_spec CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace RosatiReflect17

theorem nonempty_iso_of_pullback_iso_of_isIso {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] {M M' : Y.Modules}
    (h : Nonempty ((Scheme.Modules.pullback e).obj M ≅ (Scheme.Modules.pullback e).obj M')) : Nonempty (M ≅ M') := by
  obtain ⟨i⟩ := h
  have hid : inv e ≫ e = 𝟙 Y := IsIso.inv_hom_id e
  let F : ∀ N : Y.Modules, (Scheme.Modules.pullback (inv e)).obj ((Scheme.Modules.pullback e).obj N) ≅ N := fun N =>
    (Scheme.Modules.pullbackComp (inv e) e).app N ≪≫ (Scheme.Modules.pullbackCongr hid).app N ≪≫
      (Scheme.Modules.pullbackId Y).app N
  exact ⟨(F M).symm ≪≫ (Scheme.Modules.pullback (inv e)).mapIso i ≪≫ F M'⟩

theorem nonempty_iso_of_locIsoOnBase_field {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {M M' : X.Modules} (h : LocIsoOnBase q M M') : Nonempty (M ≅ M') := by
  obtain ⟨U, hsU, hU⟩ := h ⟨⊥, Ideal.bot_prime⟩
  have hUtop : U = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : x = ⟨⊥, Ideal.bot_prime⟩ := Subsingleton.elim _ _
    rw [this]; exact hsU
  subst hUtop
  haveI : IsIso (q ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens)).ι := by
    rw [Scheme.Hom.preimage_top]
    exact (inferInstance : IsIso (Scheme.topIso X).hom)
  exact nonempty_iso_of_pullback_iso_of_isIso _ hU

theorem locIsoOnBase_of_nonempty_iso {S : Type} [CommRing S] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of S))
    {M M' : X.Modules} (h : Nonempty (M ≅ M')) : LocIsoOnBase q M M' := by
  obtain ⟨i⟩ := h
  intro s
  exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso i⟩⟩

theorem isInvertible_mumfordBundle {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) := by
  have hd := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).1
  exact AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2 (h𝓛.pullback _)
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2 (hd.pullback _) (hd.pullback _))

theorem isPullback_prod {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (f' : A' ⟶ Spec (CommRingCat.of k'))
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    IsPullback
      (pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))
      (prodStr f' f') (prodStr f f) (Spec.map (CommRingCat.ofHom φ)) := by

  have big : IsPullback (pullback.snd f' f' ≫ g) (pullback.fst f' f') f (f' ≫ Spec.map (CommRingCat.ofHom φ)) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback f' f').flip hg
  have top : IsPullback
      (pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))
      (pullback.fst f' f') (pullback.fst f f) g := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f f) (h₂₂ := f) (v₁₃ := f) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback f f).flip
    rw [pullback.lift_snd, hg.w]
    exact big
  exact IsPullback.paste_vert top hg

end RosatiReflect17

open RosatiReflect17 in
theorem solution
    (k k' : Type) [Field k] [Field k'] [Algebra k k']
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (f' : A' ⟶ Spec (CommRingCat.of k')) (L' : RelativeGroupLaw k' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (A' ⟶ A')) (act_over' : ∀ x : I, act' x ≫ f' = f')
    (hact : ∀ x : I, act' x ≫ g = g ≫ act x) (star : I → I)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : RosatiCompatible f' L' ((Scheme.Modules.pullback g).obj 𝓛) act' act_over' star) :
    RosatiCompatible f L 𝓛 act act_over star := by
  intro b

  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) := isInvertible_mumfordBundle f L h𝓛
  have hAA : AbelianSchemePropertyBundle k (pullback.fst f f ≫ f) :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.prodStr_commRing hA hA
  have hGG := isPullback_prod (algebraMap k k') f f' g hg
  obtain ⟨mbc⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
    k k' (algebraMap k k') f L f' L' g hg hg_mul 𝓛 h𝓛

  obtain ⟨i'⟩ := nonempty_iso_of_locIsoOnBase_field (pullback.fst f' f' ≫ f') (h b)

  have hGP : pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫
      pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition) =
      pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b) (by rw [Category.assoc, act_over']; exact pullback.condition) ≫
      pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, hact]
  have hGQ : pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫
      pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition) =
      pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f') (by rw [Category.assoc, act_over']; exact pullback.condition) ≫
      pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, hact]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]

  apply locIsoOnBase_of_nonempty_iso
  refine AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback k
    (pullback.fst f f ≫ f) hAA _ _ (hΛ.pullback _) (hΛ.pullback _) k' (algebraMap k k') (pullback.fst f' f' ≫ f') _ hGG ?_
  refine ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hGP).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ (Scheme.Modules.pullback _).mapIso mbc.symm ≪≫ i' ≪≫
    (Scheme.Modules.pullback _).mapIso mbc ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hGQ.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm⟩

end S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field (solution)
