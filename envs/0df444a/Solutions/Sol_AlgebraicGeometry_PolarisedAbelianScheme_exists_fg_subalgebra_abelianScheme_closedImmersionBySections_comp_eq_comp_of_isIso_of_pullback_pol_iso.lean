-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4a0572fc-620c-5929-ad06-95813db289a2

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II"
p2m_attr_erase "instance" "DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw CerednikDrinfeld.QM AlgebraicGeometry.PolarisedAbelianScheme

attribute [local instance] MvPolynomial.gradedAlgebra

namespace NoethBC20

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem one_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) : (G.one t₁).1 = (G.one t₂).1 := by
  subst h; rfl

theorem inv_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (G.inv t₁ P₁).1 = (G.inv t₂ P₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  rfl

theorem toBase_injective {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    Function.Injective
      (baseChangePointToBase ι : SchemeHomOver t' (baseChangeStr ι f) → SchemeHomOver (t' ≫ ι) f) :=
  (baseChangePointEquiv ι t').injective

section Endo

variable (φ : A ⟶ A) (hφ : φ ≫ f = f)

def bcEndo : baseChangeScheme ι f ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst f ι ≫ φ) (pullback.snd f ι) (by rw [Category.assoc, hφ, pullback.condition])

@[reassoc (attr := simp)]
theorem bcEndo_fst : bcEndo ι φ hφ ≫ pullback.fst f ι = pullback.fst f ι ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcEndo_snd : bcEndo ι φ hφ ≫ pullback.snd f ι = pullback.snd f ι :=
  pullback.lift_snd _ _ _

theorem bcEndo_over : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f :=
  pullback.lift_snd _ _ _

theorem bcEndo_congr {φ ψ : A ⟶ A} (h : φ = ψ) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) :
    bcEndo ι φ hφ = bcEndo ι ψ hψ := by
  subst h; rfl

theorem bcEndo_eq_id {φ : A ⟶ A} (h : φ = 𝟙 A) (hφ : φ ≫ f = f) : bcEndo ι φ hφ = 𝟙 _ := by
  subst h
  apply pullback.hom_ext
  · rw [bcEndo_fst, Category.id_comp, Category.comp_id]
  · rw [bcEndo_snd, Category.id_comp]

theorem bcEndo_eq_comp {χ ψ φ : A ⟶ A} (h : χ = ψ ≫ φ) (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f) (hφ : φ ≫ f = f) :
    bcEndo ι χ hχ = bcEndo ι ψ hψ ≫ bcEndo ι φ hφ := by
  subst h
  apply pullback.hom_ext
  · simp only [bcEndo_fst, Category.assoc, bcEndo_fst_assoc]
  · simp only [bcEndo_snd, Category.assoc]

theorem toBase_pushPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (pushPt (bcEndo ι φ hφ) h' P) = pushPt φ hφ (baseChangePointToBase ι P) := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, mapPt_coe, Category.assoc, bcEndo_fst]

theorem pushPt_bcEndo_mul (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (G.mul t P Q) = G.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι φ hφ) h' ((G.baseChange ι).mul t' P Q) =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) h' P) (pushPt (bcEndo ι φ hφ) h' Q) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

theorem pushPt_bcEndo_add (G : RelativeGroupLaw R f) {χ ψ : A ⟶ A} (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt χ hχ P = G.mul t (pushPt φ hφ P) (pushPt ψ hψ P))
    (hχ' : bcEndo ι χ hχ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hφ' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hψ' : bcEndo ι ψ hψ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι χ hχ) hχ' P =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) hφ' P) (pushPt (bcEndo ι ψ hψ) hψ' P) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

end Endo

section Lev

variable (f) {C : Scheme.{u}} (lev : C ⟶ A)

abbrev bcLevScheme : Scheme.{u} :=
  pullback (lev ≫ f) ι

def bcLev : bcLevScheme ι f lev ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst (lev ≫ f) ι ≫ lev) (pullback.snd (lev ≫ f) ι)
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem bcLev_fst : bcLev ι f lev ≫ pullback.fst f ι = pullback.fst (lev ≫ f) ι ≫ lev :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcLev_snd : bcLev ι f lev ≫ pullback.snd f ι = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem bcLev_comp_baseChangeStr : bcLev ι f lev ≫ baseChangeStr ι f = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem isPullback_fst_bcLev :
    IsPullback (pullback.fst (lev ≫ f) ι) (bcLev ι f lev) lev (pullback.fst f ι) := by
  refine IsPullback.of_bot ?_ (bcLev_fst ι f lev).symm (IsPullback.of_hasPullback f ι)
  rw [bcLev_snd]
  exact IsPullback.of_hasPullback (lev ≫ f) ι

theorem isClosedImmersion_bcLev [IsClosedImmersion lev] : IsClosedImmersion (bcLev ι f lev) :=
  MorphismProperty.of_isPullback (isPullback_fst_bcLev ι f lev) ‹_›

theorem isFinite_bcLev_comp [IsFinite (lev ≫ f)] : IsFinite (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem flat_bcLev_comp [Flat (lev ≫ f)] : Flat (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem locallyOfFinitePresentation_bcLev_comp [LocallyOfFinitePresentation (lev ≫ f)] :
    LocallyOfFinitePresentation (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem factorsThrough_bcLev_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P ↔ FactorsThrough lev (baseChangePointToBase ι P) := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ pullback.fst (lev ≫ f) ι, ?_⟩
    rw [baseChangePointToBase_coe, ← hP₀, Category.assoc, Category.assoc, bcLev_fst]
  · rintro ⟨Q₀, hQ₀⟩
    rw [baseChangePointToBase_coe] at hQ₀
    refine ⟨pullback.lift Q₀ (P.1 ≫ pullback.snd f ι) ?_, ?_⟩
    · rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, pullback.condition]
    · apply pullback.hom_ext
      · rw [Category.assoc, bcLev_fst, ← Category.assoc, pullback.lift_fst, hQ₀]
      · rw [Category.assoc, bcLev_snd, pullback.lift_snd]

theorem toBase_nsmulPt (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (n : ℕ) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (nsmulPt (G.baseChange ι) t' n P) =
      nsmulPt G (t' ≫ ι) n (baseChangePointToBase ι P) := by
  induction n with
  | zero => exact baseChangePointToBase_one ι G t'
  | succ n ih => simp only [nsmulPt, baseChangePointToBase_mul, ih]

theorem lev_sub_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (G.mul t P Q) ∧ FactorsThrough lev (G.inv t P))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) Q →
      FactorsThrough (bcLev ι f lev) ((G.baseChange ι).mul t' P Q) ∧
        FactorsThrough (bcLev ι f lev) ((G.baseChange ι).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_bcLev_iff] at hP hQ
  rw [factorsThrough_bcLev_iff, factorsThrough_bcLev_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact H _ _ _ hP hQ

theorem lev_one_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (G.one t))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    FactorsThrough (bcLev ι f lev) ((G.baseChange ι).one t') := by
  rw [factorsThrough_bcLev_iff, baseChangePointToBase_one]
  exact H _

theorem lev_torsion_bc (G : RelativeGroupLaw R f) (N : ℕ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt G t N P = G.one t)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → nsmulPt (G.baseChange ι) t' N P = (G.baseChange ι).one t' := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  apply toBase_injective ι t'
  rw [toBase_nsmulPt, baseChangePointToBase_one]
  exact H _ _ hP

theorem lev_stable_bc (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev (pushPt φ hφ P))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) (pushPt (bcEndo ι φ hφ) h' P) := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  rw [factorsThrough_bcLev_iff, toBase_pushPt]
  exact H _ _ hP

end Lev

theorem geometricallyConnected_baseChangeStr [GeometricallyConnected f] :
    GeometricallyConnected (baseChangeStr ι f) :=
  inferInstance

theorem abelianSchemePropertyBundle_bc (hb : AbelianSchemePropertyBundle R f) [GeometricallyConnected f]
    (G' : RelativeGroupLaw R' (baseChangeStr ι f)) :
    AbelianSchemePropertyBundle R' (baseChangeStr ι f) where
  smooth := have := hb.smooth; inferInstance
  proper := have := hb.proper; inferInstance
  connectedFibres s := (baseChangeStr ι f).isConnected_preimage_singleton s
  hasGroupLaw := ⟨G'⟩

section Comparison

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S))
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R'))
variable (hj : j' ≫ ι = j) (g : X ⟶ A) (hg : IsPullback g p f j)

def bcComparison : X ⟶ baseChangeScheme ι f :=
  pullback.lift g (p ≫ j') (by rw [Category.assoc, hj]; exact hg.w)

@[reassoc (attr := simp)]
theorem bcComparison_fst : bcComparison ι p j j' hj g hg ≫ pullback.fst f ι = g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparison_snd : bcComparison ι p j j' hj g hg ≫ pullback.snd f ι = p ≫ j' :=
  pullback.lift_snd _ _ _

theorem isPullback_bcComparison :
    IsPullback (bcComparison ι p j j' hj g hg) p (baseChangeStr ι f) j' := by
  refine IsPullback.of_right ?_ (bcComparison_snd ι p j j' hj g hg) (IsPullback.of_hasPullback f ι)
  rw [bcComparison_fst, hj]
  exact hg

theorem comp_bcComparison_eq_bcComparison_comp_bcEndo (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (actX : X ⟶ X) (hactX : actX ≫ p = p) (H : actX ≫ g = g ≫ φ) :
    actX ≫ bcComparison ι p j j' hj g hg = bcComparison ι p j j' hj g hg ≫ bcEndo ι φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcComparison_fst, bcEndo_fst, bcComparison_fst_assoc, H]
  · simp only [Category.assoc, bcComparison_snd, bcEndo_snd]
    rw [← Category.assoc, hactX]

theorem mul_coe_comp_bcComparison (GX : RelativeGroupLaw S p) (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p),
      (GX.mul t P Q).1 ≫ g =
        (G.mul (t ≫ j) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p) :
    (GX.mul t P Q).1 ≫ bcComparison ι p j j' hj g hg =
      ((G.baseChange ι).mul (t ≫ j')
        ⟨P.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcComparison_fst, H, baseChange_mul, baseChangePointOfBase_coe, pullback.lift_fst]
    apply mul_coe_congr G
    · rw [Category.assoc, hj]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
  · have e1 : ∀ x : SchemeHomOver (t ≫ j') (baseChangeStr ι f), x.1 ≫ pullback.snd f ι = t ≫ j' :=
      fun x => x.2
    rw [e1]
    simp only [Category.assoc, bcComparison_snd]
    rw [← Category.assoc, (GX.mul t P Q).2]

section Sub

variable {C : Scheme.{u}} (lev : C ⟶ A) {XC : Scheme.{u}} (pC : XC ⟶ X) (gC : XC ⟶ C)
variable (hgC : IsPullback gC pC lev g)

def bcComparisonSub : XC ⟶ bcLevScheme ι f lev :=
  pullback.lift gC (pC ≫ p ≫ j') (by
    rw [← Category.assoc gC, hgC.w, Category.assoc, hg.w, Category.assoc, Category.assoc, hj])

@[reassoc (attr := simp)]
theorem bcComparisonSub_fst : bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.fst (lev ≫ f) ι = gC :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparisonSub_snd :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.snd (lev ≫ f) ι = pC ≫ p ≫ j' :=
  pullback.lift_snd _ _ _

theorem bcComparisonSub_bcLev :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ bcLev ι f lev = pC ≫ bcComparison ι p j j' hj g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcLev_fst, bcComparisonSub_fst_assoc, bcComparison_fst]
    exact hgC.w
  · simp only [Category.assoc, bcLev_snd, bcComparisonSub_snd, bcComparison_snd]

theorem isPullback_bcComparisonSub :
    IsPullback (bcComparisonSub ι p j j' hj g hg lev pC gC hgC) pC (bcLev ι f lev)
      (bcComparison ι p j j' hj g hg) := by
  refine IsPullback.of_right ?_ (bcComparisonSub_bcLev ι p j j' hj g hg lev pC gC hgC) (isPullback_fst_bcLev ι f lev)
  rw [bcComparisonSub_fst, bcComparison_fst]
  exact hgC

end Sub

end Comparison

end NoethBC20

namespace FGStages20

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

abbrev G (i : Idx B) : Type := ↥i.1

def φ (i j : Idx B) (h : i ≤ j) : G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

def g (i : Idx B) : G B i →+* A := (i.1).val.toRingHom

@[scoped simp] theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
@[scoped simp] theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.FGStages20.sup (i j : Idx B) : Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

p2m_export "FGStages20" "sup"
scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i)) where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m}, by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

end FGStages20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20"

namespace SPKit20

open NoethBC20

section

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem isIso_bcEndo (φ : A ⟶ A) (hφ : φ ≫ f = f) [IsIso φ] : IsIso (bcEndo ι φ hφ) := by
  have hφ' : inv φ ≫ f = f := by rw [← cancel_epi φ, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, hφ]
  refine ⟨⟨bcEndo ι (inv φ) hφ', ?_, ?_⟩⟩
  · rw [← bcEndo_eq_comp ι (IsIso.hom_inv_id φ).symm (Category.id_comp f) hφ hφ']
    exact bcEndo_eq_id ι rfl _
  · rw [← bcEndo_eq_comp ι (IsIso.inv_hom_id φ).symm (Category.id_comp f) hφ' hφ]
    exact bcEndo_eq_id ι rfl _

def bcOver (σ : SchemeHomOver f f) : SchemeHomOver (baseChangeStr ι f) (baseChangeStr ι f) :=
  ⟨bcEndo ι σ.1 σ.2, bcEndo_over ι σ.1 σ.2⟩

@[scoped simp] theorem bcOver_coe (σ : SchemeHomOver f f) : (bcOver ι σ).1 = bcEndo ι σ.1 σ.2 := rfl

theorem schemeHomOverComp_bcOver_mul (G : RelativeGroupLaw R f) (σ : SchemeHomOver f f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (G.mul t x y) σ =
        G.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t (baseChangeStr ι f)) :
    NeronModelInfra.schemeHomOverComp ((G.baseChange ι).mul t x y) (bcOver ι σ) =
      (G.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x (bcOver ι σ))
        (NeronModelInfra.schemeHomOverComp y (bcOver ι σ)) :=
  pushPt_bcEndo_mul ι σ.1 σ.2 G H (bcEndo_over ι σ.1 σ.2) t x y

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20"

theorem nonempty_pullback_iso {X P P' : Scheme.{u}} (e : X ≅ P) (cX : P ⟶ P') (gA : X ⟶ P')
    (hgA : gA = e.hom ≫ cX) (M' : P'.Modules) (N : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback cX).obj M' ≅ (Scheme.Modules.pullback e.inv).obj N)) :
    Nonempty ((Scheme.Modules.pullback gA).obj M' ≅ N) := by
  obtain ⟨e₁⟩ := h
  exact ⟨(Scheme.Modules.pullbackCongr hgA).app M' ≪≫ ((Scheme.Modules.pullbackComp e.hom cX).app M').symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso e₁ ≪≫ (Scheme.Modules.pullbackComp e.hom e.inv).app N ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app N ≪≫ (Scheme.Modules.pullbackId X).app N⟩

end SPKit20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.SPKit20"

namespace SPKit20

open NoethBC20

section PolLocal

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

theorem pol_local_bc (M : A.Modules) (σ : SchemeHomOver f f)
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M))
    (s' : ↥(Spec (CommRingCat.of R'))) :
    ∃ U' : (Spec (CommRingCat.of R')).Opens, s' ∈ U' ∧
      Nonempty ((Scheme.Modules.pullback ((baseChangeStr ι f) ⁻¹ᵁ U').ι).obj
          ((Scheme.Modules.pullback (bcOver ι σ).1).obj ((Scheme.Modules.pullback (pullback.fst f ι)).obj M)) ≅
        (Scheme.Modules.pullback ((baseChangeStr ι f) ⁻¹ᵁ U').ι).obj
          ((Scheme.Modules.pullback (pullback.fst f ι)).obj M)) := by
  obtain ⟨U, hsU, ⟨e⟩⟩ := hpol (ι.base s')
  refine ⟨ι ⁻¹ᵁ U, hsU, ⟨?_⟩⟩

  set V : (pullback f ι).Opens := (baseChangeStr ι f) ⁻¹ᵁ (ι ⁻¹ᵁ U) with hV
  have hrange : Set.range (V.ι ≫ pullback.fst f ι).base ⊆ Set.range (f ⁻¹ᵁ U).ι.base := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hv : V.ι.base v ∈ V := by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨v, rfl⟩
    change (pullback.snd f ι ≫ ι).base (V.ι.base v) ∈ U at hv
    rw [← pullback.condition] at hv
    exact hv
  set ρ' : (V : Scheme.{u}) ⟶ (f ⁻¹ᵁ U : Scheme.{u}) := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (V.ι ≫ pullback.fst f ι) hrange
    with hρ'
  have fac : ρ' ≫ (f ⁻¹ᵁ U).ι = V.ι ≫ pullback.fst f ι := IsOpenImmersion.lift_fac _ _ _
  have fac2 : V.ι ≫ (bcOver ι σ).1 ≫ pullback.fst f ι = ρ' ≫ (f ⁻¹ᵁ U).ι ≫ σ.1 := by
    rw [bcOver_coe, bcEndo_fst, ← Category.assoc, ← fac, Category.assoc]

  have e1 : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback (pullback.fst f ι)).obj M) ≅
      (Scheme.Modules.pullback ρ').obj ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M) :=
    (Scheme.Modules.pullbackComp V.ι (pullback.fst f ι)).app M ≪≫
      (Scheme.Modules.pullbackCongr fac.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp ρ' (f ⁻¹ᵁ U).ι).app M).symm

  have e2 : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback (bcOver ι σ).1).obj
        ((Scheme.Modules.pullback (pullback.fst f ι)).obj M)) ≅
      (Scheme.Modules.pullback ρ').obj ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback σ.1).obj M)) :=
    (Scheme.Modules.pullback V.ι).mapIso ((Scheme.Modules.pullbackComp (bcOver ι σ).1 (pullback.fst f ι)).app M) ≪≫
      (Scheme.Modules.pullbackComp V.ι ((bcOver ι σ).1 ≫ pullback.fst f ι)).app M ≪≫
      (Scheme.Modules.pullbackCongr fac2).app M ≪≫
      ((Scheme.Modules.pullbackComp ρ' ((f ⁻¹ᵁ U).ι ≫ σ.1)).app M).symm ≪≫
      (Scheme.Modules.pullback ρ').mapIso (((Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι σ.1).app M).symm)
  exact e2 ≪≫ (Scheme.Modules.pullback ρ').mapIso e ≪≫ e1.symm

end PolLocal
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.SPKit20"

section Package

variable {R : Type} [CommRing R] {R' : Type} [CommRing R'] {S : Type} [CommRing S]
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R'))
variable (hj : j' ≫ ι = j)
variable {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R)} (L₀ : RelativeGroupLaw R f₀)
variable {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of S)} (LX : RelativeGroupLaw S p)
  (σX : SchemeHomOver p p) (pol : X.Modules)

theorem package_bc (hb : AbelianSchemePropertyBundle R f₀) (hgc : GeometricallyConnected f₀)
    (M₀ : A₀.Modules) (hM : Scheme.Modules.IsInvertible M₀)
    (σ₀ : SchemeHomOver f₀ f₀) (hσiso : IsIso σ₀.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f₀),
      NeronModelInfra.schemeHomOverComp (L₀.mul t x y) σ₀ =
        L₀.mul t (NeronModelInfra.schemeHomOverComp x σ₀) (NeronModelInfra.schemeHomOverComp y σ₀))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ₀.1).obj M₀) ≅
        (Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj M₀))
    (gA : X ⟶ A₀) (hg : IsPullback gA p f₀ j)
    (hmulc : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t p),
      (LX.mul t x y).1 ≫ gA =
        (L₀.mul (t ≫ j) ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hpoliso : Nonempty ((Scheme.Modules.pullback gA).obj M₀ ≅ pol))
    (hσc : σX.1 ≫ gA = gA ≫ σ₀.1) :
    ∃ (_ : AbelianSchemePropertyBundle R' (baseChangeStr ι f₀))
      (_ : GeometricallyConnected (baseChangeStr ι f₀))
      (_ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (pullback.fst f₀ ι)).obj M₀))
      (_ : IsIso (bcOver ι σ₀).1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t (baseChangeStr ι f₀)),
        NeronModelInfra.schemeHomOverComp ((L₀.baseChange ι).mul t x y) (bcOver ι σ₀) =
          (L₀.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x (bcOver ι σ₀))
            (NeronModelInfra.schemeHomOverComp y (bcOver ι σ₀)))
      (_ : ∀ s : ↥(Spec (CommRingCat.of R')), ∃ U : (Spec (CommRingCat.of R')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback ((baseChangeStr ι f₀) ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback (bcOver ι σ₀).1).obj ((Scheme.Modules.pullback (pullback.fst f₀ ι)).obj M₀)) ≅
          (Scheme.Modules.pullback ((baseChangeStr ι f₀) ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback (pullback.fst f₀ ι)).obj M₀)))
      (hg' : IsPullback (bcComparison ι p j j' hj gA hg) p (baseChangeStr ι f₀) j'),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t p),
        (LX.mul t x y).1 ≫ bcComparison ι p j j' hj gA hg =
          ((L₀.baseChange ι).mul (t ≫ j')
            ⟨x.1 ≫ bcComparison ι p j j' hj gA hg, by rw [Category.assoc, hg'.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ bcComparison ι p j j' hj gA hg, by rw [Category.assoc, hg'.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback (bcComparison ι p j j' hj gA hg)).obj
          ((Scheme.Modules.pullback (pullback.fst f₀ ι)).obj M₀) ≅ pol) ∧
      σX.1 ≫ bcComparison ι p j j' hj gA hg = bcComparison ι p j j' hj gA hg ≫ (bcOver ι σ₀).1 := by
  haveI := hgc
  haveI := hσiso
  obtain ⟨epol⟩ := hpoliso
  refine ⟨abelianSchemePropertyBundle_bc ι hb (L₀.baseChange ι), geometricallyConnected_baseChangeStr ι,
    hM.pullback _, isIso_bcEndo ι σ₀.1 σ₀.2, fun t x y => schemeHomOverComp_bcOver_mul ι L₀ σ₀ hσ t x y,
    pol_local_bc ι f₀ M₀ σ₀ hpol, isPullback_bcComparison ι p j j' hj gA hg,
    fun t x y => mul_coe_comp_bcComparison ι p j j' hj gA hg LX L₀ hmulc t x y, ⟨?_⟩,
    comp_bcComparison_eq_bcComparison_comp_bcEndo ι p j j' hj gA hg σ₀.1 σ₀.2 σX.1 σX.2 hσc⟩
  exact (Scheme.Modules.pullbackComp (bcComparison ι p j j' hj gA hg) (pullback.fst f₀ ι)).app M₀ ≪≫
    (Scheme.Modules.pullbackCongr (bcComparison_fst ι p j j' hj gA hg)).app M₀ ≪≫ epol

end Package
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.SPKit20"

end SPKit20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.SPKit20"

namespace SpreadTop20

open NoethBC20 SPKit20

theorem specMap_val_comp' (L : Type) [CommRing L] (T : Subalgebra ℤ L) (T' : Subalgebra ↥T L) :
    Spec.map (CommRingCat.ofHom T'.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')) =
      Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specMap_val_comp_inclusion (L : Type) [CommRing L] (R T : Subalgebra ℤ L) (h : R ≤ T) :
    Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) =
      Spec.map (CommRingCat.ofHom R.val.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem fg_restrictScalars' (L : Type) [CommRing L] (T : Subalgebra ℤ L) (T' : Subalgebra ↥T L) (hT : T.FG) (hT' : T'.FG) :
    (T'.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
  have i2 : Algebra.FiniteType ↥T ↥T' := (Subalgebra.fg_iff_finiteType _).1 hT'
  have i3 : Algebra.FiniteType ℤ ↥T' := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T'.restrictScalars ℤ)).2 i3

theorem qc_qs_loft_of_comp_eq {W V B : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ B) (w : W ⟶ B) (hw : m ≫ v = w)
    [IsProper w] [IsSeparated v] : QuasiCompact m ∧ QuasiSeparated m ∧ LocallyOfFiniteType m := by
  haveI : IsProper (m ≫ v) := by rw [hw]; infer_instance
  haveI : QuasiCompact (m ≫ v) := inferInstance
  haveI : QuasiSeparated (m ≫ v) := inferInstance
  haveI : LocallyOfFiniteType (m ≫ v) := inferInstance
  exact ⟨QuasiCompact.of_comp m v, QuasiSeparated.of_comp m v, locallyOfFiniteType_of_comp m v⟩

theorem isClosedImmersion_toProj_of_forall {T T' : Type} [CommRing T] [CommRing T'] [Algebra T T']
    {A : Scheme.{0}} {fT : A ⟶ Spec (CommRingCat.of T)} {N : ℕ}
    (toProj : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) T)) (htoProj : toProj ≫ ProjSpace.π T N = fT)
    (H : ∀ mT : pullback (toProj ≫ ProjSpace.π T N) (Spec.map (CommRingCat.ofHom (algebraMap T T'))) ⟶
        pullback (ProjSpace.π T N) (Spec.map (CommRingCat.ofHom (algebraMap T T'))),
      mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ toProj → mT ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mT)
    (toProj' : pullback fT (Spec.map (CommRingCat.ofHom (algebraMap T T'))) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) T'))
    (h1 : toProj' ≫ ProjSpace.map T T' N = pullback.fst _ _ ≫ toProj)
    (h2 : toProj' ≫ ProjSpace.π T' N = pullback.snd _ _) :
    IsClosedImmersion toProj' := by
  subst htoProj
  let eP := (ProjSpace.isPullback_map T T' N).isoPullback
  have hc : IsClosedImmersion (toProj' ≫ eP.hom) := by
    apply H
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, h1]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, h2]
  have e : toProj' = (toProj' ≫ eP.hom) ≫ eP.inv := by simp
  rw [e]
  infer_instance

end SpreadTop20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.SPKit20"

theorem solution
    {g d n : ℕ} {k : Type} [Field k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k)), ∃ U : (Spec (CommRingCat.of k)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ (R : Subalgebra ℤ k) (_ : R.FG)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (M₀ : A₀.Modules) (_ : Scheme.Modules.IsInvertible M₀) (_ : Scheme.Modules.ClosedImmersionBySections M₀ f₀)
      (σ₀ : SchemeHomOver f₀ f₀) (_ : IsIso σ₀.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (x y : SchemeHomOver t f₀),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) σ₀ =
          L₀.mul t (NeronModelInfra.schemeHomOverComp x σ₀) (NeronModelInfra.schemeHomOverComp y σ₀))
      (_ : ∀ s : ↥(Spec (CommRingCat.of ↥R)), ∃ U : (Spec (CommRingCat.of ↥R)).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ₀.1).obj M₀) ≅
          (Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj M₀))
      (gA : u.A ⟶ A₀) (hg : CategoryTheory.IsPullback gA u.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
        (u.L.mul t x y).1 ≫ gA =
          (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback gA).obj M₀ ≅ u.pol) ∧
      σ.1 ≫ gA = gA ≫ σ₀.1 := by
  classical
  obtain ⟨R, hR, A₀, f₀, L₀, hb, hgc, M₀, hM, σ₀, hσiso, hσ, hpol₀, gA, hg, hmulc, hpoliso, hσc, T, hRT, hT, N, 𝔓, hA⟩ :=
    AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
      u σ hσiso hσ hpol
  haveI := hgc
  haveI := hb.proper

  have hjT : Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) = Spec.map (CommRingCat.ofHom R.val.toRingHom) :=
    SpreadTop20.specMap_val_comp_inclusion k R T hRT
  obtain ⟨hbT, hgcT, hMT, hσisoT, hσT, hpolT, hgT, hmulcT, hpolisoT, hσcT⟩ :=
    SPKit20.package_bc (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)) _ _ hjT L₀ u.L σ u.pol hb hgc M₀ hM σ₀ hσiso hσ hpol₀ gA hg hmulc hpoliso hσc
  haveI := hgcT
  haveI := hbT.proper

  obtain ⟨hqc, hqs, hloft⟩ := SpreadTop20.qc_qs_loft_of_comp_eq 𝔓.toProj (ProjSpace.π ↥T N) _ 𝔓.toProj_π
  haveI := hqc
  haveI := hqs
  haveI := hloft

  obtain ⟨T', hT', -, H'⟩ :=
    AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
      (A₀ := ↥T) (A := k) 𝔓.toProj (ProjSpace.π ↥T N) hA ∅

  have hjT' : Spec.map (CommRingCat.ofHom T'.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')) = Spec.map (CommRingCat.ofHom T.val.toRingHom) :=
    SpreadTop20.specMap_val_comp' k T T'
  obtain ⟨hb', hgc', hM', hσiso', hσ', hpol', hg', hmulc', hpoliso', hσc'⟩ :=
    SPKit20.package_bc (Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T'))) _ _ hjT' (L₀.baseChange (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))) u.L σ u.pol hbT hgcT _ hMT _ hσisoT hσT hpolT
      _ hgT hmulcT hpolisoT hσcT

  obtain ⟨𝔓', -, hcomm', -⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (R := ↥T) (A := ↥T')
      (IsPullback.of_hasPullback (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))) (Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')))) 𝔓
  have hci : IsClosedImmersion 𝔓'.toProj :=
    SpreadTop20.isClosedImmersion_toProj_of_forall 𝔓.toProj 𝔓.toProj_π H' 𝔓'.toProj hcomm' 𝔓'.toProj_π
  refine ⟨T'.restrictScalars ℤ, SpreadTop20.fg_restrictScalars' k T T' hT hT',
    pullback (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))) (Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T'))), pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T'))),
    (L₀.baseChange (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))).baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T'))), hb', _, hM', ⟨N, 𝔓', hci⟩, _, hσiso', hσ', hpol', _, hg',
    hmulc', hpoliso', hσc'⟩

end
end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso (solution)
