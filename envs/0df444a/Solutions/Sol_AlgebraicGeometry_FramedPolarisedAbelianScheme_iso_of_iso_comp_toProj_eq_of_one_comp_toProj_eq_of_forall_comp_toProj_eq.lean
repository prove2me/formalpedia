-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0fca85a7-804e-57ca-8f2d-89c5f154f5e4

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_iso_of_toProj_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

namespace K1Sol

universe u

def castBase {R : Type u} [CommRing R] {X : Scheme.{u}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) : M.ProjPresentation f' N := h ▸ 𝔓

theorem castBase_toProj {R : Type u} [CommRing R] {X : Scheme.{u}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) : (castBase h 𝔓).toProj = 𝔓.toProj := by
  subst h; rfl

end K1Sol

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S)
    (e₀ : X.A ≅ X'.A) (he₀f : e₀.hom ≫ X'.f = X.f) (he₀ι : e₀.hom ≫ X'.frame.toProj = X.frame.toProj)
    (hone : (X.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ X.frame.toProj =
      (X'.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ X'.frame.toProj)
    (hP : ∀ i, (X.P i).1 ≫ X.frame.toProj = (X'.P i).1 ≫ X'.frame.toProj) :
    FramedPolarisedAbelianScheme.Iso X X' := by
  haveI : IsClosedImmersion X'.frame.toProj := X'.frame_isClosedImmersion
  haveI : IsProper X'.f := X'.bundle.proper

  have hone' : (X.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ e₀.hom = (X'.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    rw [← cancel_mono X'.frame.toProj, Category.assoc, he₀ι, hone]
  have hP' : ∀ i, (X.P i).1 ≫ e₀.hom = (X'.P i).1 := fun i => by
    rw [← cancel_mono X'.frame.toProj, Category.assoc, he₀ι, hP i]

  obtain ⟨𝔔, -, h𝔔⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
    e₀.hom X'.frame
  have hiso : Nonempty ((Scheme.Modules.pullback e₀.hom).obj X'.pol ≅ X.pol) :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.nonempty_iso_of_toProj_eq (K1Sol.castBase he₀f 𝔔) X.frame
      (by rw [K1Sol.castBase_toProj, h𝔔, he₀ι])
  refine ⟨e₀, he₀f, he₀ι, ?_, hP', fun s => ⟨⊤, trivial, ?_⟩⟩
  · intro T t x y
    exact GoodReductionJacobian.AbelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one
      X.bundle X.L X'.L e₀.hom he₀f hone' t x y
  · obtain ⟨e⟩ := hiso
    exact ⟨(Scheme.Modules.pullback (X.f ⁻¹ᵁ ⊤).ι).mapIso e⟩

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq (solution)
