-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.eq_zero_of_forall_baseScalar_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8bc9e870-df14-55b1-a9d7-c9e92983a813

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation TopologicalSpace Opposite"

open scoped BigOperators

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.pullback Spec Spec.map Scheme Spec.preimage Scheme.Modules Scheme.Modules.map_smul PolarisedAbelianScheme Scheme.Modules.ProjPresentation Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq"
namespace PolarisedAbelianScheme
p2m_export "AlgebraicGeometry.PolarisedAbelianScheme" "IsPullback pol_veryAmple bundle f pol"
namespace FaithfulSections
p2m_open "AlgebraicGeometry.PolarisedAbelianScheme AlgebraicGeometry"

variable {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

theorem main (a : R)
    (h : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t a • s = 0) : a = 0 := by
  obtain ⟨N, 𝔓, -⟩ := u.pol_veryAmple
  obtain ⟨𝔓', -, -⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq (pullback.fst u.f t) 𝔓
  have key : ∀ x : ↥(pullback u.f t), ∃ U : (pullback u.f t).Opens, x ∈ U ∧
      (pullback u.f t).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (baseScalar u.f t a) = 0 := by
    intro x
    obtain ⟨i, U, hxU, hfr⟩ := 𝔓'.exists_mem_isFrameOn x
    refine ⟨U, hxU, ?_⟩
    apply (hfr.smul_eq_zero_iff le_top le_rfl _).1
    rw [← Scheme.Modules.map_smul, h (𝔓'.σ i), map_zero]
  choose U hxU hU using key
  have hcover : (⊤ : (pullback u.f t).Opens) ≤ ⨆ x, U x := fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  have hv : baseScalar u.f t a = 0 :=
    (pullback u.f t).sheaf.eq_of_locally_eq' U ⊤ (fun x => homOfLE le_top) hcover (baseScalar u.f t a) 0
      (fun x => by rw [map_zero]; exact hU x)
  have hP : CategoryTheory.IsPullback (pullback.fst u.f t) (pullback.snd u.f t) u.f
      (Spec.map (CommRingCat.ofHom (Spec.preimage t).hom)) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact CategoryTheory.IsPullback.of_hasPullback u.f t
  have bij := u.bundle.bijective_specIso_inv_comp_appTop_of_isPullback (Spec.preimage t).hom
    (pullback.snd u.f t) (pullback.fst u.f t) hP
  apply bij.1
  change baseScalar u.f t a = baseScalar u.f t 0
  rw [hv]
  change (0 : Γ(pullback u.f t, ⊤)) = baseScalarHom u.f t 0
  rw [map_zero]

end AlgebraicGeometry.PolarisedAbelianScheme.FaithfulSections

theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (a : R)
    (h : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t a • s = 0) :
    a = 0 :=
  AlgebraicGeometry.PolarisedAbelianScheme.FaithfulSections.main u t a h

end

end S_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero (solution)
