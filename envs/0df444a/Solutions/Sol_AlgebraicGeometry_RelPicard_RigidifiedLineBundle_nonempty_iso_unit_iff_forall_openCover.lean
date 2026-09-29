-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_iff_forall_openCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c0ea5e8b-2830-534e-b9b1-91a1322b8aa3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g) (𝒰 : T.OpenCover) :
    Nonempty ((M.pullbackAlong ψ).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
      ∀ j : 𝒰.I₀, Nonempty ((M.pullbackAlong
          (⟨𝒰.f j ≫ ψ.1, by rw [Category.assoc, ψ.2]⟩ : SchemeHomOver (𝒰.f j ≫ t) g)).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) (𝒰.f j ≫ t)).L) := by
  constructor
  ·
    rintro ⟨φ⟩ j
    let φj : SchemeHomOver (𝒰.f j ≫ t) t := ⟨𝒰.f j, rfl⟩
    have hcomp : baseChangeSnd f φj ≫ baseChangeSnd f ψ =
        baseChangeSnd f (⟨𝒰.f j ≫ ψ.1, by rw [Category.assoc, ψ.2]⟩ : SchemeHomOver (𝒰.f j ≫ t) g) :=
      baseChangeSnd_comp f ψ φj
    refine ⟨(Scheme.Modules.pullbackCongr hcomp.symm).app M.L ≪≫
      ((Scheme.Modules.pullbackComp (baseChangeSnd f φj) (baseChangeSnd f ψ)).app M.L).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd f φj)).mapIso φ ≪≫
      Scheme.Modules.pullbackUnitIso (baseChangeSnd f φj)⟩
  ·
    intro hloc

    let φx : ∀ x : T, SchemeHomOver (𝒰.f (𝒰.idx x) ≫ t) t := fun x => ⟨𝒰.f (𝒰.idx x), rfl⟩
    haveI : ∀ x : T, IsOpenImmersion (φx x).1 := fun x => inferInstance
    refine AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
      R f (L.one (𝟙 (Spec (CommRingCat.of R))))
      (fun A' _ _ => hA.bijective_algebraMap_sections_pullback A') t
      (fun x : T => 𝒰.f (𝒰.idx x) ≫ t) φx (fun x => ⟨x, 𝒰.covers x⟩)
      (M.pullbackAlong ψ) (RigidifiedLineBundle.unit t) ?_
    intro x
    obtain ⟨e⟩ := hloc (𝒰.idx x)
    have hcomp : baseChangeSnd f (φx x) ≫ baseChangeSnd f ψ =
        baseChangeSnd f (⟨𝒰.f (𝒰.idx x) ≫ ψ.1, by rw [Category.assoc, ψ.2]⟩ :
          SchemeHomOver (𝒰.f (𝒰.idx x) ≫ t) g) :=
      baseChangeSnd_comp f ψ (φx x)
    refine ⟨(Scheme.Modules.pullbackComp (baseChangeSnd f (φx x)) (baseChangeSnd f ψ)).app M.L ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app M.L ≪≫ e ≪≫
      (Scheme.Modules.pullbackUnitIso (baseChangeSnd f (φx x))).symm⟩

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover (solution)
