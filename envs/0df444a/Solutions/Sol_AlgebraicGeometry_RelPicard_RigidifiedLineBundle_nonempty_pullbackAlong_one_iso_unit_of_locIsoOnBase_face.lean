-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8bbc43b0-7760-5bf5-83cc-70fad625df8f

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard"

theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _)) :
    Nonempty ((M.pullbackAlong (L.one (𝟙 (Spec (CommRingCat.of S))))).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) (𝟙 _)).L) := by
  classical

  let c := prodStr f f
  let e : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f := L.one (𝟙 (Spec (CommRingCat.of S)))
  let face : pullback f f ⟶ pullback c f :=
    pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2])

  have hone : (L.one (prodStr f f)).1 = prodStr f f ≫ e.1 := by
    have := L.one_natural (𝟙 (Spec (CommRingCat.of S))) (prodStr f f) (prodStr f f) (Category.comp_id _)
    rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]
  have hbc : baseChangeSnd c e = pullback.fst c (𝟙 _) ≫ face := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      unfold baseChangeSnd
      rw [pullback.map]
      erw [pullback.lift_fst]
      rw [Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, hone, ← Category.assoc, pullback.condition, Category.assoc]
      unfold baseChangeSnd
      erw [pullback.lift_snd]
      rfl

  have h₃' := LocIsoOnBase.pullback_of_comp_eq (g := c) (pullback.snd c (𝟙 _)) (pullback.fst c (𝟙 _)) (𝟙 _)
    pullback.condition h₃
  have eM : (Scheme.Modules.pullback (pullback.fst c (𝟙 _))).obj ((Scheme.Modules.pullback face).obj M.L) ≅
      (M.pullbackAlong e).L :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hbc.symm).app M.L
  have eU : (Scheme.Modules.pullback (pullback.fst c (𝟙 _))).obj (𝟙_ (pullback f f).Modules) ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) (𝟙 _)).L :=
    Scheme.Modules.pullbackTensorUnitObjIso _
  have equivB := LocIsoOnBase.equivalence (pullback.snd c (𝟙 (Spec (CommRingCat.of S))))
  have hloc : LocIsoOnBase (pullback.snd c (𝟙 _)) (M.pullbackAlong e).L
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) (𝟙 _)).L :=
    equivB.trans (equivB.trans (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso eM.symm⟩⟩) h₃')
      (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso eU⟩⟩)

  have hP : AbelianSchemePropertyBundle S c := hA.prodStr_commRing hA
  have hB : AbelianSchemePropertyBundle S (pullback.snd c (𝟙 (Spec (CommRingCat.of S)))) :=
    hP.of_isPullback (IsPullback.of_hasPullback c (𝟙 _))
  haveI : IsProper (pullback.snd c (𝟙 (Spec (CommRingCat.of S)))) := hB.proper
  have hH0 := hB.bijective_algebraMap_sections_pullback
  exact nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
    (pullback.snd c (𝟙 _)) hH0 (rigSection c (𝟙 _) ((L.prod L).one (𝟙 _))) (pullback.lift_snd _ _ _)
    _ _ (M.pullbackAlong e).isInvertible (RigidifiedLineBundle.unit _).isInvertible hloc
    (M.pullbackAlong e).rigidified.some (RigidifiedLineBundle.unit (𝟙 _)).rigidified.some

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face (solution)
