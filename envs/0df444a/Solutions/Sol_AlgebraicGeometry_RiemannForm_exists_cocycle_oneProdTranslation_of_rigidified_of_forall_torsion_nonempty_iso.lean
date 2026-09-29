-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8d2ba890-5163-539f-99be-9bca332f56a0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

namespace RigCoh

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma pullbackComp_inv_app_pullbackUnitIso :
    (Scheme.Modules.pullbackComp f g).inv.app _ ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫ (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom f g).symm
  calc (Scheme.Modules.pullbackComp f g).inv.app _ ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫ (Scheme.Modules.pullbackUnitIso f).hom
      = (Scheme.Modules.pullbackComp f g).inv.app _ ≫ ((Scheme.Modules.pullbackComp f g).hom.app _ ≫
          (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom) := by congr 1
    _ = (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom := by erw [Iso.inv_hom_id_app_assoc]

section coh

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma pullbackCongr_hom_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).hom.app N = eqToHom (by rw [H]) := by
  subst H; simp [pullbackCongr]

lemma pullbackCongr_inv_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).inv.app N = eqToHom (by rw [H]) := by
  subst H; simp [pullbackCongr]

lemma assoc_app {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj N) ≫ (pullbackComp (f ≫ g) h).hom.app N =
    (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) := by
  have := NatTrans.congr_app (pseudofunctor_associativity f g h) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, eqToHom_app] at this
  try erw [Category.id_comp] at this
  exact (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app N)).1 this

end coh

section coh2

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma pullbackCongr_refl {q : T ⟶ A'} : pullbackCongr (rfl : q = q) = Iso.refl _ := rfl

lemma congr_comp {W : Scheme.{u}} {q q' : T ⟶ W} (H : q = q') (ι : W ⟶ A') (N : A'.Modules) :
    (pullbackCongr H).hom.app ((Scheme.Modules.pullback ι).obj N) =
      (pullbackComp q ι).hom.app N ≫ eqToHom (by rw [H]) ≫ (pullbackComp q' ι).inv.app N := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, eqToHom_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact ((pullbackComp q ι).hom_inv_id_app N).symm

lemma map_congr (lam : T' ⟶ T) {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (Scheme.Modules.pullback lam).map ((pullbackCongr H).hom.app N) =
      (pullbackComp lam q).hom.app N ≫ eqToHom (by rw [H]) ≫ (pullbackComp lam q').inv.app N := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, eqToHom_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_id]
  first
    | exact ((pullbackComp lam q).hom_inv_id_app N).symm
    | (erw [CategoryTheory.Functor.map_id]; exact ((pullbackComp lam q).hom_inv_id_app N).symm)

lemma assoc_app' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app N) =
    (pullbackComp (f ≫ g) h).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp f (g ≫ h)).inv.app N := by
  have h1 := assoc_app f g h N

  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : β.symm ≪≫ α = γ ≪≫ η.symm ≪≫ δ.symm := by
    have h2' : β ≪≫ γ = α ≪≫ δ ≪≫ η := by
      rw [← h2]; simp
    calc β.symm ≪≫ α = β.symm ≪≫ α ≪≫ (δ ≪≫ η) ≪≫ (δ ≪≫ η).symm := by simp
      _ = β.symm ≪≫ (α ≪≫ δ ≪≫ η) ≪≫ (η.symm ≪≫ δ.symm) := by simp
      _ = β.symm ≪≫ (β ≪≫ γ) ≪≫ (η.symm ≪≫ δ.symm) := by rw [h2']
      _ = γ ≪≫ η.symm ≪≫ δ.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

end coh2

section coh3

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma assoc_app'' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) =
      (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (f ≫ g) h).inv.app N ≫
        (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : α.symm = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by
    calc α.symm = (α.symm ≪≫ β ≪≫ γ) ≪≫ (γ.symm ≪≫ β.symm) := by simp
      _ = (δ ≪≫ η) ≪≫ (γ.symm ≪≫ β.symm) := by rw [h2]
      _ = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

end coh3

section rules

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma mapIso_pullbackComp_app {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).mapIso (X := (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N))
      (Y := (Scheme.Modules.pullback (g ≫ h)).obj N) ((pullbackComp g h).app N) =
      (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N) ≪≫ (pullbackComp (f ≫ g) h).app N ≪≫
        eqToIso (by rw [Category.assoc]) ≪≫ ((pullbackComp f (g ≫ h)).app N).symm := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : α = β ≪≫ γ ≪≫ η.symm ≪≫ δ.symm := by
    calc α = α ≪≫ (δ ≪≫ η) ≪≫ (η.symm ≪≫ δ.symm) := by simp
      _ = α ≪≫ (α.symm ≪≫ β ≪≫ γ) ≪≫ (η.symm ≪≫ δ.symm) := by rw [h2]
      _ = β ≪≫ γ ≪≫ η.symm ≪≫ δ.symm := by simp
  have h5 : η.symm = eqToIso (by rw [Category.assoc]) := rfl
  rw [h5] at h3
  exact h3

lemma congr_app_comp {W : Scheme.{u}} {q q' : T ⟶ W} (H : q = q') (ι : W ⟶ A') (N : A'.Modules) :
    (pullbackCongr H).app ((Scheme.Modules.pullback ι).obj N) =
      (pullbackComp q ι).app N ≪≫ eqToIso (by rw [H]) ≪≫ ((pullbackComp q' ι).app N).symm := by
  subst H
  ext : 1
  simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
    Iso.symm_hom, Iso.app_inv, Category.id_comp]
  exact ((pullbackComp q ι).hom_inv_id_app N).symm

lemma mapIso_congr_app (lam : T' ⟶ T) {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (Scheme.Modules.pullback lam).mapIso ((pullbackCongr H).app N) =
      (pullbackComp lam q).app N ≪≫ eqToIso (by rw [H]) ≪≫ ((pullbackComp lam q').app N).symm := by
  subst H
  ext : 1
  simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
    Iso.symm_hom, Iso.app_inv, Category.id_comp, Functor.mapIso_hom]
  first
    | exact ((pullbackComp lam q).hom_inv_id_app N).symm
    | (erw [CategoryTheory.Functor.map_id]; exact ((pullbackComp lam q).hom_inv_id_app N).symm)

lemma congr_app_eqToIso {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).app N = eqToIso (by rw [H]) := by
  subst H; ext : 1; simp [pullbackCongr]

lemma mapIso_mapIso (lam : T' ⟶ T) (p : T ⟶ A') {N N' : A'.Modules} (τ : N ≅ N') :
    (Scheme.Modules.pullback lam).mapIso ((Scheme.Modules.pullback p).mapIso τ) =
      (pullbackComp lam p).app N ≪≫ (Scheme.Modules.pullback (lam ≫ p)).mapIso τ ≪≫ ((pullbackComp lam p).app N').symm := by
  ext : 1
  have := (pullbackComp lam p).hom.naturality τ.hom
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [← Category.assoc, ← this]
  simp only [Functor.comp_map, Category.assoc]
  first
    | (rw [Iso.hom_inv_id_app, Category.comp_id])
    | (erw [Iso.hom_inv_id_app]; erw [Category.comp_id])

lemma mapIso_pullbackUnitIso (f : T' ⟶ T) (g : T ⟶ A') :
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g) =
      (pullbackComp f g).app _ ≪≫ pullbackUnitIso (f ≫ g) ≪≫ (pullbackUnitIso f).symm := by
  have h1 := pullbackComp_inv_app_pullbackUnitIso f g
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj (SheafOfModules.unit A'.ringCatSheaf)) ≅
      (Scheme.Modules.pullback f).obj (SheafOfModules.unit T.ringCatSheaf) :=
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj (SheafOfModules.unit A'.ringCatSheaf)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj (SheafOfModules.unit A'.ringCatSheaf) := (pullbackComp f g).app _
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj (SheafOfModules.unit A'.ringCatSheaf) ≅
      SheafOfModules.unit T'.ringCatSheaf := pullbackUnitIso (f ≫ g)
  let δ : (Scheme.Modules.pullback f).obj (SheafOfModules.unit T.ringCatSheaf) ≅ SheafOfModules.unit T'.ringCatSheaf :=
    pullbackUnitIso f
  have h2 : β.symm ≪≫ α ≪≫ δ = γ := Iso.ext h1
  have h3 : α = β ≪≫ γ ≪≫ δ.symm := by
    calc α = β ≪≫ (β.symm ≪≫ α ≪≫ δ) ≪≫ δ.symm := by simp
      _ = β ≪≫ γ ≪≫ δ.symm := by rw [h2]
  exact h3

end rules

section core

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A)
  (ε : T ⟶ Y) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
  (ε₂ : T₂ ⟶ Y₂) (j : Y₂ ⟶ Y) (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε)
  (hp₂ : ε₂ ≫ j ≫ ι = (lam ≫ p) ≫ e)

noncomputable abbrev triv {T Y : Scheme.{u}} (ε : T ⟶ Y) (ι : Y ⟶ A) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (N : A.Modules) (t : (Scheme.Modules.pullback e).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Scheme.Modules.pullback ε).obj ((Scheme.Modules.pullback ι).obj N) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  (pullbackComp ε ι).app N ≪≫ (pullbackCongr hp).app N ≪≫ ((pullbackComp p e).app N).symm ≪≫
    (Scheme.Modules.pullback p).mapIso t ≪≫ pullbackUnitIso p

include hlam in
lemma core (N : A.Modules) (t : (Scheme.Modules.pullback e).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    ((Scheme.Modules.pullback ε₂).mapIso ((pullbackComp j ι).app N)).symm ≪≫
      ((pullbackComp ε₂ j).app ((Scheme.Modules.pullback ι).obj N) ≪≫
        (pullbackCongr hlam).app ((Scheme.Modules.pullback ι).obj N) ≪≫
        ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj N)).symm) ≪≫
      (Scheme.Modules.pullback lam).mapIso (triv e ε ι p hp N t) ≪≫ pullbackUnitIso lam =
    triv e ε₂ (j ≫ ι) (lam ≫ p) hp₂ N t := by
  simp only [Functor.comp_obj, triv, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc,
    mapIso_pullbackComp_app, congr_app_comp hlam, mapIso_congr_app lam hp, congr_app_eqToIso hp₂,
    mapIso_mapIso, mapIso_pullbackUnitIso, Iso.symm_self_id, Iso.self_symm_id, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc, Iso.refl_trans, Iso.trans_refl]
  ext : 1
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans, eqToHom_trans_assoc,
    Category.assoc]

end core

section more_rules

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T A' : Scheme.{u}}

lemma mapIso_congr_nat {q q' : T ⟶ A'} (H : q = q') {N N' : A'.Modules} (ψ : N ≅ N') :
    (Scheme.Modules.pullback q).mapIso ψ =
      (pullbackCongr H).app N ≪≫ (Scheme.Modules.pullback q').mapIso ψ ≪≫ ((pullbackCongr H).app N').symm := by
  subst H
  ext : 1
  simp [pullbackCongr]

lemma congr_app_refl {q : T ⟶ A'} (N : A'.Modules) :
    (pullbackCongr (rfl : q = q)).app N = Iso.refl _ := by
  ext : 1
  simp [pullbackCongr]

end more_rules

end RigCoh

namespace RigCocycle

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso.RigCoh"

section general

variable {X B : Scheme.{u}} (rig : B ⟶ X) (𝓠 : X.Modules)
  (α₀ : (Scheme.Modules.pullback rig).obj 𝓠 ≅ SheafOfModules.unit B.ringCatSheaf)

noncomputable abbrev τ (σ : X ⟶ X) (u : B ⟶ B) (h : rig ≫ σ = u ≫ rig) :
    (Scheme.Modules.pullback rig).obj ((Scheme.Modules.pullback σ).obj 𝓠) ≅ SheafOfModules.unit B.ringCatSheaf :=
  triv rig rig σ u h 𝓠 α₀

def Normalised (σ : X ⟶ X) (u : B ⟶ B) (h : rig ≫ σ = u ≫ rig)
    (ψ : 𝓠 ≅ (Scheme.Modules.pullback σ).obj 𝓠) : Prop :=
  (Scheme.Modules.pullback rig).mapIso ψ ≪≫ τ rig 𝓠 α₀ σ u h = α₀

theorem mapIso_mapIso_eq_of_normalised (σ₁ σ₂ : X ⟶ X) (u₁ u₂ : B ⟶ B)
    (h₁ : rig ≫ σ₁ = u₁ ≫ rig) (h₂ : rig ≫ σ₂ = u₂ ≫ rig)
    (ψ₂ : 𝓠 ≅ (Scheme.Modules.pullback σ₂).obj 𝓠) (hψ₂ : Normalised rig 𝓠 α₀ σ₂ u₂ h₂ ψ₂) :
    (Scheme.Modules.pullback rig).mapIso ((Scheme.Modules.pullback σ₁).mapIso ψ₂) =
      τ rig 𝓠 α₀ σ₁ u₁ h₁ ≪≫
        (triv rig rig σ₁ u₁ h₁ ((Scheme.Modules.pullback σ₂).obj 𝓠) (τ rig 𝓠 α₀ σ₂ u₂ h₂)).symm := by
  have hφ : (Scheme.Modules.pullback rig).mapIso ψ₂ = α₀ ≪≫ (τ rig 𝓠 α₀ σ₂ u₂ h₂).symm := by
    have h' := hψ₂
    unfold Normalised at h'
    calc (Scheme.Modules.pullback rig).mapIso ψ₂
        = ((Scheme.Modules.pullback rig).mapIso ψ₂ ≪≫ τ rig 𝓠 α₀ σ₂ u₂ h₂) ≪≫ (τ rig 𝓠 α₀ σ₂ u₂ h₂).symm := by
          rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
      _ = α₀ ≪≫ (τ rig 𝓠 α₀ σ₂ u₂ h₂).symm := by rw [h']
  exact AlgebraicGeometry.Scheme.Modules.pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq
    σ₁ rig rig u₁ h₁ 𝓠 ((Scheme.Modules.pullback σ₂).obj 𝓠) α₀ (τ rig 𝓠 α₀ σ₂ u₂ h₂) ψ₂ hφ

theorem mapIso_pullbackComp_app_trans_τ (σ₁ σ₂ : X ⟶ X) (u₁ u₂ : B ⟶ B)
    (h₁ : rig ≫ σ₁ = u₁ ≫ rig) (h₂ : rig ≫ σ₂ = u₂ ≫ rig) (h₁₂ : rig ≫ (σ₁ ≫ σ₂) = (u₁ ≫ u₂) ≫ rig) :
    (Scheme.Modules.pullback rig).mapIso (X := (Scheme.Modules.pullback σ₁).obj ((Scheme.Modules.pullback σ₂).obj 𝓠))
        (Y := (Scheme.Modules.pullback (σ₁ ≫ σ₂)).obj 𝓠) ((pullbackComp σ₁ σ₂).app 𝓠) ≪≫
        τ rig 𝓠 α₀ (σ₁ ≫ σ₂) (u₁ ≫ u₂) h₁₂ =
      triv rig rig σ₁ u₁ h₁ ((Scheme.Modules.pullback σ₂).obj 𝓠) (τ rig 𝓠 α₀ σ₂ u₂ h₂) := by
  simp only [τ, triv, Functor.comp_obj, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, mapIso_pullbackComp_app, congr_app_comp h₁, mapIso_congr_app u₁ h₂, congr_app_eqToIso h₁₂,
    mapIso_mapIso, mapIso_pullbackUnitIso, Iso.symm_self_id, Iso.self_symm_id, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc, Iso.refl_trans, Iso.trans_refl]
  ext : 1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, eqToIso.hom, eqToIso.inv, eqToHom_trans,
    eqToHom_trans_assoc, Category.assoc, Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]

theorem normalised_trans (σ₁ σ₂ : X ⟶ X) (u₁ u₂ : B ⟶ B)
    (h₁ : rig ≫ σ₁ = u₁ ≫ rig) (h₂ : rig ≫ σ₂ = u₂ ≫ rig) (h₁₂ : rig ≫ (σ₁ ≫ σ₂) = (u₁ ≫ u₂) ≫ rig)
    (ψ₁ : 𝓠 ≅ (Scheme.Modules.pullback σ₁).obj 𝓠) (hψ₁ : Normalised rig 𝓠 α₀ σ₁ u₁ h₁ ψ₁)
    (ψ₂ : 𝓠 ≅ (Scheme.Modules.pullback σ₂).obj 𝓠) (hψ₂ : Normalised rig 𝓠 α₀ σ₂ u₂ h₂ ψ₂) :
    Normalised rig 𝓠 α₀ (σ₁ ≫ σ₂) (u₁ ≫ u₂) h₁₂
      (ψ₁ ≪≫ (Scheme.Modules.pullback σ₁).mapIso ψ₂ ≪≫ (pullbackComp σ₁ σ₂).app 𝓠) := by
  have h' := hψ₁
  unfold Normalised at h' ⊢
  rw [Functor.mapIso_trans, Functor.mapIso_trans, mapIso_mapIso_eq_of_normalised rig 𝓠 α₀ σ₁ σ₂ u₁ u₂ h₁ h₂ ψ₂ hψ₂]
  simp only [Iso.trans_assoc]
  rw [mapIso_pullbackComp_app_trans_τ rig 𝓠 α₀ σ₁ σ₂ u₁ u₂ h₁ h₂ h₁₂, Iso.symm_self_id, Iso.trans_refl]
  exact h'

theorem map_pullbackId_hom_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackId Z).hom.app M) =
      (pullbackComp f (𝟙 Z)).hom.app M ≫ eqToHom (by rw [Category.comp_id]; rfl) := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToHom_app,
    Category.comp_id] at h
  have h' := congrArg (fun t => (pullbackComp f (𝟙 Z)).hom.app M ≫ t) h
  simp only [Iso.hom_inv_id_app_assoc] at h'
  erw [Category.comp_id] at h'
  exact h'

@[reassoc]
theorem map_pullbackId_inv_app_comp {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackId Z).inv.app M) ≫ (pullbackComp f (𝟙 Z)).hom.app M =
      eqToHom (by rw [Category.comp_id]; rfl) := by
  have hI : (Scheme.Modules.pullback f).mapIso ((pullbackId Z).app M) =
      (pullbackComp f (𝟙 Z)).app M ≪≫ eqToIso (by rw [Category.comp_id]; rfl) := Iso.ext (map_pullbackId_hom_app f M)
  have hinv := congrArg Iso.inv hI
  simp only [Functor.mapIso_inv, Iso.trans_inv, Iso.app_inv, eqToIso.inv] at hinv
  have h2 := congrArg (fun t => t ≫ (pullbackComp f (𝟙 Z)).hom.app M) hinv
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h2
  exact h2

@[reassoc]
theorem pullbackComp_id_inv_app_comp {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) :
    (pullbackComp (𝟙 Y) f).inv.app M ≫ (pullbackId Y).hom.app ((Scheme.Modules.pullback f).obj M) =
      eqToHom (by rw [Category.id_comp]; rfl) := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app,
    Category.comp_id] at h
  exact h

@[reassoc]
theorem map_id_eq {Y : Scheme.{u}} {N N' : Y.Modules} (φ : N ⟶ N') :
    (Scheme.Modules.pullback (𝟙 Y)).map φ = (pullbackId Y).hom.app N ≫ φ ≫ (pullbackId Y).inv.app N' := by
  have nat := (pullbackId Y).hom.naturality φ
  have h := congrArg (fun t => t ≫ (pullbackId Y).inv.app N') nat
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at h
  exact h

theorem pullbackUnitIso_hom_congr {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) :
    (pullbackUnitIso f).hom = eqToHom (by rw [h]) ≫ (pullbackUnitIso g).hom := by
  subst h; simp

theorem pullbackUnitIso_id_hom (Y : Scheme.{u}) :
    (pullbackUnitIso (𝟙 Y)).hom = (pullbackId Y).hom.app (SheafOfModules.unit Y.ringCatSheaf) := by
  haveI : (Scheme.Modules.pullback (𝟙 Y)).Faithful := Functor.Faithful.of_iso (pullbackId Y).symm
  apply (Scheme.Modules.pullback (𝟙 Y)).map_injective
  have h1 := pullbackComp_inv_app_pullbackUnitIso (𝟙 Y) (𝟙 Y)
  have h1' := congrArg (fun t => (pullbackComp (𝟙 Y) (𝟙 Y)).hom.app _ ≫ t) h1
  simp only [Iso.hom_inv_id_app_assoc] at h1'

  rw [pullbackUnitIso_hom_congr (Category.comp_id (𝟙 Y)), ← Category.assoc] at h1'
  have h2 := (cancel_mono (pullbackUnitIso (𝟙 Y)).hom).1 h1'
  have h3 := map_pullbackId_hom_app (𝟙 Y) (SheafOfModules.unit Y.ringCatSheaf)
  exact h2.trans h3.symm

theorem map_comp_pullbackUnitIso_id {Y : Scheme.{u}} {N : Y.Modules} (φ : N ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback (𝟙 Y)).map φ ≫ (pullbackUnitIso (𝟙 Y)).hom = (pullbackId Y).hom.app N ≫ φ := by
  rw [pullbackUnitIso_id_hom, map_id_eq_assoc]
  erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]

theorem normalised_id (h : rig ≫ 𝟙 X = 𝟙 B ≫ rig) :
    Normalised rig 𝓠 α₀ (𝟙 X) (𝟙 B) h ((pullbackId X).app 𝓠).symm := by
  unfold Normalised
  ext : 1
  simp only [τ, triv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  erw [pullbackCongr_hom_app_eq h 𝓠]
  erw [map_comp_pullbackUnitIso_id α₀.hom]
  erw [pullbackComp_id_inv_app_comp_assoc rig 𝓠]
  erw [map_pullbackId_inv_app_comp_assoc rig 𝓠]
  erw [eqToHom_trans_assoc]
  erw [eqToHom_refl]
  erw [Category.id_comp]

theorem normalised_law0 (σ : X ⟶ X) (u : B ⟶ B) (h : rig ≫ σ = u ≫ rig) (e0 : σ = 𝟙 X) (hu : u = 𝟙 B) :
    Normalised rig 𝓠 α₀ σ u h (((pullbackId X).app 𝓠).symm ≪≫ ((pullbackCongr e0).app 𝓠).symm) := by
  subst e0 hu
  rw [congr_app_refl, Iso.refl_symm, Iso.trans_refl]
  exact normalised_id rig 𝓠 α₀ h

theorem normalised_lawAdd (σ₁ σ₂ σ₃ : X ⟶ X) (u₁ u₂ u₃ : B ⟶ B)
    (h₁ : rig ≫ σ₁ = u₁ ≫ rig) (h₂ : rig ≫ σ₂ = u₂ ≫ rig) (h₃ : rig ≫ σ₃ = u₃ ≫ rig)
    (e : σ₃ = σ₁ ≫ σ₂) (hu : u₃ = u₁ ≫ u₂)
    (ψ₁ : 𝓠 ≅ (Scheme.Modules.pullback σ₁).obj 𝓠) (hψ₁ : Normalised rig 𝓠 α₀ σ₁ u₁ h₁ ψ₁)
    (ψ₂ : 𝓠 ≅ (Scheme.Modules.pullback σ₂).obj 𝓠) (hψ₂ : Normalised rig 𝓠 α₀ σ₂ u₂ h₂ ψ₂) :
    Normalised rig 𝓠 α₀ σ₃ u₃ h₃
      (ψ₁ ≪≫ (Scheme.Modules.pullback σ₁).mapIso ψ₂ ≪≫ (pullbackComp σ₁ σ₂).app 𝓠 ≪≫
        ((pullbackCongr e).app 𝓠).symm) := by
  subst e hu
  rw [congr_app_refl, Iso.refl_symm, Iso.trans_refl]
  exact normalised_trans rig 𝓠 α₀ σ₁ σ₂ u₁ u₂ h₁ h₂ h₃ ψ₁ hψ₁ ψ₂ hψ₂

end general

end RigCocycle

namespace RigCocycle

section specific

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso.RigCoh AlgebraicGeometry.RelPicard"

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative)

noncomputable def ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
  toUnitPt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k))

noncomputable abbrev rig : A ⟶ pullback f f := rigSection f f (ε₀ f L hc)

noncomputable abbrev σQ (Q : L.AlgPoints hc k) : pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
    (by rw [Category.assoc, translation_over]; exact pullback.condition)

theorem rig_comp_σQ (Q : L.AlgPoints hc k) :
    rig f L hc ≫ σQ f L hc Q = translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) ≫ rig f L hc := by
  apply pullback.hom_ext
  · simp only [rig, rigSection, σQ, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc (translation f L _), translation_over]
  · simp only [rig, rigSection, σQ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp]

noncomputable def jA : A ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k))) :=
  pullback.lift (𝟙 A) f (by rw [Category.id_comp, specMap_algebraMap_self, Category.comp_id])

theorem rig_eq_jA_comp :
    rig f L hc = jA f ≫ (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) ≫ (pullbackSymmetry f f).hom) := by
  apply pullback.hom_ext
  · simp only [rig, rigSection, jA, sliceAt, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    rfl
  · simp only [rig, rigSection, jA, sliceAt, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

noncomputable def α₀Of (𝓠 : (pullback f f).Modules)
    (ι₀ : (Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓠) ≅ 𝟙_ _) :
    (Scheme.Modules.pullback (rig f L hc)).obj 𝓠 ≅ SheafOfModules.unit A.ringCatSheaf :=
  (pullbackCongr (rig_eq_jA_comp f L hc)).app 𝓠 ≪≫
    ((pullbackComp (jA f) (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) ≫
      (pullbackSymmetry f f).hom)).app 𝓠).symm ≪≫
    (Scheme.Modules.pullback (jA f)).mapIso
      (((pullbackComp (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))
        (pullbackSymmetry f f).hom).app 𝓠).symm ≪≫ ι₀) ≪≫
    pullbackUnitIso (jA f)

noncomputable def M₀ (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (α₀ : (Scheme.Modules.pullback (rig f L hc)).obj 𝓠 ≅ SheafOfModules.unit A.ringCatSheaf) :
    RigidifiedLineBundle f (ε₀ f L hc) f :=
  { L := 𝓠, isInvertible := h𝓠, rigidified := ⟨α₀⟩ }

noncomputable def Mσ (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (α₀ : (Scheme.Modules.pullback (rig f L hc)).obj 𝓠 ≅ SheafOfModules.unit A.ringCatSheaf)
    (σ : pullback f f ⟶ pullback f f) (u : A ⟶ A) (h : rig f L hc ≫ σ = u ≫ rig f L hc) :
    RigidifiedLineBundle f (ε₀ f L hc) f :=
  { L := (Scheme.Modules.pullback σ).obj 𝓠, isInvertible := h𝓠.pullback σ,
    rigidified := ⟨τ (rig f L hc) 𝓠 α₀ σ u h⟩ }

theorem normalised_unique (hA : AbelianSchemePropertyBundle k f) (𝓠 : (pullback f f).Modules)
    (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (α₀ : (Scheme.Modules.pullback (rig f L hc)).obj 𝓠 ≅ SheafOfModules.unit A.ringCatSheaf)
    (σ : pullback f f ⟶ pullback f f) (u : A ⟶ A) (h : rig f L hc ≫ σ = u ≫ rig f L hc)
    (φ ψ : 𝓠 ≅ (Scheme.Modules.pullback σ).obj 𝓠)
    (hφ : Normalised (rig f L hc) 𝓠 α₀ σ u h φ) (hψ : Normalised (rig f L hc) 𝓠 α₀ σ u h ψ) : φ = ψ :=
  RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq k f (ε₀ f L hc)
    (fun T _ _ => GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_algebraMap_sections_pullback hA T)
    f (M₀ f L hc 𝓠 h𝓠 α₀) (Mσ f L hc 𝓠 h𝓠 α₀ σ u h) α₀ (τ (rig f L hc) 𝓠 α₀ σ u h) φ ψ hφ hψ

theorem exists_normalised (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (α₀ : (Scheme.Modules.pullback (rig f L hc)).obj 𝓠 ≅ SheafOfModules.unit A.ringCatSheaf)
    (σ : pullback f f ⟶ pullback f f) (u : A ⟶ A) (h : rig f L hc ≫ σ = u ≫ rig f L hc)
    (hne : Nonempty (𝓠 ≅ (Scheme.Modules.pullback σ).obj 𝓠)) :
    ∃ ψ : 𝓠 ≅ (Scheme.Modules.pullback σ).obj 𝓠, Normalised (rig f L hc) 𝓠 α₀ σ u h ψ :=
  RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq k f (ε₀ f L hc) f
    (M₀ f L hc 𝓠 h𝓠 α₀) (Mσ f L hc 𝓠 h𝓠 α₀ σ u h) α₀ (τ (rig f L hc) 𝓠 α₀ σ u h) hne.some

end specific

end RigCocycle

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ)
    (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (hrig : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓠) ≅ 𝟙_ _))
    (hinv : ∀ Q : L.AlgPoints hc k, n • Q = 0 →
      Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj 𝓠 ≅ 𝓠)) :
    ∃ ψ : ∀ Q : L.AlgPoints hc k, n • Q = 0 →
        (𝓠 ≅ (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj 𝓠),
      (∀ (h0 : n • (0 : L.AlgPoints hc k) = 0)
          (e0 : (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))
          (by rw [Category.assoc, translation_over]; exact pullback.condition)) = 𝟙 (pullback f f)),
        ψ 0 h0 = ((Scheme.Modules.pullbackId (pullback f f)).app 𝓠).symm ≪≫ ((Scheme.Modules.pullbackCongr e0).app 𝓠).symm) ∧
      (∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0)
          (ePQ : (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)))
          (by rw [Category.assoc, translation_over]; exact pullback.condition)) =
            (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (by rw [Category.assoc, translation_over]; exact pullback.condition)) ≫
            (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))
              (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).app 𝓠 ≪≫
            ((Scheme.Modules.pullbackCongr ePQ).app 𝓠).symm) := by
  classical
  obtain ⟨ι₀⟩ := hrig

  let T : L.AlgPoints hc k → (A ⟶ A) := fun Q => translation f L (RelativeGroupLaw.AlgPoints.toPoint Q)
  have hT0 : T 0 = 𝟙 A := (translation_zero_and_translation_add k f L hc 0 0).1
  have hTadd : ∀ P Q : L.AlgPoints hc k, T (P + Q) = T P ≫ T Q := fun P Q =>
    (translation_zero_and_translation_add k f L hc P Q).2
  let α₀ := RigCocycle.α₀Of f L hc 𝓠 ι₀
  have hsl : ∀ Q : L.AlgPoints hc k, RigCocycle.rig f L hc ≫ RigCocycle.σQ f L hc Q = T Q ≫ RigCocycle.rig f L hc :=
    fun Q => RigCocycle.rig_comp_σQ f L hc Q

  have hex : ∀ (Q : L.AlgPoints hc k), n • Q = 0 →
      ∃ ψ : 𝓠 ≅ (Scheme.Modules.pullback (RigCocycle.σQ f L hc Q)).obj 𝓠,
        RigCocycle.Normalised (RigCocycle.rig f L hc) 𝓠 α₀ (RigCocycle.σQ f L hc Q) (T Q) (hsl Q) ψ :=
    fun Q hQ => RigCocycle.exists_normalised f L hc 𝓠 h𝓠 α₀ _ _ (hsl Q) ⟨(hinv Q hQ).some.symm⟩
  choose ψ hψ using hex
  refine ⟨ψ, ?_, ?_⟩
  · intro h0 e0
    exact RigCocycle.normalised_unique f L hc hA 𝓠 h𝓠 α₀ _ _ (hsl 0) _ _ (hψ 0 h0)
      (RigCocycle.normalised_law0 (RigCocycle.rig f L hc) 𝓠 α₀ _ _ (hsl 0) e0 hT0)
  · intro P Q hP hQ hPQ ePQ
    exact RigCocycle.normalised_unique f L hc hA 𝓠 h𝓠 α₀ _ _ (hsl (P + Q)) _ _ (hψ (P + Q) hPQ)
      (RigCocycle.normalised_lawAdd (RigCocycle.rig f L hc) 𝓠 α₀ _ _ _ _ _ _ (hsl P) (hsl Q) (hsl (P + Q))
        ePQ (hTadd P Q) (ψ P hP) (hψ P hP) (ψ Q hQ) (hψ Q hQ))

end S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso (solution)
