-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/561864a3-5fad-504d-9ced-7a1c241f27d6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

namespace K6H8

noncomputable def isoOfPullbackIso' {P Q : Scheme.{u}} (φ : Q ⟶ P) [IsIso φ] {A B : P.Modules}
    (i : (Scheme.Modules.pullback φ).obj A ≅ (Scheme.Modules.pullback φ).obj B) : A ≅ B :=
  ((Scheme.Modules.pullbackId P).app A).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ).symm).app A ≪≫
    ((Scheme.Modules.pullbackComp (inv φ) φ).app A).symm ≪≫
    (Scheme.Modules.pullback (inv φ)).mapIso i ≪≫
    (Scheme.Modules.pullbackComp (inv φ) φ).app B ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app B ≪≫
    (Scheme.Modules.pullbackId P).app B

theorem nonempty_rigidify_iso_self' {k : Type u} [Field k] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of k) ⟶ P) (q : P ⟶ Spec (CommRingCat.of k)) (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨i⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible σ q L hL k (𝟙 _)
  exact ⟨isoOfPullbackIso' (pullback.fst q (𝟙 _)) i⟩

end K6H8

open K6H8 in

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR cX ε k
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    {C₁ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (i₁ : SchemeHomOver c₁ (baseChange R cX k))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)

    {B : Type u} [CommRing B] (ρ : R →+* B) (πk : B →+* k) (hAlgk : algebraMap R k = πk.comp ρ)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hya : y.1 ≫ pullback.fst D.toBase (specMap R k) = Spec.map (CommRingCat.ofHom πk) ≫ a.1)
    (N : (pullback cX (Spec.map (CommRingCat.ofHom ρ))).Modules) (hN : Scheme.Modules.IsInvertible N)
    (isoA : (hrep.poincare.pullbackAlong a).L ≅
      Scheme.Modules.rigidify (rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε) (pullback.snd cX (Spec.map (CommRingCat.ofHom ρ))) N) :

    letI ψ : SchemeHomOver (𝟙 _ ≫ specMap R k) (Spec.map (CommRingCat.ofHom ρ)) :=
      ⟨Spec.map (CommRingCat.ofHom πk), by
        rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]⟩
    Nonempty ((hrep₁.poincare.pullbackAlong
        (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) y)).L ≅
      (Scheme.Modules.pullback
        (curveChange i₁.1 i₁.2 (𝟙 _) ≫ (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj N) := by
  classical

  obtain ⟨e1⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
    i₁.1 i₁.2 hε₁ hreps hrep₁ (𝟙 _) y
  have e1' : (hrep₁.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) y)).L ≅
      Scheme.Modules.rigidify (rigSection c₁ (𝟙 _) ε₁) (pullback.snd c₁ (𝟙 _))
        ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong y).L) := e1

  obtain ⟨e2⟩ := nonempty_rigidify_iso_self' (rigSection c₁ (𝟙 _) ε₁) (pullback.snd c₁ (𝟙 _)) _
    ((hreps.poincare.pullbackAlong y).isInvertible.pullback (curveChange i₁.1 i₁.2 (𝟙 _)))

  let ā : SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase := ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩
  let ψ : SchemeHomOver (𝟙 _ ≫ specMap R k) (Spec.map (CommRingCat.ofHom ρ)) :=
    ⟨Spec.map (CommRingCat.ofHom πk), by
      rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]⟩
  have hcomp : baseChangeSnd (baseChange R cX k) y ≫ (BaseChange.κ cX k (D.baseChange k).toBase).hom ≫ baseChangeSnd cX ā =
      ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) ≫ baseChangeSnd cX a := by
    rw [← Category.assoc, BaseChange.baseChangeSnd_κ_hom, Category.assoc, Category.assoc, baseChangeSnd_comp, baseChangeSnd_comp]
    congr 2
    apply Subtype.ext
    show y.1 ≫ pullback.fst D.toBase (specMap R k) = Spec.map (CommRingCat.ofHom πk) ≫ a.1
    exact hya
  have e3 : (hreps.poincare.pullbackAlong y).L ≅
      (Scheme.Modules.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj (hrep.poincare.pullbackAlong a).L :=
    (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX k) y)).mapIso hPk.some ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX k) y)).mapIso
        ((Scheme.Modules.pullbackComp (BaseChange.κ cX k (D.baseChange k).toBase).hom (baseChangeSnd cX ā)).app hrep.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hrep.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app hrep.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app hrep.poincare.L).symm

  have hq : ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) ≫ pullback.snd cX (Spec.map (CommRingCat.ofHom ρ)) =
      pullback.snd (baseChange R cX k) (𝟙 _) ≫ Spec.map (CommRingCat.ofHom πk) := by
    rw [Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  have hσ : rigSection (baseChange R cX k) (𝟙 _) (sectionBaseChange k ε) ≫ ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) =
      Spec.map (CommRingCat.ofHom πk) ≫ rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε := by
    rw [← Category.assoc, BaseChange.rigSection_κ_hom, rigSection_baseChangeSnd]
  obtain ⟨e4⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    (Spec.map (CommRingCat.ofHom πk)) ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) hσ hq hN
  obtain ⟨e5⟩ := nonempty_rigidify_iso_self' (rigSection (baseChange R cX k) (𝟙 _) (sectionBaseChange k ε))
    (pullback.snd (baseChange R cX k) (𝟙 _)) _ (hN.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ))
  have e6 : (hreps.poincare.pullbackAlong y).L ≅
      (Scheme.Modules.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj N :=
    e3 ≪≫ (Scheme.Modules.pullback _).mapIso isoA ≪≫ e4 ≪≫ e5

  exact ⟨e1' ≪≫ e2 ≪≫ (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).mapIso e6 ≪≫
    (Scheme.Modules.pullbackComp _ _).app N⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify (solution)
