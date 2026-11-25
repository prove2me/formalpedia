-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
-- name    : GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:33.977175+00:00
-- url     : https://prove2.me/theorems/49e3d8bf-4950-48fe-bad2-9b44b1ee3f21
-- title:
--   Qcoh Presheaf
-- statement:
--   Definitions and structural lemmas for Qcoh Presheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohPresheaf.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackComp_inv_pullbackSection
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackSection_naturality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
section Coherence
variable {X : Scheme.{u}} (F : X.Modules)
noncomputable def compHom {Y Z : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) (c : Y ⟶ X) (h : a ≫ b = c) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj F) ⟶
      (Scheme.Modules.pullback c).obj F :=
  (Scheme.Modules.pullbackComp a b).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F
lemma compHom_assoc {Y₁ Y₂ Y₃ : Scheme.{u}} (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (c₃ : Y₃ ⟶ X)
    (c₂ : Y₂ ⟶ X) (c₁ : Y₁ ⟶ X) (h₂ : b ≫ c₃ = c₂) (h₁ : a ≫ c₂ = c₁) :
    (Scheme.Modules.pullback a).map (compHom F b c₃ c₂ h₂) ≫ compHom F a c₂ c₁ h₁ =
      (Scheme.Modules.pullbackComp a b).hom.app _ ≫
        compHom F (a ≫ b) c₃ c₁ (by rw [Category.assoc, h₂, h₁]) := by
  subst h₂ h₁
  have H := congrArg (fun φ => φ.app F) (Scheme.Modules.pseudofunctor_associativity a b c₃)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  simp only [compHom, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, eqToIso.hom, eqToHom_app]
  have H' : (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c₃).obj F) ≫
      (Scheme.Modules.pullbackComp (a ≫ b) c₃).hom.app F =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c₃).hom.app F) ≫
        (Scheme.Modules.pullbackComp a (b ≫ c₃)).hom.app F ≫ eqToHom (by simp) := by
    rw [← H]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% H']
  simp
lemma pullbackSection_id {Y : Scheme.{u}} (N : Y.Modules) (s : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackId Y).hom.app N).app ⊤ (pullbackSection (𝟙 Y) N s) = s := by
  have h := unit_conjugateEquiv Adjunction.id (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Y))
    (Scheme.Modules.pullbackId Y).hom N
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom s) h
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp,
    Scheme.Modules.pushforwardId_inv_app_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply] at h'
  exact h'.symm
lemma compHom_id {Y : Scheme.{u}} (c : Y ⟶ X) (h : 𝟙 Y ≫ c = c) :
    compHom F (𝟙 Y) c c h = (Scheme.Modules.pullbackId Y).hom.app _ := by
  have H := congrArg (fun φ => φ.app F) (Scheme.Modules.pseudofunctor_right_unitality c)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at H
  erw [Category.comp_id] at H
  have H2 : (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback c).obj F) =
      (Scheme.Modules.pullbackComp (𝟙 Y) c).hom.app F ≫ eqToHom (by simp) := by
    rw [← H, Iso.hom_inv_id_app_assoc]
  rw [H2]
  simp only [compHom, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
lemma compHom_id_section {Y : Scheme.{u}} (c : Y ⟶ X) (h : 𝟙 Y ≫ c = c)
    (s : Γ((Scheme.Modules.pullback c).obj F, ⊤)) :
    (compHom F (𝟙 Y) c c h).app ⊤ (pullbackSection (𝟙 Y) _ s) = s := by
  rw [compHom_id]
  exact pullbackSection_id _ s
lemma pullbackComp_hom_pullbackSection {W T U : Scheme.{u}} (f : W ⟶ T) (g : T ⟶ U)
    (N : U.Modules) (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app ⊤
      (pullbackSection f _ (pullbackSection g N n)) = pullbackSection (f ≫ g) N n := by
  rw [← pullbackComp_inv_pullbackSection, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app]
  rfl
end Coherence
section Presheaf
variable {X : Scheme.{u}} (F : X.Modules)
noncomputable def qcohMap {U U' : X.Etale} (g : U ⟶ U') :
    Γ((Scheme.Modules.pullback U'.hom).obj F, ⊤) →+ Γ((Scheme.Modules.pullback U.hom).obj F, ⊤) :=
  ((compHom F g.left U'.hom U.hom (MorphismProperty.Over.w g)).app ⊤).hom.comp
    (pullbackSection g.left _)
lemma qcohMap_apply {U U' : X.Etale} (g : U ⟶ U') (s : Γ((Scheme.Modules.pullback U'.hom).obj F, ⊤)) :
    qcohMap F g s =
      (compHom F g.left U'.hom U.hom (MorphismProperty.Over.w g)).app ⊤
        (pullbackSection g.left _ s) := rfl
lemma qcohMap_id (U : X.Etale) (s : Γ((Scheme.Modules.pullback U.hom).obj F, ⊤)) :
    qcohMap F (𝟙 U) s = s :=
  compHom_id_section F U.hom (MorphismProperty.Over.w (𝟙 U)) s
lemma qcohMap_comp {U U' U'' : X.Etale} (g : U ⟶ U') (k : U' ⟶ U'')
    (s : Γ((Scheme.Modules.pullback U''.hom).obj F, ⊤)) :
    qcohMap F (g ≫ k) s = qcohMap F g (qcohMap F k s) := by
  have e1 := pullbackSection_naturality g.left
    (compHom F k.left U''.hom U'.hom (MorphismProperty.Over.w k))
    (pullbackSection k.left _ s)
  have e2 := congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤).hom
      (pullbackSection g.left _ (pullbackSection k.left _ s)))
    (compHom_assoc F g.left k.left U''.hom U'.hom U.hom (MorphismProperty.Over.w k)
      (MorphismProperty.Over.w g))
  have e3 := pullbackComp_hom_pullbackSection g.left k.left
    ((Scheme.Modules.pullback U''.hom).obj F) s
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply] at e2
  rw [qcohMap_apply, qcohMap_apply, qcohMap_apply, ← e1, e2, e3]
  rfl
noncomputable def qcohPresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := Γ((Scheme.Modules.pullback U.unop.hom).obj F, ⊤)
  map g := AddCommGrpCat.ofHom (qcohMap F g.unop)
  map_id U := by
    ext s
    exact qcohMap_id F U.unop s
  map_comp g k := by
    ext s
    exact qcohMap_comp F k.unop g.unop s
end Presheaf
end GroundTheory.Arith.Etale


