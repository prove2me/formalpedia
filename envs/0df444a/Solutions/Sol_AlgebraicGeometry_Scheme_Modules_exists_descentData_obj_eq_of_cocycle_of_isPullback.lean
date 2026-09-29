-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/815edbf3-bd19-523a-ac5a-10f50a9672eb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace LDescDatumAux

p2m_open "CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

section generic

universe w v v' u'

variable {C : Type w} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

set_option backward.isDefEq.respectTransparency false in

theorem pullHom_hom_inv_id {X₁ X₂ Y Y' : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom φ.hom g gf₁ gf₂ h₁ h₂ ≫ pullHom φ.inv g gf₂ gf₁ h₂ h₁ = 𝟙 _ := by
  dsimp only [pullHom]
  simp only [Category.assoc]
  rw [← reassoc_of% Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app, Category.id_comp,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]

variable {S Y : C} {f : Y ⟶ S} (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
  (M : F.obj (.mk (op Y)))
  (φ : (F.map sq.p₁.op.toLoc).toFunctor.obj M ≅ (F.map sq.p₂.op.toLoc).toFunctor.obj M)

abbrev homG : ∀ (i j : Unit),
    (F.map ((fun _ _ : Unit => sq) i j).p₁.op.toLoc).toFunctor.obj ((fun _ : Unit => M) i) ⟶
      (F.map ((fun _ _ : Unit => sq) i j).p₂.op.toLoc).toFunctor.obj ((fun _ : Unit => M) j) :=
  fun _ _ => φ.hom

theorem generic_comp
    (hφ : pullHom φ.hom sq₃.p₁₂ sq₃.p₁ sq₃.p₂ sq₃.p₁₂_p₁ sq₃.p₁₂_p₂ ≫
        pullHom φ.hom sq₃.p₂₃ sq₃.p₂ sq₃.p₃ sq₃.p₂₃_p₂ sq₃.p₂₃_p₃ =
      pullHom φ.hom sq₃.p₁₃ sq₃.p₁ sq₃.p₃ sq₃.p₁₃_p₁ sq₃.p₁₃_p₃)
    (i₁ i₂ i₃ : Unit) :
    DescentData'.pullHom' (F := F) (sq := fun _ _ : Unit => sq) (homG sq M φ)
        ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p (i₁ := i₁) (i₂ := i₂)
        ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p₁ ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p₂
        (ChosenPullback₃.w₁ _) (ChosenPullback₃.w₂ _) ≫
      DescentData'.pullHom' (F := F) (sq := fun _ _ : Unit => sq) (homG sq M φ)
        ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p (i₁ := i₂) (i₂ := i₃)
        ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p₂ ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p₃
        (ChosenPullback₃.w₂ _) (ChosenPullback₃.w₃ _) =
      DescentData'.pullHom' (F := F) (sq := fun _ _ : Unit => sq) (homG sq M φ)
        ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p (i₁ := i₁) (i₂ := i₃)
        ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p₁ ((fun _ _ _ : Unit => sq₃) i₁ i₂ i₃).p₃
        (ChosenPullback₃.w₁ _) (ChosenPullback₃.w₃ _) := by
  obtain ⟨⟩ := i₁; obtain ⟨⟩ := i₂; obtain ⟨⟩ := i₃
  rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (sq₃ := fun _ _ _ : Unit => sq₃) (homG sq M φ) () () (),
    DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (sq₃ := fun _ _ _ : Unit => sq₃) (homG sq M φ) () () (),
    DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (sq₃ := fun _ _ _ : Unit => sq₃) (homG sq M φ) () () ()]
  exact hφ

theorem generic_self
    (hφ : pullHom φ.hom sq₃.p₁₂ sq₃.p₁ sq₃.p₂ sq₃.p₁₂_p₁ sq₃.p₁₂_p₂ ≫
        pullHom φ.hom sq₃.p₂₃ sq₃.p₂ sq₃.p₃ sq₃.p₂₃_p₂ sq₃.p₂₃_p₃ =
      pullHom φ.hom sq₃.p₁₃ sq₃.p₁ sq₃.p₃ sq₃.p₁₃_p₁ sq₃.p₁₃_p₃)
    (i : Unit) :
    DescentData'.pullHom' (F := F) (sq := fun _ _ : Unit => sq) (homG sq M φ) ((fun _ : Unit => f) i)
      (i₁ := i) (i₂ := i) (𝟙 Y) (𝟙 Y) (Category.id_comp f) (Category.id_comp f) = 𝟙 _ := by
  obtain ⟨⟩ := i
  have h3 := DescentData'.comp_pullHom'' (F := F) (sq := fun _ _ : Unit => sq) (sq₃ := fun _ _ _ : Unit => sq₃)
    (homG sq M φ) (generic_comp sq sq₃ M φ hφ) f (i₁ := ()) (i₂ := ()) (i₃ := ())
    (𝟙 Y) (𝟙 Y) (𝟙 Y) (Category.id_comp f) (Category.id_comp f) (Category.id_comp f)
  have uv : DescentData'.pullHom' (F := F) (sq := fun _ _ : Unit => sq) (homG sq M φ) f
      (i₁ := ()) (i₂ := ()) (𝟙 Y) (𝟙 Y) (Category.id_comp f) (Category.id_comp f) ≫
      pullHom φ.inv (sq.isPullback.lift (𝟙 Y) (𝟙 Y) (by simp)) (𝟙 Y) (𝟙 Y)
        (sq.isPullback.lift_snd _ _ _) (sq.isPullback.lift_fst _ _ _) = 𝟙 _ :=
    pullHom_hom_inv_id φ _ _ _ _ _
  rw [← Category.comp_id (DescentData'.pullHom' _ _ _ _ _ _), ← uv, ← Category.assoc, h3]

noncomputable def genericDatum
    (hφ : pullHom φ.hom sq₃.p₁₂ sq₃.p₁ sq₃.p₂ sq₃.p₁₂_p₁ sq₃.p₁₂_p₂ ≫
        pullHom φ.hom sq₃.p₂₃ sq₃.p₂ sq₃.p₃ sq₃.p₂₃_p₂ sq₃.p₂₃_p₃ =
      pullHom φ.hom sq₃.p₁₃ sq₃.p₁ sq₃.p₃ sq₃.p₁₃_p₁ sq₃.p₁₃_p₃) :
    F.DescentData' (fun _ _ : Unit => sq) (fun _ _ _ : Unit => sq₃) where
  obj := fun _ => M
  hom := homG sq M φ
  pullHom'_hom_self := generic_self sq sq₃ M φ hφ
  pullHom'_hom_comp := generic_comp sq sq₃ M φ hφ

end generic

section modules

open AlgebraicGeometry

noncomputable abbrev FF := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem cat_eqToHom_app {A B : Cat.{u, u + 1}} {G H : A ⟶ B} (h : G = H) (Z : A) :
    (eqToHom h).toNatTrans.app Z = eqToHom (by rw [h]) := by
  subst h; rfl

theorem FF_mapComp_hom_app {T T' W : Scheme.{u}} (p : T' ⟶ T) (f : W ⟶ T') (M : T.Modules) :
    (FF.mapComp p.op.toLoc f.op.toLoc).hom.toNatTrans.app M = (Scheme.Modules.pullbackComp f p).inv.app M := rfl

theorem FF_mapComp_inv_app {T T' W : Scheme.{u}} (p : T' ⟶ T) (f : W ⟶ T') (M : T.Modules) :
    (FF.mapComp p.op.toLoc f.op.toLoc).inv.toNatTrans.app M = (Scheme.Modules.pullbackComp f p).hom.app M := rfl

theorem FF_map_map {T T' : Scheme.{u}} (p : T' ⟶ T) {L M : T.Modules} (β : L ⟶ M) :
    (FF.map p.op.toLoc).toFunctor.map β = (Scheme.Modules.pullback p).map β := rfl

theorem pullHom_FF {X' X'' W : Scheme.{u}} {a₁ a₂ : X'' ⟶ X'} {L₁ L₂ : X'.Modules}
    (φ : (Scheme.Modules.pullback a₁).obj L₁ ⟶ (Scheme.Modules.pullback a₂).obj L₂)
    (b : W ⟶ X'') (g₁ g₂ : W ⟶ X') (hg₁ : b ≫ a₁ = g₁) (hg₂ : b ≫ a₂ = g₂) :
    pullHom (F := FF) (M₁ := L₁) (M₂ := L₂) (f₁ := a₁) (f₂ := a₂) φ b g₁ g₂ hg₁ hg₂ =
      ((Scheme.Modules.pullbackCongr hg₁).inv.app L₁ ≫ (Scheme.Modules.pullbackComp b a₁).inv.app L₁ ≫
        (Scheme.Modules.pullback b).map φ ≫ (Scheme.Modules.pullbackComp b a₂).hom.app L₂ ≫
        (Scheme.Modules.pullbackCongr hg₂).hom.app L₂ :
          (Scheme.Modules.pullback g₁).obj L₁ ⟶ (Scheme.Modules.pullback g₂).obj L₂) := by
  dsimp only [pullHom, Pseudofunctor.mapComp']
  simp only [Iso.trans_hom, Iso.trans_inv, PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂Iso_inv,
    eqToIso.hom, eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.comp_app, Category.assoc]
  rw [cat_eqToHom_app, cat_eqToHom_app, FF_mapComp_hom_app, FF_mapComp_inv_app, FF_map_map]
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app]
  rfl

noncomputable def pullHomIso {X' X'' W : Scheme.{u}} {a₁ a₂ : X'' ⟶ X'} {L₁ L₂ : X'.Modules}
    (ψ : (Scheme.Modules.pullback a₁).obj L₁ ≅ (Scheme.Modules.pullback a₂).obj L₂)
    (b : W ⟶ X'') (g₁ g₂ : W ⟶ X') (hg₁ : b ≫ a₁ = g₁) (hg₂ : b ≫ a₂ = g₂) :
    (Scheme.Modules.pullback g₁).obj L₁ ≅ (Scheme.Modules.pullback g₂).obj L₂ :=
  ((Scheme.Modules.pullbackCongr hg₁).app L₁).symm ≪≫ ((Scheme.Modules.pullbackComp b a₁).app L₁).symm ≪≫
    (Scheme.Modules.pullback b).mapIso ψ ≪≫ (Scheme.Modules.pullbackComp b a₂).app L₂ ≪≫
    (Scheme.Modules.pullbackCongr hg₂).app L₂

theorem pullHom_FF_iso {X' X'' W : Scheme.{u}} {a₁ a₂ : X'' ⟶ X'} {L₁ L₂ : X'.Modules}
    (ψ : (Scheme.Modules.pullback a₁).obj L₁ ≅ (Scheme.Modules.pullback a₂).obj L₂)
    (b : W ⟶ X'') (g₁ g₂ : W ⟶ X') (hg₁ : b ≫ a₁ = g₁) (hg₂ : b ≫ a₂ = g₂) :
    pullHom (F := FF) (M₁ := L₁) (M₂ := L₂) (f₁ := a₁) (f₂ := a₂) ψ.hom b g₁ g₂ hg₁ hg₂ =
      (pullHomIso ψ b g₁ g₂ hg₁ hg₂).hom :=
  pullHom_FF ψ.hom b g₁ g₂ hg₁ hg₂

variable {X X' X'' X''' : Scheme.{u}} (c : X' ⟶ X) (a₁ a₂ : X'' ⟶ X') (ha : IsPullback a₁ a₂ c c)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (hb : IsPullback b₁₂ b₂₃ a₂ a₁)

@[reducible] noncomputable def sqC : ChosenPullback c c where
  pullback := X''
  p₁ := a₁
  p₂ := a₂
  condition := ha.w
  isLimit := ha.isLimit

@[reducible] noncomputable def sq3C : ChosenPullback₃ (sqC c a₁ a₂ ha) (sqC c a₁ a₂ ha) (sqC c a₁ a₂ ha) where
  chosenPullback :=
    { pullback := X'''
      p₁ := b₁₂
      p₂ := b₂₃
      condition := h₂
      isLimit := hb.isLimit }
  l :=
    { f := b₁₃
      f_p₁ := h₁.symm
      f_p₂ := h₃
      f_p := by
        change b₁₃ ≫ a₁ ≫ c = b₁₂ ≫ a₁ ≫ c
        rw [← Category.assoc, ← h₁, Category.assoc] }

variable (L' : X'.Modules) (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')

noncomputable def ψF :
    (FF.map (sqC c a₁ a₂ ha).p₁.op.toLoc).toFunctor.obj L' ≅ (FF.map (sqC c a₁ a₂ ha).p₂.op.toLoc).toFunctor.obj L' :=
  ⟨ψ.hom, ψ.inv, ψ.hom_inv_id, ψ.inv_hom_id⟩

theorem pullHom_ψF {W : Scheme.{u}} (b : W ⟶ X'') (g₁ g₂ : W ⟶ X') (hg₁ : b ≫ a₁ = g₁) (hg₂ : b ≫ a₂ = g₂) :
    pullHom (F := FF) (ψF c a₁ a₂ ha L' ψ).hom b g₁ g₂ hg₁ hg₂ = (pullHomIso ψ b g₁ g₂ hg₁ hg₂).hom :=
  pullHom_FF_iso ψ b g₁ g₂ hg₁ hg₂

theorem cocycle_iso (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    (pullHomIso ψ b₁₂ (b₁₂ ≫ a₁) (b₁₂ ≫ a₂) rfl rfl).hom ≫ (pullHomIso ψ b₂₃ (b₁₂ ≫ a₂) (b₂₃ ≫ a₂) h₂.symm rfl).hom =
      (pullHomIso ψ b₁₃ (b₁₂ ≫ a₁) (b₂₃ ≫ a₂) h₁.symm h₃).hom := by
  have E₁ : (Scheme.Modules.pullback (b₁₂ ≫ a₁)).obj L' = (Scheme.Modules.pullback (b₁₃ ≫ a₁)).obj L' := by rw [h₁]
  have E₃ : (Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L' = (Scheme.Modules.pullback (b₂₃ ≫ a₂)).obj L' := by rw [h₃]
  have t := congrArg (fun x => eqToHom E₁ ≫ x ≫ eqToHom E₃) (congrArg Iso.hom hψ)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id] at t
  simp only [pullHomIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  exact t

theorem cocycle_iso' (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    (pullHomIso ψ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₂_p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₂_p₂).hom ≫
      (pullHomIso ψ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂₃_p₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂₃_p₃).hom =
      (pullHomIso ψ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₃_p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₃_p₃).hom :=
  cocycle_iso a₁ a₂ b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ L' ψ hψ

theorem cocycle_pullHom (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    pullHom (F := FF) (ψF c a₁ a₂ ha L' ψ).hom (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₂_p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₂_p₂ ≫
      pullHom (F := FF) (ψF c a₁ a₂ ha L' ψ).hom (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂₃_p₂ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₂₃_p₃ =
      pullHom (F := FF) (ψF c a₁ a₂ ha L' ψ).hom (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₃ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₃_p₁ (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb).p₁₃_p₃ := by
  rw [pullHom_ψF, pullHom_ψF, pullHom_ψF]
  exact cocycle_iso' c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb L' ψ hψ

noncomputable def datum (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) : FF.DescentData (fun _ : Unit => c) :=
  (genericDatum (F := FF) (sqC c a₁ a₂ ha) (sq3C c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb) L' (ψF c a₁ a₂ ha L' ψ)
    (cocycle_pullHom c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb L' ψ hψ)).descentData

theorem datum_obj (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) (i : Unit) :
    (datum c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb L' ψ hψ).obj i = L' := rfl

end modules

end LDescDatumAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped TensorProduct in
theorem solution
    {X X' X'' X''' : Scheme.{u}} (c : X' ⟶ X) (a₁ a₂ : X'' ⟶ X') (ha : IsPullback a₁ a₂ c c)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (hb : IsPullback b₁₂ b₂₃ a₂ a₁)
    (L' : X'.Modules)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    ∃ D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => c),
      ∀ i, D.obj i = L' :=
  ⟨LDescDatumAux.datum c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb L' ψ hψ,
    LDescDatumAux.datum_obj c a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hb L' ψ hψ⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback (solution)
