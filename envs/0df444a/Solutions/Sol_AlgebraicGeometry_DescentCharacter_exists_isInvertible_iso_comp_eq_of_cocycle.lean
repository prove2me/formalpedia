-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.exists_isInvertible_iso_comp_eq_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6ee8cf6b-4826-5573-a579-b30988dca649

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Bicategory CategoryTheory.Bicategory Opposite Bicategory.Opposite AlgebraicGeometry.DescentCharacter CategoryTheory.Pseudofunctor CategoryTheory.Bicategory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

universe u

noncomputable section

namespace KcDescEff

abbrev FF := ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)

section modulesLevel
variable {X Y P : Scheme.{u}}

def canonIso (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g₁ g₂ : P ⟶ X) (hg₁ : g₁ ≫ q = r) (hg₂ : g₂ ≫ q = r) :
    (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback g₂).obj ((Scheme.Modules.pullback q).obj M) :=
  (Scheme.Modules.pullbackComp g₁ q).app M ≪≫
    eqToIso (show (Scheme.Modules.pullback (g₁ ≫ q)).obj M = (Scheme.Modules.pullback (g₂ ≫ q)).obj M by
      rw [hg₁, hg₂]) ≪≫
    ((Scheme.Modules.pullbackComp g₂ q).app M).symm

theorem pullbackCongr_hom_app {g g' : X ⟶ Y} (e : g = g') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app M =
      eqToHom (show (Scheme.Modules.pullback g).obj M = (Scheme.Modules.pullback g').obj M by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

end modulesLevel

section unfold
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem mapComp_hom_app (M : Z.Modules) :
    ((FF.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app M) = (Scheme.Modules.pullbackComp f g).inv.app M := rfl

theorem mapComp_inv_app (M : Z.Modules) :
    ((FF.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app M) = (Scheme.Modules.pullbackComp f g).hom.app M := rfl

theorem mapComp'_hom_app (fg : X ⟶ Z) (hfg : f ≫ g = fg)
    (H : g.op.toLoc ≫ f.op.toLoc = fg.op.toLoc) (M : Z.Modules) :
    ((FF.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc H).hom.toNatTrans.app M) =
      eqToHom (show (Scheme.Modules.pullback fg).obj M = (Scheme.Modules.pullback (f ≫ g)).obj M by rw [hfg]) ≫
        (Scheme.Modules.pullbackComp f g).inv.app M := by
  subst hfg
  simp only [Pseudofunctor.mapComp', PrelaxFunctor.map₂Iso_hom, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
    Iso.trans_hom, Cat.Hom₂.comp_app, Cat.eqToHom_app, mapComp_hom_app]
  rfl

theorem mapComp'_inv_app (fg : X ⟶ Z) (hfg : f ≫ g = fg)
    (H : g.op.toLoc ≫ f.op.toLoc = fg.op.toLoc) (M : Z.Modules) :
    ((FF.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc H).inv.toNatTrans.app M) =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫
      eqToHom (show (Scheme.Modules.pullback (f ≫ g)).obj M = (Scheme.Modules.pullback fg).obj M by rw [hfg]) := by
  subst hfg
  simp only [Pseudofunctor.mapComp', Iso.trans_inv, PrelaxFunctor.map₂Iso_inv, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.comp_app, Cat.eqToHom_app, mapComp_inv_app]
  rfl

theorem mapComp'_inv_comp_hom {P : Scheme.{u}} (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g₁ g₂ : P ⟶ X)
    (hg₁ : g₁ ≫ q = r) (hg₂ : g₂ ≫ q = r)
    (H1 : q.op.toLoc ≫ g₁.op.toLoc = r.op.toLoc) (H2 : q.op.toLoc ≫ g₂.op.toLoc = r.op.toLoc) :
    (FF.mapComp' q.op.toLoc g₁.op.toLoc r.op.toLoc H1).inv.toNatTrans.app M ≫
      (FF.mapComp' q.op.toLoc g₂.op.toLoc r.op.toLoc H2).hom.toNatTrans.app M = (canonIso q M r g₁ g₂ hg₁ hg₂).hom := by
  have e1 := mapComp'_inv_app g₁ q r hg₁ H1 M
  have e2 := mapComp'_hom_app g₂ q r hg₂ H2 M
  rw [e1, e2]
  have test : ((Scheme.Modules.pullbackComp g₁ q).hom.app M ≫
      eqToHom (show (Scheme.Modules.pullback (g₁ ≫ q)).obj M = (Scheme.Modules.pullback r).obj M by rw [hg₁])) ≫
      (eqToHom (show (Scheme.Modules.pullback r).obj M = (Scheme.Modules.pullback (g₂ ≫ q)).obj M by rw [hg₂]) ≫
        (Scheme.Modules.pullbackComp g₂ q).inv.app M) = (canonIso q M r g₁ g₂ hg₁ hg₂).hom := by
    simp only [canonIso, Iso.trans_hom, Iso.app_hom, eqToIso.hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
      eqToHom_trans_assoc]
    try dsimp only [Functor.comp_obj]
  exact test

theorem ofObj_hom_eq {P : Scheme.{u}} (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g₁ g₂ : P ⟶ X)
    (hg₁ : g₁ ≫ q = r) (hg₂ : g₂ ≫ q = r) :
    (DescentData.ofObj (F := FF) (f := fun _ : Unit => q) M).hom r (i₁ := ()) (i₂ := ()) g₁ g₂ hg₁ hg₂ =
      (canonIso q M r g₁ g₂ hg₁ hg₂).hom := by
  rw [DescentData.ofObj_hom]
  exact mapComp'_inv_comp_hom q M r g₁ g₂ hg₁ hg₂ _ _

end unfold

section generic

universe w₁ w₂ v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁, w₂})
  {S X₀ P₀ P₃ : C} (q : X₀ ⟶ S) (p₁ p₂ : P₀ ⟶ X₀) (w : p₁ ≫ q = p₂ ≫ q)
  (a b : P₃ ⟶ P₀) (wab : a ≫ p₂ = b ≫ p₁)
  (c : P₃ ⟶ P₀) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)

abbrev gsq (hlim : IsLimit (PullbackCone.mk p₁ p₂ w)) : ChosenPullback q q :=
  { pullback := P₀, p₁ := p₁, p₂ := p₂, condition := w, isLimit := hlim, p := p₁ ≫ q, hp₁ := rfl }

abbrev gsq₃ (hlim : IsLimit (PullbackCone.mk p₁ p₂ w)) (hlim₃ : IsLimit (PullbackCone.mk a b wab)) :
    ChosenPullback₃ (gsq q p₁ p₂ w hlim) (gsq q p₁ p₂ w hlim) (gsq q p₁ p₂ w hlim) :=
  { chosenPullback :=
      { pullback := P₃, p₁ := a, p₂ := b, condition := wab, isLimit := hlim₃, p := a ≫ p₂, hp₁ := rfl }
    l := { f := c, f_p₁ := hca, f_p₂ := hcb, f_p := by
            change c ≫ p₁ ≫ q = a ≫ p₁ ≫ q
            rw [← Category.assoc, hca, Category.assoc] } }

theorem generic_effective (hlim : IsLimit (PullbackCone.mk p₁ p₂ w)) (hlim₃ : IsLimit (PullbackCone.mk a b wab))
    (δ : X₀ ⟶ P₀) (hδ₁ : δ ≫ p₁ = 𝟙 X₀) (hδ₂ : δ ≫ p₂ = 𝟙 X₀)
    {L : F.obj (.mk (op X₀))}
    (hom : (F.map p₁.op.toLoc).toFunctor.obj L ⟶ (F.map p₂.op.toLoc).toFunctor.obj L)
    (hself : pullHom hom δ (𝟙 X₀) (𝟙 X₀) hδ₁ hδ₂ = 𝟙 _)
    (hcomp : pullHom hom a (a ≫ p₁) (a ≫ p₂) rfl rfl ≫ pullHom hom b (a ≫ p₂) (b ≫ p₂) wab.symm rfl =
      pullHom hom c (a ≫ p₁) (b ≫ p₂) hca hcb)
    (PL : F.obj (.mk (op X₀)) → Prop) (PN : F.obj (.mk (op S)) → Prop) (hL : PL L)
    (heff : ∀ D : F.DescentData (fun _ : Unit => q), (∀ i, PL (D.obj i)) →
      ∃ N : F.obj (.mk (op S)), PN N ∧ Nonempty ((F.toDescentData (fun _ : Unit => q)).obj N ≅ D)) :
    ∃ (N : F.obj (.mk (op S))) (_ : PN N) (β : (F.map q.op.toLoc).toFunctor.obj N ≅ L),
      (F.map p₁.op.toLoc).toFunctor.map β.hom ≫ hom =
        (DescentData.ofObj (F := F) (f := fun _ : Unit => q) N).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm ≫ (F.map p₂.op.toLoc).toFunctor.map β.hom := by

  let D' : F.DescentData' (fun _ _ : Unit => gsq q p₁ p₂ w hlim)
      (fun _ _ _ : Unit => gsq₃ q p₁ p₂ w a b wab c hca hcb hlim hlim₃) :=
    { obj := fun _ => L
      hom := fun _ _ => hom
      pullHom'_hom_self := fun i => by
        cases i
        rw [DescentData'.pullHom'_eq_pullHom (F := F) (sq := fun _ _ : Unit => gsq q p₁ p₂ w hlim)
          (obj := fun _ => L) (obj' := fun _ => L) (fun _ _ => hom) q (i₁ := ()) (i₂ := ()) (𝟙 X₀) (𝟙 X₀) δ
          (by simp) (by simp) hδ₁ hδ₂]
        exact hself
      pullHom'_hom_comp := fun i₁ i₂ i₃ => by
        cases i₁; cases i₂; cases i₃
        rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (F := F) (sq := fun _ _ : Unit => gsq q p₁ p₂ w hlim)
            (sq₃ := fun _ _ _ : Unit => gsq₃ q p₁ p₂ w a b wab c hca hcb hlim hlim₃) (obj := fun _ => L)
            (fun _ _ => hom) () () (),
          DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (F := F) (sq := fun _ _ : Unit => gsq q p₁ p₂ w hlim)
            (sq₃ := fun _ _ _ : Unit => gsq₃ q p₁ p₂ w a b wab c hca hcb hlim hlim₃) (obj := fun _ => L)
            (fun _ _ => hom) () () (),
          DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (F := F) (sq := fun _ _ : Unit => gsq q p₁ p₂ w hlim)
            (sq₃ := fun _ _ _ : Unit => gsq₃ q p₁ p₂ w a b wab c hca hcb hlim hlim₃) (obj := fun _ => L)
            (fun _ _ => hom) () () ()]
        exact hcomp }
  obtain ⟨N, hN, ⟨e⟩⟩ := heff D'.descentData (fun _ => hL)

  have h₁ := congrArg (fun ψ => DescentData.Hom.hom ψ ()) e.hom_inv_id
  have h₂ := congrArg (fun ψ => DescentData.Hom.hom ψ ()) e.inv_hom_id
  simp only [DescentData.comp_hom, DescentData.id_hom] at h₁ h₂
  let β : (F.map q.op.toLoc).toFunctor.obj N ≅ L := ⟨e.hom.hom (), e.inv.hom (), h₁, h₂⟩
  refine ⟨N, hN, β, ?_⟩
  have H := e.hom.comm (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂ rfl w.symm

  rw [DescentData'.descentData_hom] at H
  rw [DescentData'.pullHom'_eq_pullHom D'.hom (p₁ ≫ q) p₁ p₂ (𝟙 P₀) rfl w.symm (Category.id_comp _)
    (Category.id_comp _), pullHom_id] at H
  exact H.symm.symm

end generic

section bridge
variable {X Y P Z : Scheme.{u}}

theorem mapComp'_hom_comp_map_comp_inv (p₁ p₂ : P ⟶ X) (L : X.Modules)
    (φ : (Scheme.Modules.pullback p₁).obj L ⟶ (Scheme.Modules.pullback p₂).obj L)
    (g : Z ⟶ P) (gf₁ gf₂ : Z ⟶ X) (hg₁ : g ≫ p₁ = gf₁) (hg₂ : g ≫ p₂ = gf₂)
    (H1 : p₁.op.toLoc ≫ g.op.toLoc = gf₁.op.toLoc) (H2 : p₂.op.toLoc ≫ g.op.toLoc = gf₂.op.toLoc) :
    (FF.mapComp' p₁.op.toLoc g.op.toLoc gf₁.op.toLoc H1).hom.toNatTrans.app L ≫
      (Scheme.Modules.pullback g).map φ ≫ (FF.mapComp' p₂.op.toLoc g.op.toLoc gf₂.op.toLoc H2).inv.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr hg₁).inv.app L ≫ (Scheme.Modules.pullbackComp g p₁).inv.app L ≫
      (Scheme.Modules.pullback g).map φ ≫ (Scheme.Modules.pullbackComp g p₂).hom.app L ≫
        (Scheme.Modules.pullbackCongr hg₂).hom.app L := by
  rw [mapComp'_hom_app g p₁ gf₁ hg₁ H1 L, mapComp'_inv_app g p₂ gf₂ hg₂ H2 L]
  have test : (eqToHom (show (Scheme.Modules.pullback gf₁).obj L = (Scheme.Modules.pullback (g ≫ p₁)).obj L by
        rw [hg₁]) ≫ (Scheme.Modules.pullbackComp g p₁).inv.app L) ≫ (Scheme.Modules.pullback g).map φ ≫
        ((Scheme.Modules.pullbackComp g p₂).hom.app L ≫
          eqToHom (show (Scheme.Modules.pullback (g ≫ p₂)).obj L = (Scheme.Modules.pullback gf₂).obj L by
            rw [hg₂])) =
      (Scheme.Modules.pullbackCongr hg₁).inv.app L ≫ (Scheme.Modules.pullbackComp g p₁).inv.app L ≫
        (Scheme.Modules.pullback g).map φ ≫ (Scheme.Modules.pullbackComp g p₂).hom.app L ≫
          (Scheme.Modules.pullbackCongr hg₂).hom.app L := by
    rw [pullbackCongr_hom_app hg₂ L]
    have : (Scheme.Modules.pullbackCongr hg₁).inv.app L =
        eqToHom (show (Scheme.Modules.pullback gf₁).obj L = (Scheme.Modules.pullback (g ≫ p₁)).obj L by
          rw [hg₁]) := by
      subst hg₁; simp [Scheme.Modules.pullbackCongr]
    rw [this]
    simp only [Category.assoc]
  exact test

theorem pullHom_eq (p₁ p₂ : P ⟶ X) (L : X.Modules)
    (φ : (Scheme.Modules.pullback p₁).obj L ⟶ (Scheme.Modules.pullback p₂).obj L)
    (g : Z ⟶ P) (gf₁ gf₂ : Z ⟶ X) (hg₁ : g ≫ p₁ = gf₁) (hg₂ : g ≫ p₂ = gf₂) :
    pullHom (F := FF) (M₁ := L) (M₂ := L) (f₁ := p₁) (f₂ := p₂) φ g gf₁ gf₂ hg₁ hg₂ =
    (Scheme.Modules.pullbackCongr hg₁).inv.app L ≫ (Scheme.Modules.pullbackComp g p₁).inv.app L ≫
      (Scheme.Modules.pullback g).map φ ≫ (Scheme.Modules.pullbackComp g p₂).hom.app L ≫
        (Scheme.Modules.pullbackCongr hg₂).hom.app L := by
  rw [pullHom]
  exact mapComp'_hom_comp_map_comp_inv p₁ p₂ L φ g gf₁ gf₂ hg₁ hg₂ _ _

end bridge

section main
variable {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (p₁ p₂ : P ⟶ X) (hP : IsPullback p₁ p₂ q q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hP₃ : IsPullback a b p₂ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)

theorem effective {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M))
    (hunit :
      (Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _)
    (hcocycle :
      ((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hP₃.w).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) :
    ∃ (N : Y.Modules) (_ : Scheme.Modules.IsInvertible N)
      (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M),
      (Scheme.Modules.pullback p₁).map β.hom ≫ φ =
        ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hP.w]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom := by

  have hself : pullHom (F := FF) (M₁ := (Scheme.Modules.pullback q).obj M) (M₂ := (Scheme.Modules.pullback q).obj M)
      (f₁ := p₁) (f₂ := p₂) φ δ (𝟙 X) (𝟙 X) hδ₁ hδ₂ = 𝟙 _ := by
    rw [pullHom_eq]
    exact hunit
  have e1 : (Scheme.Modules.pullbackCongr (rfl : a ≫ p₁ = a ≫ p₁)).inv.app ((Scheme.Modules.pullback q).obj M) =
      𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have e2 : (Scheme.Modules.pullbackCongr (rfl : a ≫ p₂ = a ≫ p₂)).hom.app ((Scheme.Modules.pullback q).obj M) =
      𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have e3 : (Scheme.Modules.pullbackCongr (rfl : b ≫ p₂ = b ≫ p₂)).hom.app ((Scheme.Modules.pullback q).obj M) =
      𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have e4 : (Scheme.Modules.pullbackCongr hP₃.w.symm).inv.app ((Scheme.Modules.pullback q).obj M) =
      (Scheme.Modules.pullbackCongr hP₃.w).hom.app ((Scheme.Modules.pullback q).obj M) := by
    simp [Scheme.Modules.pullbackCongr]
  have hcocycle' := hcocycle
  rw [← e4] at hcocycle'
  rw [← Category.id_comp ((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M)), ← e1,
    ← Category.comp_id ((Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)), ← e2,
    ← Category.comp_id ((Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)), ← e3]
    at hcocycle'
  have hcomp : pullHom (F := FF) (M₁ := (Scheme.Modules.pullback q).obj M) (M₂ := (Scheme.Modules.pullback q).obj M)
        (f₁ := p₁) (f₂ := p₂) φ a (a ≫ p₁) (a ≫ p₂) rfl rfl ≫
      pullHom (F := FF) (M₁ := (Scheme.Modules.pullback q).obj M) (M₂ := (Scheme.Modules.pullback q).obj M)
        (f₁ := p₁) (f₂ := p₂) φ b (a ≫ p₂) (b ≫ p₂) hP₃.w.symm rfl =
      pullHom (F := FF) (M₁ := (Scheme.Modules.pullback q).obj M) (M₂ := (Scheme.Modules.pullback q).obj M)
        (f₁ := p₁) (f₂ := p₂) φ c (a ≫ p₁) (b ≫ p₂) hca hcb := by
    rw [pullHom_eq, pullHom_eq, pullHom_eq]
    simp only [Category.assoc] at hcocycle' ⊢
    exact hcocycle'
  obtain ⟨N, hN, β, hβ⟩ := generic_effective FF q p₁ p₂ hP.w a b hP₃.w c hca hcb hP.isLimit hP₃.isLimit δ hδ₁ hδ₂ φ
    hself hcomp (fun L' => Scheme.Modules.IsInvertible L') (fun N' => Scheme.Modules.IsInvertible N')
    (hM.pullback q)
    (fun D hD => AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
      q D hD)
  refine ⟨N, hN, β, ?_⟩
  rw [ofObj_hom_eq q N (p₁ ≫ q) p₁ p₂ rfl hP.w.symm] at hβ
  exact hβ

end main

end KcDescEff

end

theorem solution
    {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (p₁ p₂ : P ⟶ X) (hP : IsPullback p₁ p₂ q q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hP₃ : IsPullback a b p₂ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M))
    (hunit :
      (Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _)
    (hcocycle :
      ((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hP₃.w).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) :
    ∃ (N : Y.Modules) (_ : Scheme.Modules.IsInvertible N)
      (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M),
      (Scheme.Modules.pullback p₁).map β.hom ≫ φ =
        ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hP.w]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom :=
  KcDescEff.effective q p₁ p₂ hP δ hδ₁ hδ₂ a b hP₃ c hca hcb hM φ hunit hcocycle

end S_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle (solution)
