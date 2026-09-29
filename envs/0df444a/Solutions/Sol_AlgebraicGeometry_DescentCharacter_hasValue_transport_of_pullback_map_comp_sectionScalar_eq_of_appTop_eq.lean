-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/292a6951-5c6e-5293-84c9-361b5ee84b5b

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Bicategory CategoryTheory.Bicategory AlgebraicGeometry AlgebraicGeometry.DescentCharacter CategoryTheory.Pseudofunctor CategoryTheory.Bicategory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

noncomputable section

namespace C7G2

namespace Gen

universe w₁ w₂ v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁, w₂})

variable {C : Type u₁} [Category.{v₁} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁, w₂})

theorem toLoc_eq {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg) :
    g.op.toLoc ≫ f.op.toLoc = fg.op.toLoc := by
  rw [← h, op_comp, Quiver.Hom.comp_toLoc]

theorem pullHom_mapComp'_conj {S S' X' : C} (gY : S' ⟶ S) (q' : X' ⟶ S') (ρ : X' ⟶ S) (hρ : q' ≫ gY = ρ)
    (T' : X' ⟶ X') (h' : T' ≫ q' = q') (hT : T' ≫ ρ = ρ) {N M : F.obj (.mk (op S))}
    (ψ : (F.map ρ.op.toLoc).toFunctor.obj N ⟶ (F.map ρ.op.toLoc).toFunctor.obj M) :
    pullHom (F := F) (M₁ := (F.map gY.op.toLoc).toFunctor.obj N) (M₂ := (F.map gY.op.toLoc).toFunctor.obj M)
        (f₁ := q') (f₂ := q')
        ((F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app N ≫ ψ ≫
          (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app M)
        T' q' q' h' h' =
      (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app N ≫
        pullHom (F := F) (M₁ := N) (M₂ := M) (f₁ := ρ) (f₂ := ρ) ψ T' ρ ρ hT hT ≫
        (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app M := by
  have key := fun (L : F.obj (.mk (op S))) =>
    F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app gY.op.toLoc q'.op.toLoc T'.op.toLoc ρ.op.toLoc q'.op.toLoc
      ρ.op.toLoc (toLoc_eq q' gY ρ hρ) (toLoc_eq T' q' q' h') (toLoc_eq q' gY ρ hρ) L

  have k1 : (F.mapComp' q'.op.toLoc T'.op.toLoc q'.op.toLoc (toLoc_eq T' q' q' h')).hom.toNatTrans.app
        ((F.map gY.op.toLoc).toFunctor.obj N) ≫
      (F.map T'.op.toLoc).toFunctor.map
        ((F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app N) =
      (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app N ≫
        (F.mapComp' ρ.op.toLoc T'.op.toLoc ρ.op.toLoc (toLoc_eq T' ρ ρ hT)).hom.toNatTrans.app N := by
    rw [← cancel_epi ((F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app N),
      Cat.Hom.hom_inv_id_toNatTrans_app_assoc, ← Category.assoc, key N, Category.assoc, ← Functor.map_comp,
      Cat.Hom.hom_inv_id_toNatTrans_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have k2 : (F.map T'.op.toLoc).toFunctor.map
        ((F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app M) ≫
      (F.mapComp' q'.op.toLoc T'.op.toLoc q'.op.toLoc (toLoc_eq T' q' q' h')).inv.toNatTrans.app
        ((F.map gY.op.toLoc).toFunctor.obj M) =
      (F.mapComp' ρ.op.toLoc T'.op.toLoc ρ.op.toLoc (toLoc_eq T' ρ ρ hT)).inv.toNatTrans.app M ≫
        (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app M := by
    rw [← cancel_epi ((F.mapComp' ρ.op.toLoc T'.op.toLoc ρ.op.toLoc (toLoc_eq T' ρ ρ hT)).hom.toNatTrans.app M),
      Cat.Hom.hom_inv_id_toNatTrans_app_assoc, ← Category.assoc, ← key M, Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, k1]
  simp only [Category.assoc]
  rw [k2]

theorem pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃M₃ : F.obj (.mk (op X₃))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ h₁ h₃ = pullHom φ g gf₁ gf₂ h₁ h₂ ≫ pullHom ψ g gf₂ gf₃ h₂ h₃ := by
  simp [pullHom]

theorem pullHom_id' ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (h₁ : g ≫ f₁ = gf₁) :
    pullHom (F := F) (M₁ := M₁) (M₂ := M₁) (f₁ := f₁) (f₂ := f₁) (𝟙 _) g gf₁ gf₁ h₁ h₁ = 𝟙 _ := by
  simp [pullHom]

theorem pullHom_congr ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g g' : Y' ⟶ Y) (hg : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₁' : g' ≫ f₁ = gf₁) (h₂' : g' ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ h₁ h₂ = pullHom φ g' gf₁ gf₂ h₁' h₂' := by
  subst hg; rfl

section mainGeneric

variable {S X₀ P X' S' : C} (q : X₀ ⟶ S) (p₁ p₂ : P ⟶ X₀) (r : P ⟶ S) (hp₁ : p₁ ≫ q = r) (hp₂ : p₂ ≫ q = r)
  {N M : F.obj (.mk (op S))}
  (β : (F.map q.op.toLoc).toFunctor.obj N ≅ (F.map q.op.toLoc).toFunctor.obj M)
  (σ : (F.map r.op.toLoc).toFunctor.obj M ⟶ (F.map r.op.toLoc).toFunctor.obj M)
  (E : pullHom β.hom p₂ r r hp₂ hp₂ = pullHom β.hom p₁ r r hp₁ hp₁ ≫ σ)
  (s : X' ⟶ P) (q' : X' ⟶ S') (gY : S' ⟶ S) (ρ : X' ⟶ S) (hρ : q' ≫ gY = ρ) (hsr : s ≫ r = ρ)
  (T' : X' ⟶ X') (h' : T' ≫ q' = q') (hT : T' ≫ ρ = ρ) (hs₂ : s ≫ p₂ = T' ≫ s ≫ p₁)

include hp₁ hp₂ E hsr hs₂ in

theorem pullHom_translate_eq :
    pullHom (pullHom β.hom (s ≫ p₁) ρ ρ (by rw [Category.assoc, hp₁, hsr]) (by rw [Category.assoc, hp₁, hsr]))
        T' ρ ρ hT hT =
      pullHom β.hom (s ≫ p₁) ρ ρ (by rw [Category.assoc, hp₁, hsr]) (by rw [Category.assoc, hp₁, hsr]) ≫
        pullHom σ s ρ ρ hsr hsr := by
  have hsp₂ : (s ≫ p₂) ≫ q = ρ := by rw [Category.assoc, hp₂, hsr]
  rw [pullHom_pullHom β.hom (s ≫ p₁) ρ ρ T' ρ ρ _ _ hT hT,
    pullHom_congr F β.hom (T' ≫ s ≫ p₁) (s ≫ p₂) hs₂.symm ρ ρ _ _ hsp₂ hsp₂,
    ← pullHom_pullHom β.hom p₂ r r s ρ ρ hp₂ hp₂ hsr hsr, E,
    pullHom_comp F _ σ s ρ ρ ρ hsr hsr hsr,
    pullHom_pullHom β.hom p₁ r r s ρ ρ hp₁ hp₁ hsr hsr]

include hp₁ hp₂ E hsr hs₂ hρ h' hT in

theorem discrepancy_eq :
    ((F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app M ≫
        pullHom β.inv (s ≫ p₁) ρ ρ (by rw [Category.assoc, hp₁, hsr]) (by rw [Category.assoc, hp₁, hsr]) ≫
        (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app N) ≫
      pullHom (F := F) (M₁ := (F.map gY.op.toLoc).toFunctor.obj N) (M₂ := (F.map gY.op.toLoc).toFunctor.obj M)
        (f₁ := q') (f₂ := q')
        ((F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app N ≫
          pullHom β.hom (s ≫ p₁) ρ ρ (by rw [Category.assoc, hp₁, hsr]) (by rw [Category.assoc, hp₁, hsr]) ≫
          (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app M)
        T' q' q' h' h' =
    (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).inv.toNatTrans.app M ≫
      pullHom σ s ρ ρ hsr hsr ≫
      (F.mapComp' gY.op.toLoc q'.op.toLoc ρ.op.toLoc (toLoc_eq q' gY ρ hρ)).hom.toNatTrans.app M := by
  rw [pullHom_mapComp'_conj F gY q' ρ hρ T' h' hT, pullHom_translate_eq F q p₁ p₂ r hp₁ hp₂ β σ E s ρ hsr T' hT hs₂]
  simp only [Category.assoc]
  rw [Cat.Hom.hom_inv_id_toNatTrans_app_assoc, ← Category.assoc (pullHom β.inv _ _ _ _ _),
    ← pullHom_comp F β.inv β.hom (s ≫ p₁) ρ ρ ρ, Iso.inv_hom_id, pullHom_id', Category.id_comp]

end mainGeneric

end Gen

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
  try rfl

theorem mapComp'_inv_app (fg : X ⟶ Z) (hfg : f ≫ g = fg)
    (H : g.op.toLoc ≫ f.op.toLoc = fg.op.toLoc) (M : Z.Modules) :
    ((FF.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc H).inv.toNatTrans.app M) =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫
      eqToHom (show (Scheme.Modules.pullback (f ≫ g)).obj M = (Scheme.Modules.pullback fg).obj M by rw [hfg]) := by
  subst hfg
  simp only [Pseudofunctor.mapComp', Iso.trans_inv, PrelaxFunctor.map₂Iso_inv, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.comp_app, Cat.eqToHom_app, mapComp_inv_app]
  try rfl

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

end unfold

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

section bridge2
variable {X P Z : Scheme.{u}}

theorem pullbackCongr_inv_app' {Y : Scheme.{u}} {g g' : X ⟶ Y} (e : g = g') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app M =
      eqToHom (show (Scheme.Modules.pullback g').obj M = (Scheme.Modules.pullback g).obj M by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

theorem pullHom_eq₂ (p₁ p₂ : P ⟶ X) (L₁ L₂ : X.Modules)
    (φ : (Scheme.Modules.pullback p₁).obj L₁ ⟶ (Scheme.Modules.pullback p₂).obj L₂)
    (g : Z ⟶ P) (gf₁ gf₂ : Z ⟶ X) (hg₁ : g ≫ p₁ = gf₁) (hg₂ : g ≫ p₂ = gf₂) :
    pullHom (F := FF) (M₁ := L₁) (M₂ := L₂) (f₁ := p₁) (f₂ := p₂) φ g gf₁ gf₂ hg₁ hg₂ =
    (Scheme.Modules.pullbackCongr hg₁).inv.app L₁ ≫ (Scheme.Modules.pullbackComp g p₁).inv.app L₁ ≫
      (Scheme.Modules.pullback g).map φ ≫ (Scheme.Modules.pullbackComp g p₂).hom.app L₂ ≫
        (Scheme.Modules.pullbackCongr hg₂).hom.app L₂ := by
  dsimp only [pullHom]
  rw [mapComp'_hom_app g p₁ gf₁ hg₁, mapComp'_inv_app g p₂ gf₂ hg₂, pullbackCongr_hom_app hg₂,
    pullbackCongr_inv_app' hg₁]
  simp only [Category.assoc]
  rfl

end bridge2

section scalar
variable {X X' : Scheme.{u}} {R' : Type u} [CommRing R']

abbrev resTop (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op r

def smulLin (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) : Γ(P, U) →ₗ[Γ(X, U)] Γ(P, U) :=
  DistribSMul.toLinearMap Γ(X, U) Γ(P, U) (resTop r U)

@[scoped simp] theorem smulLin_apply (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) (s : Γ(P, U)) :
    smulLin r P U s = resTop r U • s := rfl

theorem smul_eq (P : X.Modules) (U : (Opens X)ᵒᵖ) (a : X.ringCatSheaf.obj.obj U) (x : P.val.obj U) :
    (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
      (show Γ(X, U.unop) from a) • (show Γ(P, U.unop) from x) := rfl

def scalarEnd (r : Γ(X, ⊤)) (P : X.Modules) : P ⟶ P :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (smulLin r P U.unop).toAddMonoidHom
      naturality := by
        intro U V i
        ext s
        change (resTop r V.unop • (show Γ(P, V.unop) from P.presheaf.map i (show Γ(P, U.unop) from s)) :
            Γ(P, V.unop)) =
          (show Γ(P, V.unop) from P.presheaf.map i (resTop r U.unop • (show Γ(P, U.unop) from s)))
        have hi : i = (i.unop).op := rfl
        rw [hi, Scheme.Modules.map_smul, ← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
        rfl }
    (fun U a x => by
      change resTop r U.unop • (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
        (show Γ(P, U.unop) from (a • (show P.val.obj U from resTop r U.unop • (show Γ(P, U.unop) from x)) :
          P.val.obj U))
      rw [smul_eq, smul_eq, smul_smul, smul_smul, mul_comm])⟩

theorem scalarEnd_app (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) (s : Γ(P, U)) :
    (scalarEnd r P).app U s = resTop r U • s := rfl

theorem app_resTop (g : X' ⟶ X) (u : Γ(X, ⊤)) (U : X.Opens) :
    g.app U (resTop u U) = resTop (g.appTop u) (g ⁻¹ᵁ U) := by
  unfold resTop
  rw [← CategoryTheory.comp_apply, g.naturality]
  rfl

theorem pullback_map_sectionScalar (g : X' ⟶ X) (u : Γ(X, ⊤)) {M : X.Modules} {σ : M ⟶ M}
    (hσ : ∀ (U : X.Opens) (s : Γ(M, U)), σ.app U s = resTop u U • s) :
    ∀ (U : X'.Opens) (s : Γ((Scheme.Modules.pullback g).obj M, U)),
      ((Scheme.Modules.pullback g).map σ).app U s = resTop (g.appTop u) U • s := by
  have key : (Scheme.Modules.pullback g).map σ = scalarEnd (g.appTop u) ((Scheme.Modules.pullback g).obj M) := by
    apply Scheme.Modules.pullback_hom_ext g
    intro U s
    rw [← Scheme.Modules.pullbackLocalSection_app, hσ U s, Scheme.Modules.pullbackLocalSection_smul,
      scalarEnd_app, app_resTop]
  intro U s
  rw [key, scalarEnd_app]

theorem isBaseScalar_conj (f' : X' ⟶ Spec (CommRingCat.of R')) {M M' : X'.Modules} (a : M' ⟶ M) (b : M ⟶ M')
    (hab : a ≫ b = 𝟙 M') {σ : M ⟶ M} {c : R'} (hσ : IsBaseScalar f' σ c) : IsBaseScalar f' (a ≫ σ ≫ b) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, hσ U, Scheme.Modules.Hom.app_smul, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, hab, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

end scalar

section main

variable {X Y P X' Y' : Scheme.{u}} {R' : Type u} [CommRing R']

theorem translateIso_hom_eq_pullHom {q' : X' ⟶ Y'} {T' : X' ⟶ X'} (h' : T' ≫ q' = q') {N' M' : Y'.Modules}
    (γ : (Scheme.Modules.pullback q').obj N' ≅ (Scheme.Modules.pullback q').obj M') :
    (translateIso h' γ).hom =
      pullHom (F := FF) (M₁ := N') (M₂ := M') (f₁ := q') (f₂ := q') γ.hom T' q' q' h' h' := by
  dsimp only [pullHom]
  rw [mapComp'_hom_app T' q' q' h', mapComp'_inv_app T' q' q' h']
  simp only [translateIso, transportIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, pullbackCongr_hom_app, pullbackCongr_inv_app', Category.assoc]
  rfl

theorem transported_hom (q : X ⟶ Y) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (q' : X' ⟶ Y') (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY) :
    ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm).hom =
      (FF.mapComp' gY.op.toLoc q'.op.toLoc (q' ≫ gY).op.toLoc (Gen.toLoc_eq q' gY (q' ≫ gY) rfl)).inv.toNatTrans.app N ≫
        pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q) β.hom gX (q' ≫ gY) (q' ≫ gY) hq hq ≫
        (FF.mapComp' gY.op.toLoc q'.op.toLoc (q' ≫ gY).op.toLoc (Gen.toLoc_eq q' gY (q' ≫ gY) rfl)).hom.toNatTrans.app M := by
  rw [pullHom_eq₂, mapComp'_inv_app q' gY (q' ≫ gY) rfl, mapComp'_hom_app q' gY (q' ≫ gY) rfl]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, pullbackCongr_hom_app,
    pullbackCongr_inv_app', eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc]

theorem transported_inv (q : X ⟶ Y) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (q' : X' ⟶ Y') (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY) :
    ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm).inv =
      (FF.mapComp' gY.op.toLoc q'.op.toLoc (q' ≫ gY).op.toLoc (Gen.toLoc_eq q' gY (q' ≫ gY) rfl)).inv.toNatTrans.app M ≫
        pullHom (F := FF) (M₁ := M) (M₂ := N) (f₁ := q) (f₂ := q) β.inv gX (q' ≫ gY) (q' ≫ gY) hq hq ≫
        (FF.mapComp' gY.op.toLoc q'.op.toLoc (q' ≫ gY).op.toLoc (Gen.toLoc_eq q' gY (q' ≫ gY) rfl)).hom.toNatTrans.app N := by
  rw [pullHom_eq₂, mapComp'_inv_app q' gY (q' ≫ gY) rfl, mapComp'_hom_app q' gY (q' ≫ gY) rfl]
  simp only [Iso.trans_inv, Iso.app_hom, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv, pullbackCongr_hom_app,
    pullbackCongr_inv_app', eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc]

theorem datum_eq (q : X ⟶ Y) (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q) {N M : Y.Modules}
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : (Scheme.Modules.pullback p₁).map β.hom ≫
        (σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app M)) =
      ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom) :
    pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q) β.hom p₂ (p₁ ≫ q) (p₁ ≫ q) hp.symm hp.symm =
      pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q) β.hom p₁ (p₁ ≫ q) (p₁ ≫ q) rfl rfl ≫
        ((Scheme.Modules.pullbackComp p₁ q).inv.app M ≫ σ ≫ (Scheme.Modules.pullbackComp p₁ q).hom.app M) := by
  rw [pullHom_eq₂, pullHom_eq₂]
  simp only [pullbackCongr_hom_app, pullbackCongr_inv_app', eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  have h2 : eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
        rw [hp]) ≫ (Scheme.Modules.pullbackComp p₂ q).inv.app N ≫ (Scheme.Modules.pullback p₂).map β.hom =
      (Scheme.Modules.pullbackComp p₁ q).inv.app N ≫ (Scheme.Modules.pullback p₁).map β.hom ≫ σ ≫
        (Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
          rw [hp]) ≫ (Scheme.Modules.pullbackComp p₂ q).inv.app M := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp p₁ q).hom.app N)]
    simp only [Iso.hom_inv_id_app_assoc]
    simpa only [Category.assoc] using hβ.symm
  have h3 := h2 =≫ ((Scheme.Modules.pullbackComp p₂ q).hom.app M ≫
    eqToHom (show (Scheme.Modules.pullback (p₂ ≫ q)).obj M = (Scheme.Modules.pullback (p₁ ≫ q)).obj M by rw [hp]))
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h3
  exact h3

theorem main (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    {N M : Y.Modules} (u : Γ(P, ⊤))
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : (Scheme.Modules.pullback p₁).map β.hom ≫
        (σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app M)) =
      ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q') (hT' : T' ≫ f' = f')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY)
    (s : X' ⟶ P) (hs₁ : s ≫ p₁ = gX) (hs₂ : s ≫ p₂ = T' ≫ gX)
    (c : R') (hsu : s.appTop u = f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv c)) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      c := by
  have E := datum_eq q p₁ p₂ hp σ β hβ
  subst hs₁
  have hsr : s ≫ p₁ ≫ q = q' ≫ gY := by rw [← Category.assoc, hq]
  have hT : T' ≫ q' ≫ gY = q' ≫ gY := by rw [← Category.assoc, h']
  have hs₂' : s ≫ p₂ = T' ≫ s ≫ p₁ := hs₂
  have D := Gen.discrepancy_eq FF q p₁ p₂ (p₁ ≫ q) rfl hp.symm β _ E s q' gY (q' ≫ gY) rfl hsr T' h' hT hs₂'
  unfold HasValue discrepancy
  rw [Iso.trans_hom, Iso.symm_hom, translateIso_hom_eq_pullHom h', transported_inv q β q' (s ≫ p₁) gY hq,
    transported_hom q β q' (s ≫ p₁) gY hq, D, pullHom_eq₂, Functor.map_comp, Functor.map_comp]

  have hsσ : IsBaseScalar f' ((Scheme.Modules.pullback s).map σ) c := by
    intro U t
    rw [pullback_map_sectionScalar s u hσ U t, hsu]
    rfl
  have key := isBaseScalar_conj f'
    ((FF.mapComp' gY.op.toLoc q'.op.toLoc (q' ≫ gY).op.toLoc (Gen.toLoc_eq q' gY (q' ≫ gY) rfl)).inv.toNatTrans.app M ≫
      (Scheme.Modules.pullbackCongr hsr).inv.app M ≫ (Scheme.Modules.pullbackComp s (p₁ ≫ q)).inv.app M ≫
      (Scheme.Modules.pullback s).map ((Scheme.Modules.pullbackComp p₁ q).inv.app M))
    ((Scheme.Modules.pullback s).map ((Scheme.Modules.pullbackComp p₁ q).hom.app M) ≫
      (Scheme.Modules.pullbackComp s (p₁ ≫ q)).hom.app M ≫ (Scheme.Modules.pullbackCongr hsr).hom.app M ≫
      (FF.mapComp' gY.op.toLoc q'.op.toLoc (q' ≫ gY).op.toLoc (Gen.toLoc_eq q' gY (q' ≫ gY) rfl)).hom.toNatTrans.app M)
    (by
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, Cat.Hom.inv_hom_id_toNatTrans_app])
    hsσ
  simpa only [Category.assoc] using key

end main

end C7G2
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2"

theorem solution
    {X Y P X' Y' : Scheme.{u}} {R' : Type u} [CommRing R'] (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    {N M : Y.Modules} (u : Γ(P, ⊤))
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : (Scheme.Modules.pullback p₁).map β.hom ≫
        (σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app M)) =
      ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q') (hT' : T' ≫ f' = f')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY)
    (s : X' ⟶ P) (hs₁ : s ≫ p₁ = gX) (hs₂ : s ≫ p₂ = T' ≫ gX)
    (c : R') (hsu : s.appTop u = f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv c)) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      c :=
  C7G2.main q p₁ p₂ hp u σ hσ β hβ f' h' hT' gX gY hq s hs₁ hs₂ c hsu

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2"

end S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq (solution)
