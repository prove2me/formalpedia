-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.existsUnique_iso_mapIso_eq_of_hasValue_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b9ea8c7b-93a5-55ee-813e-b39295e304bc

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one

set_option autoImplicit false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Bicategory CategoryTheory.Bicategory Opposite Bicategory.Opposite AlgebraicGeometry.DescentCharacter CategoryTheory.Pseudofunctor CategoryTheory.Bicategory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

universe u

noncomputable section

namespace KcDescAlong

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

theorem pullbackComp_comp_hom_app (T : P ⟶ P) (p : P ⟶ X) (q : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (T ≫ p) q).hom.app M =
      (Scheme.Modules.pullbackComp T p).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback T).map ((Scheme.Modules.pullbackComp p q).hom.app M) ≫
          (Scheme.Modules.pullbackComp T (p ≫ q)).hom.app M ≫
            eqToHom (show (Scheme.Modules.pullback (T ≫ p ≫ q)).obj M =
              (Scheme.Modules.pullback ((T ≫ p) ≫ q)).obj M by rw [Category.assoc]) := by
  have assoc := congrArg (fun α => NatTrans.app α M) (Scheme.Modules.pseudofunctor_associativity T p q)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    eqToHom_app, Functor.comp_obj, Category.id_comp] at assoc
  rw [← Iso.app_inv, Iso.inv_comp_eq, ← Iso.app_inv, ← Functor.mapIso_inv, Iso.inv_comp_eq,
    ← Iso.app_hom, ← Category.assoc, ← Iso.trans_hom, ← Iso.eq_inv_comp] at assoc
  rw [assoc]
  erw [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_hom, Iso.app_inv]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc]

def uIso (T : P ⟶ P) (p₁ : P ⟶ X) (q : X ⟶ Y) (hw : (T ≫ p₁) ≫ q = p₁ ≫ q) (M : Y.Modules) :
    (Scheme.Modules.pullback (T ≫ p₁)).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback (p₁ ≫ q)).obj M :=
  (Scheme.Modules.pullbackComp (T ≫ p₁) q).app M ≪≫
    eqToIso (show (Scheme.Modules.pullback ((T ≫ p₁) ≫ q)).obj M = (Scheme.Modules.pullback (p₁ ≫ q)).obj M by
      rw [hw])

theorem key (T : P ⟶ P) (p₁ : P ⟶ X) (q : X ⟶ Y)
    (h : T ≫ p₁ ≫ q = p₁ ≫ q) (hw : (T ≫ p₁) ≫ q = p₁ ≫ q) (M : Y.Modules) :
    ((Scheme.Modules.pullbackComp T p₁).app ((Scheme.Modules.pullback q).obj M)).symm ≪≫
      (Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullbackComp p₁ q).app M) ≪≫ transportIso h M =
    uIso T p₁ q hw M := by
  ext : 1
  have e1 := pullbackComp_comp_hom_app T p₁ q M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, transportIso, uIso,
    eqToIso.hom, pullbackCongr_hom_app]
  rw [e1]
  simp only [Category.assoc, eqToHom_trans]

theorem mapIso_mapIso_eq (T : P ⟶ P) (p₁ : P ⟶ X) {A B : X.Modules} (β : A ≅ B) :
    (Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullback p₁).mapIso β) =
      (Scheme.Modules.pullbackComp T p₁).app A ≪≫ (Scheme.Modules.pullback (T ≫ p₁)).mapIso β ≪≫
        ((Scheme.Modules.pullbackComp T p₁).app B).symm := by
  ext : 1
  have nat := (Scheme.Modules.pullbackComp T p₁).hom.naturality β.hom
  simp only [Functor.comp_map] at nat
  dsimp only [Functor.comp_obj] at nat
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
  exact ((Category.assoc _ _ _).symm.trans
    ((Iso.comp_inv_eq ((Scheme.Modules.pullbackComp T p₁).app B)).mpr nat.symm)).symm

theorem translateIso_transfer (T : P ⟶ P) (p₁ : P ⟶ X) (q : X ⟶ Y)
    (h : T ≫ p₁ ≫ q = p₁ ≫ q) (hw : (T ≫ p₁) ≫ q = p₁ ≫ q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    translateIso h (((Scheme.Modules.pullbackComp p₁ q).app N).symm ≪≫ (Scheme.Modules.pullback p₁).mapIso β ≪≫
        (Scheme.Modules.pullbackComp p₁ q).app M) =
      (uIso T p₁ q hw N).symm ≪≫ (Scheme.Modules.pullback (T ≫ p₁)).mapIso β ≪≫ uIso T p₁ q hw M := by
  have KM := key T p₁ q h hw M
  have KN := key T p₁ q h hw N

  have KN' : (transportIso h N).symm ≪≫ (Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullbackComp p₁ q).app N).symm
      ≪≫ (Scheme.Modules.pullbackComp T p₁).app ((Scheme.Modules.pullback q).obj N) = (uIso T p₁ q hw N).symm := by
    rw [← KN]
    ext : 1
    simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Functor.mapIso_symm, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom]
  simp only [translateIso, Functor.mapIso_trans, Iso.trans_assoc]
  dsimp only [Functor.comp_obj]
  rw [mapIso_mapIso_eq T p₁ β]
  rw [← KM, ← KN']
  dsimp only [Functor.comp_obj]
  simp only [Iso.trans_assoc, Functor.mapIso_symm, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc]

theorem trans_canonIso_eq_of_hasValue_one {R : Type u} [CommRing R] (f : P ⟶ Spec (CommRingCat.of R))
    (T : P ⟶ P) (p₁ : P ⟶ X) (q : X ⟶ Y)
    (h : T ≫ p₁ ≫ q = p₁ ≫ q) (hw : (T ≫ p₁) ≫ q = p₁ ≫ q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : HasValue f h (((Scheme.Modules.pullbackComp p₁ q).app N).symm ≪≫ (Scheme.Modules.pullback p₁).mapIso β ≪≫
        (Scheme.Modules.pullbackComp p₁ q).app M) 1) :
    (Scheme.Modules.pullback p₁).mapIso β ≪≫ canonIso q M (p₁ ≫ q) p₁ (T ≫ p₁) rfl hw =
      canonIso q N (p₁ ≫ q) p₁ (T ≫ p₁) rfl hw ≪≫ (Scheme.Modules.pullback (T ≫ p₁)).mapIso β := by

  set β' := ((Scheme.Modules.pullbackComp p₁ q).app N).symm ≪≫ (Scheme.Modules.pullback p₁).mapIso β ≪≫
        (Scheme.Modules.pullbackComp p₁ q).app M with hβ'def
  have hdisc : (discrepancy h β').hom = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    rw [hβ U s, baseSection_one, one_smul, Scheme.Modules.Hom.id_app]
    rfl
  have hinv : translateIso h β' = β' := by
    ext : 1
    have e : β'.inv ≫ (translateIso h β').hom = 𝟙 _ := hdisc
    rw [← cancel_epi β'.inv, e, Iso.inv_hom_id]
  rw [translateIso_transfer T p₁ q h hw β] at hinv

  have canonM : canonIso q M (p₁ ≫ q) p₁ (T ≫ p₁) rfl hw =
      (Scheme.Modules.pullbackComp p₁ q).app M ≪≫ (uIso T p₁ q hw M).symm := by
    ext : 1
    simp only [canonIso, uIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Iso.app_hom,
      Iso.app_inv, Iso.symm_inv, Category.assoc]
  have canonN : canonIso q N (p₁ ≫ q) p₁ (T ≫ p₁) rfl hw =
      (Scheme.Modules.pullbackComp p₁ q).app N ≪≫ (uIso T p₁ q hw N).symm := by
    ext : 1
    simp only [canonIso, uIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Iso.app_hom,
      Iso.app_inv, Iso.symm_inv, Category.assoc]
  rw [canonM, canonN]
  have h2 : (Scheme.Modules.pullback (T ≫ p₁)).mapIso β = uIso T p₁ q hw N ≪≫ β' ≪≫ (uIso T p₁ q hw M).symm := by
    rw [← hinv]
    simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
      Iso.symm_self_id, Iso.refl_trans]
  rw [h2, hβ'def]
  dsimp only [Functor.comp_obj]
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
      Iso.symm_self_id, Iso.refl_trans]

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
  {S X₀ P₀ : C} (q : X₀ ⟶ S) (p₁ p₂ : P₀ ⟶ X₀) (w : p₁ ≫ q = p₂ ≫ q)
  (hlim : IsLimit (PullbackCone.mk p₁ p₂ w))

abbrev gsq : ChosenPullback q q :=
  { pullback := P₀, p₁ := p₁, p₂ := p₂, condition := w, isLimit := hlim, p := p₁ ≫ q, hp₁ := rfl }

theorem generic_comm_all (sq₃ : ChosenPullback₃ (gsq q p₁ p₂ w hlim) (gsq q p₁ p₂ w hlim) (gsq q p₁ p₂ w hlim))
    {N M : F.obj (.mk (op S))}
    (βh : (F.map q.op.toLoc).toFunctor.obj N ⟶ (F.map q.op.toLoc).toFunctor.obj M)
    (commh : (F.map p₁.op.toLoc).toFunctor.map βh ≫
        (DescentData.ofObj (F := F) (f := fun _ : Unit => q) M).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm =
      (DescentData.ofObj (F := F) (f := fun _ : Unit => q) N).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm ≫ (F.map p₂.op.toLoc).toFunctor.map βh)
    {Z : C} (r : Z ⟶ S) (g₁ g₂ : Z ⟶ X₀) (hg₁ : g₁ ≫ q = r) (hg₂ : g₂ ≫ q = r) :
    (F.map g₁.op.toLoc).toFunctor.map βh ≫
        (DescentData.ofObj (F := F) (f := fun _ : Unit => q) M).hom r (i₁ := ()) (i₂ := ()) g₁ g₂ hg₁ hg₂ =
      (DescentData.ofObj (F := F) (f := fun _ : Unit => q) N).hom r (i₁ := ()) (i₂ := ()) g₁ g₂ hg₁ hg₂ ≫
        (F.map g₂.op.toLoc).toFunctor.map βh := by
  let φh : DescentData'.ofDescentData (fun _ _ => gsq q p₁ p₂ w hlim) (fun _ _ _ => sq₃)
        ((F.toDescentData (fun _ : Unit => q)).obj N) ⟶
      DescentData'.ofDescentData (fun _ _ => gsq q p₁ p₂ w hlim) (fun _ _ _ => sq₃)
        ((F.toDescentData (fun _ : Unit => q)).obj M) :=
    { hom := fun _ => βh
      comm := fun i j => by cases i; cases j; exact commh }
  have H := DescentData'.comm φh r (i₁ := ()) (i₂ := ()) g₁ g₂ hg₁ hg₂
  rw [DescentData'.pullHom'_ofDescentData_hom, DescentData'.pullHom'_ofDescentData_hom] at H
  exact H

theorem generic_existsUnique (sq₃ : ChosenPullback₃ (gsq q p₁ p₂ w hlim) (gsq q p₁ p₂ w hlim) (gsq q p₁ p₂ w hlim))
    {N M : F.obj (.mk (op S))}
    (β : (F.map q.op.toLoc).toFunctor.obj N ≅ (F.map q.op.toLoc).toFunctor.obj M)
    (cN : (F.map p₁.op.toLoc).toFunctor.obj ((F.map q.op.toLoc).toFunctor.obj N) ⟶
      (F.map p₂.op.toLoc).toFunctor.obj ((F.map q.op.toLoc).toFunctor.obj N))
    (cM : (F.map p₁.op.toLoc).toFunctor.obj ((F.map q.op.toLoc).toFunctor.obj M) ⟶
      (F.map p₂.op.toLoc).toFunctor.obj ((F.map q.op.toLoc).toFunctor.obj M))
    (hcN : (DescentData.ofObj (F := F) (f := fun _ : Unit => q) N).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm = cN)
    (hcM : (DescentData.ofObj (F := F) (f := fun _ : Unit => q) M).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm = cM)
    (comm : (F.map p₁.op.toLoc).toFunctor.map β.hom ≫ cM = cN ≫ (F.map p₂.op.toLoc).toFunctor.map β.hom)
    (bijNM : Function.Bijective ((F.toDescentData (fun _ : Unit => q)).map : (N ⟶ M) → _))
    (bijMN : Function.Bijective ((F.toDescentData (fun _ : Unit => q)).map : (M ⟶ N) → _))
    (bijNN : Function.Bijective ((F.toDescentData (fun _ : Unit => q)).map : (N ⟶ N) → _))
    (bijMM : Function.Bijective ((F.toDescentData (fun _ : Unit => q)).map : (M ⟶ M) → _)) :
    ∃! α : N ≅ M, (F.map q.op.toLoc).toFunctor.mapIso α = β := by
  have commh : (F.map p₁.op.toLoc).toFunctor.map β.hom ≫
        (DescentData.ofObj (F := F) (f := fun _ : Unit => q) M).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm =
      (DescentData.ofObj (F := F) (f := fun _ : Unit => q) N).hom (p₁ ≫ q) (i₁ := ()) (i₂ := ()) p₁ p₂
          rfl w.symm ≫ (F.map p₂.op.toLoc).toFunctor.map β.hom := by
    rw [hcN, hcM]; exact comm
  let Ψ : (F.toDescentData (fun _ : Unit => q)).obj N ≅ (F.toDescentData (fun _ : Unit => q)).obj M :=
    DescentData.isoMk (fun _ => β) (fun Z r i₁ i₂ g₁ g₂ hg₁ hg₂ => by
      cases i₁; cases i₂
      exact generic_comm_all F q p₁ p₂ w hlim sq₃ β.hom commh r g₁ g₂ hg₁ hg₂)
  obtain ⟨a, ha⟩ := bijNM.2 Ψ.hom
  obtain ⟨b, hb⟩ := bijMN.2 Ψ.inv
  have ha' : (F.map q.op.toLoc).toFunctor.map a = β.hom := by
    have := congrArg (fun ψ => DescentData.Hom.hom ψ ()) ha
    simp only [Pseudofunctor.toDescentData_map_hom, DescentData.isoMk_hom_hom, Ψ] at this
    exact this
  have hab : a ≫ b = 𝟙 N := by
    apply bijNN.1
    rw [Functor.map_comp, ha, hb, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have hba : b ≫ a = 𝟙 M := by
    apply bijMM.1
    rw [Functor.map_comp, ha, hb, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  refine ⟨⟨a, b, hab, hba⟩, ?_, ?_⟩
  · ext : 1
    exact ha'
  · intro α' hα'
    ext : 1
    apply bijNM.1
    rw [ha]
    ext i
    cases i
    simp only [Pseudofunctor.toDescentData_map_hom, DescentData.isoMk_hom_hom, Ψ]
    exact congrArg Iso.hom hα'

end generic

section main
variable {X Y P : Scheme.{u}} (q : X ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
  (p₁ p₂ : P ⟶ X) (hP : IsPullback p₁ p₂ q q)

def sq₃ : ChosenPullback₃ (gsq q p₁ p₂ hP.w hP.isLimit) (gsq q p₁ p₂ hP.w hP.isLimit) (gsq q p₁ p₂ hP.w hP.isLimit) :=
  { chosenPullback :=
      { pullback := Limits.pullback p₂ p₁, p₁ := Limits.pullback.fst p₂ p₁, p₂ := Limits.pullback.snd p₂ p₁,
        condition := Limits.pullback.condition, isLimit := (IsPullback.of_hasPullback p₂ p₁).isLimit,
        p := Limits.pullback.fst p₂ p₁ ≫ p₂, hp₁ := rfl }
    l := (ChosenPullback.LiftStruct.nonempty
            (show (Limits.pullback.fst p₂ p₁ ≫ p₁) ≫ q = (Limits.pullback.snd p₂ p₁ ≫ p₂) ≫ q by
              rw [Category.assoc, Category.assoc, hP.w, Limits.pullback.condition_assoc, hP.w])
            (show (Limits.pullback.fst p₂ p₁ ≫ p₁) ≫ q = Limits.pullback.fst p₂ p₁ ≫ p₁ ≫ q by
              rw [Category.assoc])).some }

theorem existsUnique_of_comm {N M : Y.Modules} (hN : Scheme.Modules.IsInvertible N) (hM : Scheme.Modules.IsInvertible M)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (comm : (Scheme.Modules.pullback p₁).map β.hom ≫ (canonIso q M (p₁ ≫ q) p₁ p₂ rfl hP.w.symm).hom =
      (canonIso q N (p₁ ≫ q) p₁ p₂ rfl hP.w.symm).hom ≫ (Scheme.Modules.pullback p₂).map β.hom) :
    ∃! α : N ≅ M, (Scheme.Modules.pullback q).mapIso α = β :=
  generic_existsUnique FF q p₁ p₂ hP.w hP.isLimit (sq₃ q p₁ p₂ hP) β
    (canonIso q N (p₁ ≫ q) p₁ p₂ rfl hP.w.symm).hom (canonIso q M (p₁ ≫ q) p₁ p₂ rfl hP.w.symm).hom
    (ofObj_hom_eq q N (p₁ ≫ q) p₁ p₂ rfl hP.w.symm) (ofObj_hom_eq q M (p₁ ≫ q) p₁ p₂ rfl hP.w.symm) comm
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q N M hN hM)
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q M N hM hN)
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q N N hN hN)
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q M M hM hM)

end main

end KcDescAlong

end

theorem solution
    {X Y P : Scheme.{u}} {R : Type u} [CommRing R] (f : P ⟶ Spec (CommRingCat.of R))
    (q : X ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (p₁ p₂ : P ⟶ X) (hP : IsPullback p₁ p₂ q q) (T : P ⟶ P) (hT : T ≫ p₁ = p₂)
    (h : T ≫ p₁ ≫ q = p₁ ≫ q) {N M : Y.Modules}
    (hN : Scheme.Modules.IsInvertible N) (hM : Scheme.Modules.IsInvertible M)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : HasValue f h
      (((Scheme.Modules.pullbackComp p₁ q).app N).symm ≪≫ (Scheme.Modules.pullback p₁).mapIso β ≪≫
        (Scheme.Modules.pullbackComp p₁ q).app M) 1) :
    ∃! α : N ≅ M, (Scheme.Modules.pullback q).mapIso α = β := by
  subst hT
  have comm := KcDescAlong.trans_canonIso_eq_of_hasValue_one f T p₁ q h hP.w.symm β hβ
  have commh := congrArg Iso.hom comm
  simp only [Iso.trans_hom, Functor.mapIso_hom] at commh
  exact KcDescAlong.existsUnique_of_comm q p₁ (T ≫ p₁) hP hN hM β commh

end S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one (solution)
