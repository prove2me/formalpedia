-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_finite_faithfullyFlat_of_bijective_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/638271a5-639c-5dca-9c9c-e781df828924

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open NeronModelInfra AlgebraicGeometry.RelPicard

noncomputable section
namespace ExZar

section Coherence
variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

theorem pullbackComp_paste (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    Functor.whiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g).hom ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (Scheme.Modules.pullbackComp g h).hom (Scheme.Modules.pullback f) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom ≫ eqToHom (by rw [Category.assoc]) := by
  have H0 := Scheme.Modules.pseudofunctor_associativity f g h
  have H1 : Functor.whiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g).hom ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫ (Functor.isoWhiskerRight (Scheme.Modules.pullbackComp g h) (Scheme.Modules.pullback f)).hom ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom ≫
        ((Scheme.Modules.pullbackComp f (g ≫ h)).inv ≫ Functor.whiskerRight (Scheme.Modules.pullbackComp g h).inv (Scheme.Modules.pullback f) ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g).hom ≫
            (Scheme.Modules.pullbackComp (f ≫ g) h).hom) := by
    rw [Iso.hom_inv_id_assoc, Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id,
      Functor.whiskerRight_id', Category.id_comp, Iso.inv_hom_id_assoc]
  rw [H0] at H1
  exact H1

theorem pullbackComp_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (M : X₃.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫ (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  have H := NatTrans.congr_app (pullbackComp_paste f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Category.id_comp, eqToHom_app] at H
  exact H

def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) : Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback m :=
  Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (Scheme.Modules.pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp [τ, Scheme.Modules.pullbackCongr]

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (Scheme.Modules.pullbackComp f g).inv.app M := by
  subst e
  simp [τ, Scheme.Modules.pullbackCongr]

theorem τ_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (fg : X₀ ⟶ X₂) (gh : X₁ ⟶ X₃) (m : X₀ ⟶ X₃)
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = m) (M : X₃.Modules) :
    (τ f g fg e₁).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (τ fg h m e₃).hom.app M =
      (Scheme.Modules.pullback f).map ((τ g h gh e₂).hom.app M) ≫ (τ f gh m (by rw [← e₂, ← Category.assoc, e₁, e₃])).hom.app M := by
  subst e₁ e₂ e₃
  simp only [τ_hom_app, eqToHom_refl, Category.comp_id]
  rw [pullbackComp_paste_app]

def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback k ⋙ Scheme.Modules.pullback h :=
  Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr e ≪≫ (Scheme.Modules.pullbackComp h k).symm

theorem route {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (sqIso E).hom.app ((Scheme.Modules.pullback b).obj M) ≫ (Scheme.Modules.pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map ((τ a b d e).hom.app M) ≫ (sqIso H).hom.app M :=
  AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app a b d e s₀ s₁ s r p m G E F H M

end Coherence

abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

section Bridge
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem MOD_mapComp'_eq_mapComp_app {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d) (M : MOD.obj a) :
    (MOD.mapComp' u v (u ≫ v) rfl).hom.toNatTrans.app M = (MOD.mapComp u v).hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem MOD_mapComp'_eq_mapComp_inv_app {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d)
    (M : MOD.obj a) :
    (MOD.mapComp' u v (u ≫ v) rfl).inv.toNatTrans.app M = (MOD.mapComp u v).inv.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem MOD_mapComp'_hom_app (fg : X ⟶ Z) (h : f ≫ g = fg) (L : Z.Modules) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
      (τ f g fg h).inv.app L := by
  subst h
  rw [τ_inv_app]
  simp only [eqToHom_refl, Category.id_comp]
  exact MOD_mapComp'_eq_mapComp_app g.op.toLoc f.op.toLoc L

theorem MOD_mapComp'_inv_app (fg : X ⟶ Z) (h : f ≫ g = fg) (L : Z.Modules) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
      (τ f g fg h).hom.app L := by
  subst h
  rw [τ_hom_app]
  simp only [eqToHom_refl, Category.comp_id]
  exact MOD_mapComp'_eq_mapComp_inv_app g.op.toLoc f.op.toLoc L

end Bridge

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat in

theorem pullHom_MOD {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (F := MOD) (M₁ := M₁) (M₂ := M₂) φ g gf₁ gf₂ hgf₁ hgf₂ =
      ((τ g f₁ gf₁ hgf₁).inv.app M₁ ≫ (Scheme.Modules.pullback g).map φ ≫ (τ g f₂ gf₂ hgf₂).hom.app M₂ :) :=
  congrArg₂ (fun a b => a ≫ (Scheme.Modules.pullback g).map φ ≫ b)
    (MOD_mapComp'_hom_app g f₁ gf₁ hgf₁ M₁) (MOD_mapComp'_inv_app g f₂ gf₂ hgf₂ M₂)

def pullHomIso {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (Scheme.Modules.pullback gf₁).obj M₁ ≅ (Scheme.Modules.pullback gf₂).obj M₂ :=
  ((τ g f₁ gf₁ hgf₁).app M₁).symm ≪≫ (Scheme.Modules.pullback g).mapIso Φ ≪≫ (τ g f₂ gf₂ hgf₂).app M₂

theorem pullHomIso_hom' {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHomIso Φ g gf₁ gf₂ hgf₁ hgf₂).hom =
      (τ g f₁ gf₁ hgf₁).inv.app M₁ ≫ (Scheme.Modules.pullback g).map Φ.hom ≫ (τ g f₂ gf₂ hgf₂).hom.app M₂ :=
  rfl

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat in

theorem pullHomIso_hom {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHomIso Φ g gf₁ gf₂ hgf₁ hgf₂).hom =
      pullHom (F := MOD) (M₁ := M₁) (M₂ := M₂) Φ.hom g gf₁ gf₂ hgf₁ hgf₂ :=
  (pullHom_MOD Φ.hom g gf₁ gf₂ hgf₁ hgf₂).symm

def pullHomMap {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (Scheme.Modules.pullback gf₁).obj M₁ ⟶ (Scheme.Modules.pullback gf₂).obj M₂ :=
  (τ g f₁ gf₁ hgf₁).inv.app M₁ ≫ (Scheme.Modules.pullback g).map φ ≫ (τ g f₂ gf₂ hgf₂).hom.app M₂

theorem pullHomIso_hom_eq_pullHomMap {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHomIso Φ g gf₁ gf₂ hgf₁ hgf₂).hom = pullHomMap Φ.hom g gf₁ gf₂ hgf₁ hgf₂ :=
  rfl

def toMOD {X₁ X₂ Y : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂) :
    (MOD.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (MOD.map f₂.op.toLoc).toFunctor.obj M₂ := φ

theorem toMOD_eq {X₁ X₂ Y : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂) :
    toMOD f₁ f₂ φ = φ := rfl

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat in

theorem pullHom_toMOD {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (F := MOD) (M₁ := M₁) (M₂ := M₂) (toMOD f₁ f₂ φ) g gf₁ gf₂ hgf₁ hgf₂ =
      toMOD gf₁ gf₂ (pullHomMap φ g gf₁ gf₂ hgf₁ hgf₂) :=
  pullHom_MOD φ g gf₁ gf₂ hgf₁ hgf₂

theorem toMOD_comp {X₁ X₂ X₃ Y : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} {M₃ : X₃.Modules}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (f₃ : Y ⟶ X₃)
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (ψ : (Scheme.Modules.pullback f₂).obj M₂ ⟶ (Scheme.Modules.pullback f₃).obj M₃) :
    toMOD f₁ f₂ φ ≫ toMOD f₂ f₃ ψ = toMOD f₁ f₃ (φ ≫ ψ) :=
  rfl

theorem toMOD_congr {X₁ X₂ Y : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    {φ ψ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂} (h : φ = ψ) :
    toMOD f₁ f₂ φ = toMOD f₁ f₂ ψ :=
  congrArg _ h

theorem toMOD_id {X₁ Y : Scheme.{u}} {M₁ : X₁.Modules} (f₁ : Y ⟶ X₁) :
    toMOD f₁ f₁ (𝟙 ((Scheme.Modules.pullback f₁).obj M₁)) = 𝟙 _ :=
  rfl

def isoOfMOD {X Y : Scheme.{u}} {g : X ⟶ Y} {L : Y.Modules} {N : X.Modules}
    (e : @Iso (MOD.obj (.mk (op X))) _ ((MOD.map g.op.toLoc).toFunctor.obj L) N) :
    (Scheme.Modules.pullback g).obj L ≅ N := e

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat in

theorem MOD_pullHom_eq_id_of_iso {X₁ Y W : Scheme.{u}} {M₁ : X₁.Modules} {a₁ a₂ : Y ⟶ X₁}
    (Φ : (Scheme.Modules.pullback a₁).obj M₁ ≅ (Scheme.Modules.pullback a₂).obj M₁) (p : W ⟶ Y) (q : W ⟶ X₁)
    (h₁ : p ≫ a₁ = q) (h₂ : p ≫ a₂ = q) (H : pullHomIso Φ p q q h₁ h₂ = Iso.refl _) :
    pullHom (F := MOD) (M₁ := M₁) (M₂ := M₁) Φ.hom p q q h₁ h₂ = 𝟙 _ := by
  have E' := congrArg Iso.hom H
  rw [pullHomIso_hom] at E'
  exact E'

section PlainDescent
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

theorem pullHomMap_comp_of {X₁ X₂ X₃ Y₁₂ Y₂₃ Y₁₃ W : Scheme.{u}}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules} {M₃ : X₃.Modules}
    {a₁ : Y₁₂ ⟶ X₁} {a₂ : Y₁₂ ⟶ X₂} {b₂ : Y₂₃ ⟶ X₂} {b₃ : Y₂₃ ⟶ X₃} {c₁ : Y₁₃ ⟶ X₁} {c₃ : Y₁₃ ⟶ X₃}
    (Φ₁₂ : (Scheme.Modules.pullback a₁).obj M₁ ≅ (Scheme.Modules.pullback a₂).obj M₂)
    (Φ₂₃ : (Scheme.Modules.pullback b₂).obj M₂ ≅ (Scheme.Modules.pullback b₃).obj M₃)
    (Φ₁₃ : (Scheme.Modules.pullback c₁).obj M₁ ≅ (Scheme.Modules.pullback c₃).obj M₃)
    (p₁₂ : W ⟶ Y₁₂) (p₂₃ : W ⟶ Y₂₃) (p₁₃ : W ⟶ Y₁₃) (q₁ : W ⟶ X₁) (q₂ : W ⟶ X₂) (q₃ : W ⟶ X₃)
    (h₁ : p₁₂ ≫ a₁ = q₁) (h₂ : p₁₂ ≫ a₂ = q₂) (h₃ : p₂₃ ≫ b₂ = q₂) (h₄ : p₂₃ ≫ b₃ = q₃)
    (h₅ : p₁₃ ≫ c₁ = q₁) (h₆ : p₁₃ ≫ c₃ = q₃)
    (hc : pullHomIso Φ₁₂ p₁₂ q₁ q₂ h₁ h₂ ≪≫ pullHomIso Φ₂₃ p₂₃ q₂ q₃ h₃ h₄ = pullHomIso Φ₁₃ p₁₃ q₁ q₃ h₅ h₆) :
    pullHomMap Φ₁₂.hom p₁₂ q₁ q₂ h₁ h₂ ≫ pullHomMap Φ₂₃.hom p₂₃ q₂ q₃ h₃ h₄ = pullHomMap Φ₁₃.hom p₁₃ q₁ q₃ h₅ h₆ := by
  have H := congrArg Iso.hom hc
  rw [Iso.trans_hom, pullHomIso_hom_eq_pullHomMap, pullHomIso_hom_eq_pullHomMap, pullHomIso_hom_eq_pullHomMap] at H
  exact H

variable {ι : Type w} {S : Scheme.{u}} {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ S)
  (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
  (obj : ∀ i, (X i).Modules)
  (φ : ∀ i j, (Scheme.Modules.pullback (sq i j).p₁).obj (obj i) ≅ (Scheme.Modules.pullback (sq i j).p₂).obj (obj j))

def homG (i j : ι) :
    (MOD.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶ (MOD.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j) :=
  toMOD (sq i j).p₁ (sq i j).p₂ (φ i j).hom

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat in

theorem pullHom_homG (i j : ι) {W : Scheme.{u}} (p : W ⟶ (sq i j).pullback) (q₁ : W ⟶ X i) (q₂ : W ⟶ X j)
    (h₁ : p ≫ (sq i j).p₁ = q₁) (h₂ : p ≫ (sq i j).p₂ = q₂) :
    pullHom (F := MOD) (homG g sq obj φ i j) p q₁ q₂ h₁ h₂ =
      toMOD q₁ q₂ (pullHomMap (φ i j).hom p q₁ q₂ h₁ h₂) :=
  pullHom_toMOD (φ i j).hom p q₁ q₂ h₁ h₂

variable (δ : ∀ i, X i ⟶ (sq i i).pullback) (hδ₁ : ∀ i, δ i ≫ (sq i i).p₁ = 𝟙 _) (hδ₂ : ∀ i, δ i ≫ (sq i i).p₂ = 𝟙 _)
  (hself : ∀ i (h₁ : δ i ≫ (sq i i).p₁ = 𝟙 _) (h₂ : δ i ≫ (sq i i).p₂ = 𝟙 _),
    pullHomIso (φ i i) (δ i) (𝟙 _) (𝟙 _) h₁ h₂ = Iso.refl _)
  (hcomp : ∀ i j k (h₁ : (sq₃ i j k).p₁₂ ≫ (sq i j).p₁ = (sq₃ i j k).p₁)
    (h₂ : (sq₃ i j k).p₁₂ ≫ (sq i j).p₂ = (sq₃ i j k).p₂) (h₃ : (sq₃ i j k).p₂₃ ≫ (sq j k).p₁ = (sq₃ i j k).p₂)
    (h₄ : (sq₃ i j k).p₂₃ ≫ (sq j k).p₂ = (sq₃ i j k).p₃) (h₅ : (sq₃ i j k).p₁₃ ≫ (sq i k).p₁ = (sq₃ i j k).p₁)
    (h₆ : (sq₃ i j k).p₁₃ ≫ (sq i k).p₂ = (sq₃ i j k).p₃),
    pullHomIso (φ i j) (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂ h₁ h₂ ≪≫
      pullHomIso (φ j k) (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃ h₃ h₄ =
    pullHomIso (φ i k) (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃ h₅ h₆)

def dataG : MOD.DescentData' (f := g) sq sq₃ where
  obj := obj
  hom := homG g sq obj φ
  pullHom'_hom_self i := by
    rw [DescentData'.pullHom'_eq_pullHom (F := MOD) (f := g) (sq := sq) (obj := obj) (obj' := obj) (homG g sq obj φ)
      (g i) (𝟙 (X i)) (𝟙 (X i)) (δ i) _ _ (hδ₁ i) (hδ₂ i)]
    exact MOD_pullHom_eq_id_of_iso (φ i i) (δ i) (𝟙 _) _ _ (hself i _ _)
  pullHom'_hom_comp i j k := by
    rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (sq₃ := sq₃) (hom := homG g sq obj φ) i j k,
      DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (sq₃ := sq₃) (hom := homG g sq obj φ) i j k,
      DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (sq₃ := sq₃) (hom := homG g sq obj φ) i j k,
      pullHom_homG, pullHom_homG, pullHom_homG, toMOD_comp]
    exact congrArg (toMOD (sq₃ i j k).p₁ (sq₃ i j k).p₃)
      (pullHomMap_comp_of (φ i j) (φ j k) (φ i k) (sq₃ i j k).p₁₂ (sq₃ i j k).p₂₃ (sq₃ i j k).p₁₃
        (sq₃ i j k).p₁ (sq₃ i j k).p₂ (sq₃ i j k).p₃ _ _ _ _ _ _ (hcomp i j k _ _ _ _ _ _))

theorem dataG_obj (i : ι) : (dataG g sq sq₃ obj φ δ hδ₁ hδ₂ hself hcomp).obj i = obj i := rfl

include δ hδ₁ hδ₂ hself hcomp in

theorem exists_iso_of_plainDescent [(MOD.toDescentData g).IsEquivalence] :
    ∃ L : S.Modules, ∀ i, Nonempty ((Scheme.Modules.pullback (g i)).obj L ≅ obj i) := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L : S.Modules, Nonempty ((MOD.toDescentData g).obj L ≅
      (DescentData'.toDescentDataFunctor MOD sq sq₃).obj (dataG g sq sq₃ obj φ δ hδ₁ hδ₂ hself hcomp)) :=
    ⟨_, ⟨(MOD.toDescentData g).objObjPreimageIso _⟩⟩
  refine ⟨L, fun i => ⟨isoOfMOD (X := X i) (Y := S) (g := g i) (L := L) (N := obj i)
    ⟨e.hom.hom i, e.inv.hom i,
      (DescentData.comp_hom e.hom e.inv i).symm.trans
        ((congrArg (fun ψ => DescentData.Hom.hom ψ i) e.hom_inv_id).trans (DescentData.id_hom _ i)),
      (DescentData.comp_hom e.inv e.hom i).symm.trans
        ((congrArg (fun ψ => DescentData.Hom.hom ψ i) e.inv_hom_id).trans (DescentData.id_hom _ i))⟩⟩⟩

end PlainDescent

section PlainDescentFF
open CategoryTheory.Pseudofunctor

theorem exists_iso_of_plainDescent_ff {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (sq : ∀ _ _ : Unit, ChosenPullback q q) (sq₃ : ∀ i j k : Unit, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (obj : Unit → Y'.Modules) (hobj : ∀ i, Scheme.Modules.IsInvertible (obj i))
    (φ : ∀ i j, (Scheme.Modules.pullback (sq i j).p₁).obj (obj i) ≅ (Scheme.Modules.pullback (sq i j).p₂).obj (obj j))
    (δ : ∀ i, Y' ⟶ (sq i i).pullback) (hδ₁ : ∀ i, δ i ≫ (sq i i).p₁ = 𝟙 _) (hδ₂ : ∀ i, δ i ≫ (sq i i).p₂ = 𝟙 _)
    (hself : ∀ i (h₁ : δ i ≫ (sq i i).p₁ = 𝟙 _) (h₂ : δ i ≫ (sq i i).p₂ = 𝟙 _),
      pullHomIso (φ i i) (δ i) (𝟙 _) (𝟙 _) h₁ h₂ = Iso.refl _)
    (hcomp : ∀ i j k (h₁ : (sq₃ i j k).p₁₂ ≫ (sq i j).p₁ = (sq₃ i j k).p₁)
      (h₂ : (sq₃ i j k).p₁₂ ≫ (sq i j).p₂ = (sq₃ i j k).p₂) (h₃ : (sq₃ i j k).p₂₃ ≫ (sq j k).p₁ = (sq₃ i j k).p₂)
      (h₄ : (sq₃ i j k).p₂₃ ≫ (sq j k).p₂ = (sq₃ i j k).p₃) (h₅ : (sq₃ i j k).p₁₃ ≫ (sq i k).p₁ = (sq₃ i j k).p₁)
      (h₆ : (sq₃ i j k).p₁₃ ≫ (sq i k).p₂ = (sq₃ i j k).p₃),
      pullHomIso (φ i j) (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂ h₁ h₂ ≪≫
        pullHomIso (φ j k) (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃ h₃ h₄ =
      pullHomIso (φ i k) (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃ h₅ h₆) :
    ∃ L : Y.Modules, Scheme.Modules.IsInvertible L ∧
      ∀ i, Nonempty ((Scheme.Modules.pullback q).obj L ≅ obj i) := by
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective q
      ((DescentData'.toDescentDataFunctor MOD sq sq₃).obj
        (dataG (fun _ : Unit => q) sq sq₃ obj φ δ hδ₁ hδ₂ hself hcomp))
      (fun i => hobj i)
  refine ⟨L, hL, fun i => ⟨isoOfMOD (X := Y') (Y := Y) (g := q) (L := L) (N := obj i)
    ⟨e.hom.hom i, e.inv.hom i,
      (DescentData.comp_hom e.hom e.inv i).symm.trans
        ((congrArg (fun ψ => DescentData.Hom.hom ψ i) e.hom_inv_id).trans (DescentData.id_hom _ i)),
      (DescentData.comp_hom e.inv e.hom i).symm.trans
        ((congrArg (fun ψ => DescentData.Hom.hom ψ i) e.inv_hom_id).trans (DescentData.id_hom _ i))⟩⟩⟩

end PlainDescentFF

end ExZar
end

noncomputable section
namespace ExZar

open NeronModelInfra AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

lemma isPullback_baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  have big : IsPullback (baseChangeSnd c ψ ≫ pullback.fst c t) (pullback.snd c t') c (ψ.1 ≫ t) := by
    rw [ψ.2, show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback c t'
  exact big.of_right ((pullback.lift_snd _ _ _)) (IsPullback.of_hasPullback c t)

lemma isPullback_baseChangeSnd {X U V W : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)} {wS : W ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x) (a : SchemeHomOver wS uS) (b : SchemeHomOver wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) := by
  have hbig : IsPullback (pullback.snd c wS ≫ a.1) (baseChangeSnd c b) u.1 (pullback.snd c vS ≫ v.1) :=
    (isPullback_baseChangeSnd_snd c b).flip.paste_horiz h
  have hbig' : IsPullback (baseChangeSnd c a ≫ pullback.snd c uS) (baseChangeSnd c b) u.1
      (baseChangeSnd c v ≫ pullback.snd c x) := by
    rw [show baseChangeSnd c a ≫ pullback.snd c uS = pullback.snd c wS ≫ a.1 from pullback.lift_snd _ _ _,
      show baseChangeSnd c v ≫ pullback.snd c x = pullback.snd c vS ≫ v.1 from pullback.lift_snd _ _ _]
    exact hbig
  refine hbig'.of_right ?_ (isPullback_baseChangeSnd_snd c u).flip
  rw [baseChangeSnd_comp, baseChangeSnd_comp]
  congr 1
  exact Subtype.ext h.w

abbrev strMap₁₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    Limits.pullback ψ₁.1 ψ₂.1 ⟶ Spec (CommRingCat.of R) :=
  pullback.fst ψ₁.1 ψ₂.1 ≫ t₁

def pr₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₁ :=
  ⟨pullback.fst ψ₁.1 ψ₂.1, rfl⟩

def pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₂ :=
  ⟨pullback.snd ψ₁.1 ψ₂.1, by
    have h2 : pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 ≫ t = pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ := by rw [ψ₂.2]
    have h1 : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 ≫ t = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁ := by rw [ψ₁.2]
    change pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁
    rw [← h2, ← h1, ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[scoped simp] lemma pr₁_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₁ ψ₁ ψ₂).1 = pullback.fst ψ₁.1 ψ₂.1 := rfl

@[scoped simp] lemma pr₂_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₂ ψ₁ ψ₂).1 = pullback.snd ψ₁.1 ψ₂.1 := rfl

lemma postComp_pr₁_eq_postComp_pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    postComp ψ₁ (pr₁ ψ₁ ψ₂) = postComp ψ₂ (pr₂ ψ₁ ψ₂) :=
  Subtype.ext pullback.condition

def chosenPullback {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    ChosenPullback (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) where
  pullback := Limits.pullback c (strMap₁₂ ψ₁ ψ₂)
  p₁ := baseChangeSnd c (pr₁ ψ₁ ψ₂)
  p₂ := baseChangeSnd c (pr₂ ψ₁ ψ₂)
  condition := by
    rw [baseChangeSnd_comp, baseChangeSnd_comp, postComp_pr₁_eq_postComp_pr₂]
  isLimit := (isPullback_baseChangeSnd c ψ₁ ψ₂ (pr₁ ψ₁ ψ₂) (pr₂ ψ₁ ψ₂)
    (IsPullback.of_hasPullback ψ₁.1 ψ₂.1)).isLimit
  p := baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))
  hp₁ := baseChangeSnd_comp c _ _

section three
variable {T T₁ T₂ T₃ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} {t₃ : T₃ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) (ψ₃ : SchemeHomOver t₃ t)

abbrev ρ₁₂ : SchemeHomOver (strMap₁₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) (strMap₁₂ ψ₁ ψ₂) := pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)

abbrev ρ₂₃ : SchemeHomOver (strMap₁₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) (strMap₁₂ ψ₂ ψ₃) := pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)

def ρ₁₃ : SchemeHomOver (strMap₁₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) (strMap₁₂ ψ₁ ψ₃) :=
  ⟨pullback.lift ((ρ₁₂ ψ₁ ψ₂ ψ₃).1 ≫ (pr₁ ψ₁ ψ₂).1) ((ρ₂₃ ψ₁ ψ₂ ψ₃).1 ≫ (pr₂ ψ₂ ψ₃).1)
      (by
        have hT₂ : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 = pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 := pullback.condition
        have hT₂' : pullback.fst ψ₂.1 ψ₃.1 ≫ ψ₂.1 = pullback.snd ψ₂.1 ψ₃.1 ≫ ψ₃.1 := pullback.condition
        have hT₃ : pullback.fst (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.snd ψ₁.1 ψ₂.1 =
            pullback.snd (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.fst ψ₂.1 ψ₃.1 :=
          pullback.condition
        simp only [pr₁_val, pr₂_val, Category.assoc]
        rw [hT₂, ← Category.assoc, hT₃, Category.assoc, hT₂']),
    by
      simp only [pr₁_val, pr₂_val]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc]
      rfl⟩

lemma ρ₁₃_pr₁ : postComp (pr₁ ψ₁ ψ₃) (ρ₁₃ ψ₁ ψ₂ ψ₃) = postComp (pr₁ ψ₁ ψ₂) (ρ₁₂ ψ₁ ψ₂ ψ₃) :=
  Subtype.ext (pullback.lift_fst _ _ _)

lemma ρ₁₃_pr₂ : postComp (pr₂ ψ₁ ψ₃) (ρ₁₃ ψ₁ ψ₂ ψ₃) = postComp (pr₂ ψ₂ ψ₃) (ρ₂₃ ψ₁ ψ₂ ψ₃) :=
  Subtype.ext (pullback.lift_snd _ _ _)

lemma ρ₂₃_pr₁ : postComp (pr₁ ψ₂ ψ₃) (ρ₂₃ ψ₁ ψ₂ ψ₃) = postComp (pr₂ ψ₁ ψ₂) (ρ₁₂ ψ₁ ψ₂ ψ₃) :=
  Subtype.ext pullback.condition.symm

def chosenPullback₃ :
    ChosenPullback₃ (chosenPullback c ψ₁ ψ₂) (chosenPullback c ψ₂ ψ₃) (chosenPullback c ψ₁ ψ₃) where
  chosenPullback := chosenPullback c (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)
  p := baseChangeSnd c (postComp (postComp ψ₁ (pr₁ ψ₁ ψ₂)) (ρ₁₂ ψ₁ ψ₂ ψ₃))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ₁ ψ₂) (ρ₁₂ ψ₁ ψ₂ ψ₃))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ₂ ψ₃) (ρ₂₃ ψ₁ ψ₂ ψ₃))
  l :=
    { f := baseChangeSnd c (ρ₁₃ ψ₁ ψ₂ ψ₃)
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ₁ ψ₃) = _
        rw [baseChangeSnd_comp, ρ₁₃_pr₁]
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ₁ ψ₃) = _
        rw [baseChangeSnd_comp, ρ₁₃_pr₂]
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₃)) = _
        rw [baseChangeSnd_comp]
        congr 1
        exact Subtype.ext (by
          show (ρ₁₃ ψ₁ ψ₂ ψ₃).1 ≫ (pr₁ ψ₁ ψ₃).1 ≫ ψ₁.1 = (ρ₁₂ ψ₁ ψ₂ ψ₃).1 ≫ (pr₁ ψ₁ ψ₂).1 ≫ ψ₁.1
          simp only [← Category.assoc]
          congr 1
          exact pullback.lift_fst _ _ _) }
  hp₁ := by
    change baseChangeSnd c (ρ₁₂ ψ₁ ψ₂ ψ₃) ≫ baseChangeSnd c (pr₁ ψ₁ ψ₂) = _
    rw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (ρ₂₃ ψ₁ ψ₂ ψ₃) ≫ baseChangeSnd c (pr₂ ψ₂ ψ₃) = _
    rw [baseChangeSnd_comp]

end three

end ExZar
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

noncomputable section
namespace ExZar

open NeronModelInfra AlgebraicGeometry.RelPicard CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isInvertible_of_iso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L')
    (h : Scheme.Modules.IsInvertible L') : Scheme.Modules.IsInvertible L := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨eU⟩⟩ := h.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e ≪≫ eU⟩⟩

theorem isInvertible_of_openCover {Y : Scheme.{u}} {ι : Type w} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y)
    [∀ i, IsOpenImmersion (g i)] (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) (L : Y.Modules)
    (h : ∀ i, Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (g i)).obj L)) : Scheme.Modules.IsInvertible L := by
  refine ⟨fun y => ?_⟩
  obtain ⟨i, x, hx⟩ := hg y
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (h i).1 x
  refine ⟨(g i) ''ᵁ U, ⟨x, hxU, hx⟩, ⟨?_⟩⟩
  have fac : ((g i) ''ᵁ U).ι = ((g i).isoImage U).inv ≫ U.ι ≫ g i := ((g i).isoImage_inv_ι U).symm
  exact (Scheme.Modules.pullbackCongr fac).app L ≪≫
    ((Scheme.Modules.pullbackComp ((g i).isoImage U).inv (U.ι ≫ g i)).app L).symm ≪≫
    (Scheme.Modules.pullback ((g i).isoImage U).inv).mapIso (((Scheme.Modules.pullbackComp U.ι (g i)).app L).symm ≪≫ eU) ≪≫
    Scheme.Modules.pullbackUnitIso ((g i).isoImage U).inv

section Theta
variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {ι : Type w} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ Spec (CommRingCat.of R)}
  (f : ∀ i, SchemeHomOver (u i) t) (M : ∀ i, RigidifiedLineBundle c ε (u i))

abbrev EE (T : Scheme.{u}) : T.Modules := SheafOfModules.unit T.ringCatSheaf

def β (i : ι) :
    (Scheme.Modules.pullback (rigSection c (u i) ε)).obj (M i).L ≅ (Scheme.Modules.pullback (f i).1).obj (EE T) :=
  (M i).rigidified.some ≪≫ (Scheme.Modules.pullbackUnitIso (f i).1).symm

def Θ (i : ι) {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (g₁ : Limits.pullback c z ⟶ Limits.pullback c (u i)) (ζ₁ : Z ⟶ U i)
    (S₁ : rigSection c z ε ≫ g₁ = ζ₁ ≫ rigSection c (u i) ε) (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f i).1 = ζT) :
    (Scheme.Modules.pullback (rigSection c z ε)).obj ((Scheme.Modules.pullback g₁).obj (M i).L) ≅ (Scheme.Modules.pullback ζT).obj (EE T) :=
  (sqIso S₁).app (M i).L ≪≫ (Scheme.Modules.pullback ζ₁).mapIso (β c ε f M i) ≪≫ (τ ζ₁ (f i).1 ζT h₁).app (EE T)

end Theta
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

section Rigidity
variable {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))

theorem iso_eq_of_map_rigSection_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {L₁ L₂ : (Limits.pullback c z).Modules}
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (r₂ : Nonempty ((Scheme.Modules.pullback (rigSection c z ε)).obj L₂ ≅ SheafOfModules.unit Z.ringCatSheaf))
    (φ ψ : L₁ ≅ L₂)
    (h : (Scheme.Modules.pullback (rigSection c z ε)).map φ.hom = (Scheme.Modules.pullback (rigSection c z ε)).map ψ.hom) :
    φ = ψ := by
  let α' := r₂.some
  let α := (Scheme.Modules.pullback (rigSection c z ε)).mapIso φ ≪≫ α'
  let M₁ : RigidifiedLineBundle c ε z := ⟨L₁, h₁, ⟨α⟩⟩
  let M₂ : RigidifiedLineBundle c ε z := ⟨L₂, h₂, ⟨α'⟩⟩
  have hs := AlgebraicGeometry.RelPicard.RigidifiedLineBundle.subsingleton_iso_map_pullback_rigSection_comp_eq
    R c ε hH0 z M₁ M₂ α α'
  have hφ : (Scheme.Modules.pullback (rigSection c z ε)).mapIso φ ≪≫ α' = α := rfl
  have hψ : (Scheme.Modules.pullback (rigSection c z ε)).mapIso ψ ≪≫ α' = α := by
    have e : (Scheme.Modules.pullback (rigSection c z ε)).mapIso ψ = (Scheme.Modules.pullback (rigSection c z ε)).mapIso φ :=
      Iso.ext h.symm
    rw [e]
  exact congrArg Subtype.val (hs.elim ⟨φ, hφ⟩ ⟨ψ, hψ⟩)

theorem hom_eq_of_map_rigSection_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {L₁ L₂ : (Limits.pullback c z).Modules}
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (r₂ : Nonempty ((Scheme.Modules.pullback (rigSection c z ε)).obj L₂ ≅ SheafOfModules.unit Z.ringCatSheaf))
    (φ ψ : L₁ ⟶ L₂) (hφ : IsIso φ) (hψ : IsIso ψ)
    (h : (Scheme.Modules.pullback (rigSection c z ε)).map φ = (Scheme.Modules.pullback (rigSection c z ε)).map ψ) :
    φ = ψ :=
  congrArg Iso.hom (iso_eq_of_map_rigSection_eq c ε z hH0 h₁ h₂ r₂ (asIso φ) (asIso ψ) h)

theorem exists_iso_map_rigSection_eq {L₁ L₂ : (Limits.pullback c z).Modules}
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂) {W : Z.Modules}
    (θ₁ : (Scheme.Modules.pullback (rigSection c z ε)).obj L₁ ≅ W) (θ₂ : (Scheme.Modules.pullback (rigSection c z ε)).obj L₂ ≅ W)
    (ω : W ≅ SheafOfModules.unit Z.ringCatSheaf) (e : Nonempty (L₁ ≅ L₂)) :
    ∃ Φ : L₁ ≅ L₂, (Scheme.Modules.pullback (rigSection c z ε)).map Φ.hom = θ₁.hom ≫ θ₂.inv := by
  let M₁ : RigidifiedLineBundle c ε z := ⟨L₁, h₁, ⟨θ₁ ≪≫ ω⟩⟩
  let M₂ : RigidifiedLineBundle c ε z := ⟨L₂, h₂, ⟨θ₂ ≪≫ ω⟩⟩
  obtain ⟨Φ, hΦ⟩ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
      R c ε z M₁ M₂ (θ₁ ≪≫ ω) (θ₂ ≪≫ ω) e.some
  refine ⟨Φ, ?_⟩
  have h := congrArg Iso.hom hΦ
  simp only [Iso.trans_hom, Functor.mapIso_hom] at h
  rw [← cancel_mono θ₂.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, ← cancel_mono ω.hom,
    Category.assoc]
  exact h

end Rigidity
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

section Datum
variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {ι : Type w} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ Spec (CommRingCat.of R)}
  (f : ∀ i, SchemeHomOver (u i) t) (M : ∀ i, RigidifiedLineBundle c ε (u i))
  (hM : ∀ (i j : ι) (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (p₁ : SchemeHomOver z (u i)) (p₂ : SchemeHomOver z (u j)),
    p₁.1 ≫ (f i).1 = p₂.1 ≫ (f j).1 → Nonempty (((M i).pullbackAlong p₁).L ≅ ((M j).pullbackAlong p₂).L))

def fF (i : ι) : Limits.pullback c (u i) ⟶ Limits.pullback c t := baseChangeSnd c (f i)

def sqF (i j : ι) : ChosenPullback (fF c f i) (fF c f j) := chosenPullback c (f i) (f j)

def sq₃F (i j k : ι) : ChosenPullback₃ (sqF c f i j) (sqF c f j k) (sqF c f i k) := chosenPullback₃ c (f i) (f j) (f k)

abbrev wT (i j : ι) : Limits.pullback (f i).1 (f j).1 ⟶ T := (pr₁ (f i) (f j)).1 ≫ (f i).1

lemma pr₂_comp_eq_wT (i j : ι) : (pr₂ (f i) (f j)).1 ≫ (f j).1 = wT f i j := pullback.condition.symm

abbrev Θ₁ (i j : ι) :=
  Θ c ε f M i (strMap₁₂ (f i) (f j)) (baseChangeSnd c (pr₁ (f i) (f j))) (pr₁ (f i) (f j)).1
    (rigSection_baseChangeSnd c ε _) (wT f i j) rfl

abbrev Θ₂ (i j : ι) :=
  Θ c ε f M j (strMap₁₂ (f i) (f j)) (baseChangeSnd c (pr₂ (f i) (f j))) (pr₂ (f i) (f j)).1
    (rigSection_baseChangeSnd c ε _) (wT f i j) (pr₂_comp_eq_wT f i j)

include hM in
theorem exists_homIso (i j : ι) :
    ∃ Φ : (Scheme.Modules.pullback (baseChangeSnd c (pr₁ (f i) (f j)))).obj (M i).L ≅
        (Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L,
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ (f i) (f j)) ε)).map Φ.hom =
        (Θ₁ c ε f M i j).hom ≫ (Θ₂ c ε f M i j).inv :=
  exists_iso_map_rigSection_eq c ε _ ((M i).isInvertible.pullback _) ((M j).isInvertible.pullback _)
    (Θ₁ c ε f M i j) (Θ₂ c ε f M i j) (Scheme.Modules.pullbackUnitIso (wT f i j))
    (hM i j _ _ (pr₁ (f i) (f j)) (pr₂ (f i) (f j)) pullback.condition)

include hM in

def homIso (i j : ι) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ (f i) (f j)))).obj (M i).L ≅
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L :=
  (exists_homIso c ε f M hM i j).choose

theorem map_homIso (i j : ι) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ (f i) (f j)) ε)).map (homIso c ε f M hM i j).hom =
      (Θ₁ c ε f M i j).hom ≫ (Θ₂ c ε f M i j).inv :=
  (exists_homIso c ε f M hM i j).choose_spec

section Half
variable (k : ι) {W Z : Scheme.{u}} {w : W ⟶ Spec (CommRingCat.of R)} {z : Z ⟶ Spec (CommRingCat.of R)}
    (π : SchemeHomOver w (u k)) (wT' : W ⟶ T) (hw : π.1 ≫ (f k).1 = wT')
    (ζ : SchemeHomOver z w) (g : Limits.pullback c z ⟶ Limits.pullback c (u k))
    (hg : baseChangeSnd c ζ ≫ baseChangeSnd c π = g)
    (ζ₁ : Z ⟶ U k) (hζ₁ : ζ.1 ≫ π.1 = ζ₁) (S₁ : rigSection c z ε ≫ g = ζ₁ ≫ rigSection c (u k) ε)
    (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f k).1 = ζT) (hT : ζ.1 ≫ wT' = ζT)

include hg hζ₁ S₁ in

theorem half_A :
    (Scheme.Modules.pullback (rigSection c z ε)).map ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).inv.app (M k).L) ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map ((sqIso (rigSection_baseChangeSnd c ε π)).hom.app (M k).L) =
    (sqIso S₁).hom.app (M k).L ≫
      (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (rigSection c (u k) ε)).obj (M k).L) :=
  (Iso.inv_comp_eq ((Scheme.Modules.pullback (rigSection c z ε)).mapIso
      ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).app (M k).L))).mpr
    (((Iso.eq_comp_inv ((τ ζ.1 π.1 ζ₁ hζ₁).app ((Scheme.Modules.pullback (rigSection c (u k) ε)).obj (M k).L))).mpr
      ((Category.assoc _ _ _).trans
        (route (baseChangeSnd c ζ) (baseChangeSnd c π) g hg (rigSection c z ε) (rigSection c w ε)
          (rigSection c (u k) ε) ζ.1 π.1 ζ₁ hζ₁ (rigSection_baseChangeSnd c ε ζ) (rigSection_baseChangeSnd c ε π)
          S₁ (M k).L))).trans (Category.assoc _ _ _))

include hζ₁ in

theorem half_B :
    (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (rigSection c (u k) ε)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map ((Scheme.Modules.pullback π.1).map (β c ε f M k).hom) =
    (Scheme.Modules.pullback ζ₁).map (β c ε f M k).hom ≫
      (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (f k).1).obj (EE T)) :=
  ((τ ζ.1 π.1 ζ₁ hζ₁).inv.naturality (β c ε f M k).hom).symm

include hζ₁ hw h₁ hT in

theorem half_C :
    (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (f k).1).obj (EE T)) ≫
      (Scheme.Modules.pullback ζ.1).map ((τ π.1 (f k).1 wT' hw).hom.app (EE T)) =
    (τ ζ₁ (f k).1 ζT h₁).hom.app (EE T) ≫ (τ ζ.1 wT' ζT hT).inv.app (EE T) :=
  (Iso.inv_comp_eq ((τ ζ.1 π.1 ζ₁ hζ₁).app ((Scheme.Modules.pullback (f k).1).obj (EE T)))).mpr
    (((Iso.eq_comp_inv ((τ ζ.1 wT' ζT hT).app (EE T))).mpr
      (τ_paste_app ζ.1 π.1 (f k).1 ζ₁ wT' ζT hζ₁ hw h₁ (EE T)).symm).trans (Category.assoc _ _ _))

include hζ₁ in

theorem half :
    (Scheme.Modules.pullback (rigSection c z ε)).map ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).inv.app (M k).L) ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map (Θ c ε f M k w (baseChangeSnd c π) π.1 (rigSection_baseChangeSnd c ε π) wT' hw).hom =
    (Θ c ε f M k z g ζ₁ S₁ ζT h₁).hom ≫ (τ ζ.1 wT' ζT hT).inv.app (EE T) := by
  have HA := half_A c ε M k π ζ g hg ζ₁ hζ₁ S₁
  have HB := half_B c ε f M k π ζ ζ₁ hζ₁
  have HC := half_C f k π wT' hw ζ ζ₁ hζ₁ ζT h₁ hT
  simp only [Θ, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  dsimp only [Functor.comp_obj] at HA HB HC ⊢
  simp only [Category.assoc]
  refine ((reassoc_of% HA) _).trans ?_
  refine (congrArg (fun x => (sqIso S₁).hom.app (M k).L ≫ x) ((reassoc_of% HB) _)).trans ?_
  exact congrArg (fun x => (sqIso S₁).hom.app (M k).L ≫ (Scheme.Modules.pullback ζ₁).map (β c ε f M k).hom ≫ x) HC

include hζ₁ in

theorem half' :
    (Scheme.Modules.pullback (rigSection c z ε)).map ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).inv.app (M k).L) ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map (Θ c ε f M k w (baseChangeSnd c π) π.1 (rigSection_baseChangeSnd c ε π) wT' hw).hom =
    (Θ c ε f M k z g ζ₁ S₁ ζT h₁).hom ≫ (τ ζ.1 wT' ζT hT).inv.app (EE T) := by
  have HA := half_A c ε M k π ζ g hg ζ₁ hζ₁ S₁
  have HB := half_B c ε f M k π ζ ζ₁ hζ₁
  have HC := half_C f k π wT' hw ζ ζ₁ hζ₁ ζT h₁ hT
  simp only [Θ, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  dsimp only [Functor.comp_obj] at HA HB HC ⊢
  simp only [Category.assoc, reassoc_of% HA, reassoc_of% HB, HC]

include hζ₁ in

theorem half_inv :
    (Scheme.Modules.pullback ζ.1).map (Θ c ε f M k w (baseChangeSnd c π) π.1 (rigSection_baseChangeSnd c ε π) wT' hw).inv ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).inv.app ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback (rigSection c z ε)).map ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).hom.app (M k).L) =
    (τ ζ.1 wT' ζT hT).hom.app (EE T) ≫ (Θ c ε f M k z g ζ₁ S₁ ζT h₁).inv := by
  have H : ((Scheme.Modules.pullback (rigSection c z ε)).mapIso ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).app (M k).L)).symm ≪≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).app ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≪≫
      (Scheme.Modules.pullback ζ.1).mapIso (Θ c ε f M k w (baseChangeSnd c π) π.1 (rigSection_baseChangeSnd c ε π) wT' hw) =
      Θ c ε f M k z g ζ₁ S₁ ζT h₁ ≪≫ ((τ ζ.1 wT' ζT hT).app (EE T)).symm :=
    Iso.ext (half c ε f M k π wT' hw ζ g hg ζ₁ hζ₁ S₁ ζT h₁ hT)
  have H' := congrArg Iso.inv H
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] at H'
  exact H'

end Half
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

theorem key (i j : ι) {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of R)}
    (ζ : SchemeHomOver z (strMap₁₂ (f i) (f j)))
    (g : Limits.pullback c z ⟶ Limits.pullback c (strMap₁₂ (f i) (f j))) (hg : g = baseChangeSnd c ζ)
    (g₁ : Limits.pullback c z ⟶ Limits.pullback c (u i)) (g₂ : Limits.pullback c z ⟶ Limits.pullback c (u j))
    (hg₁ : g ≫ baseChangeSnd c (pr₁ (f i) (f j)) = g₁) (hg₂ : g ≫ baseChangeSnd c (pr₂ (f i) (f j)) = g₂)
    (ζ₁ : Z ⟶ U i) (ζ₂ : Z ⟶ U j) (hζ₁ : ζ.1 ≫ (pr₁ (f i) (f j)).1 = ζ₁) (hζ₂ : ζ.1 ≫ (pr₂ (f i) (f j)).1 = ζ₂)
    (S₁ : rigSection c z ε ≫ g₁ = ζ₁ ≫ rigSection c (u i) ε) (S₂ : rigSection c z ε ≫ g₂ = ζ₂ ≫ rigSection c (u j) ε)
    (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f i).1 = ζT) (h₂ : ζ₂ ≫ (f j).1 = ζT) :
    (Scheme.Modules.pullback (rigSection c z ε)).map
      (pullHomIso (homIso c ε f M hM i j) g g₁ g₂ hg₁ hg₂).hom =
      (Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁).hom ≫ (Θ c ε f M j z g₂ ζ₂ S₂ ζT h₂).inv := by
  subst hg
  have hT : ζ.1 ≫ wT f i j = ζT := by
    show ζ.1 ≫ (pr₁ (f i) (f j)).1 ≫ (f i).1 = ζT
    rw [← Category.assoc, hζ₁, h₁]
  have Hi := half c ε f M i (pr₁ (f i) (f j)) (wT f i j) rfl ζ g₁ hg₁ ζ₁ hζ₁ S₁ ζT h₁ hT
  have Hj := half_inv c ε f M j (pr₂ (f i) (f j)) (wT f i j) (pr₂_comp_eq_wT f i j) ζ g₂ hg₂ ζ₂ hζ₂ S₂ ζT h₂ hT

  have HN : (Scheme.Modules.pullback (rigSection c z ε)).map
        ((Scheme.Modules.pullback (baseChangeSnd c ζ)).map (homIso c ε f M hM i j).hom) =
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ (f i) (f j)))).obj (M i).L) ≫
        (Scheme.Modules.pullback ζ.1).map ((Scheme.Modules.pullback (rigSection c (strMap₁₂ (f i) (f j)) ε)).map
          (homIso c ε f M hM i j).hom) ≫
        (sqIso (rigSection_baseChangeSnd c ε ζ)).inv.app ((Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L) :=
    ((Iso.eq_comp_inv ((sqIso (rigSection_baseChangeSnd c ε ζ)).app
        ((Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L))).mpr
      ((sqIso (rigSection_baseChangeSnd c ε ζ)).hom.naturality (homIso c ε f M hM i j).hom)).trans
      (Category.assoc _ _ _)
  rw [pullHomIso_hom', Functor.map_comp, Functor.map_comp]
  dsimp only [Functor.comp_obj] at Hi Hj HN ⊢
  rw [HN, map_homIso, Functor.map_comp]
  simp only [Category.assoc]
  refine ((reassoc_of% Hi) _).trans ?_
  refine (congrArg (fun x => (Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁).hom ≫ (τ ζ.1 (wT f i j) ζT hT).inv.app (EE T) ≫ x)
    Hj).trans ?_
  exact congrArg (fun x => (Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁).hom ≫ x)
    (Iso.inv_hom_id_app_assoc (τ ζ.1 (wT f i j) ζT hT) (EE T) (Θ c ε f M j z g₂ ζ₂ S₂ ζT h₂).inv)

def δ (i : ι) : SchemeHomOver (u i) (strMap₁₂ (f i) (f i)) :=
  ⟨pullback.lift (𝟙 _) (𝟙 _) rfl, by rw [pullback.lift_fst_assoc, Category.id_comp]⟩

lemma δ_pr₁ (i : ι) : baseChangeSnd c (δ f i) ≫ baseChangeSnd c (pr₁ (f i) (f i)) = 𝟙 _ := by
  rw [baseChangeSnd_comp]
  have e : postComp (pr₁ (f i) (f i)) (δ f i) = ⟨𝟙 _, Category.id_comp _⟩ := Subtype.ext (pullback.lift_fst _ _ _)
  rw [e]
  exact baseChangeSnd_id c (u i)

lemma δ_pr₂ (i : ι) : baseChangeSnd c (δ f i) ≫ baseChangeSnd c (pr₂ (f i) (f i)) = 𝟙 _ := by
  rw [baseChangeSnd_comp]
  have e : postComp (pr₂ (f i) (f i)) (δ f i) = ⟨𝟙 _, Category.id_comp _⟩ := Subtype.ext (pullback.lift_snd _ _ _)
  rw [e]
  exact baseChangeSnd_id c (u i)

lemma nonempty_rigidification (i : ι) {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (g₁ : Limits.pullback c z ⟶ Limits.pullback c (u i)) (ζ₁ : Z ⟶ U i)
    (S₁ : rigSection c z ε ≫ g₁ = ζ₁ ≫ rigSection c (u i) ε) (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f i).1 = ζT) :
    Nonempty ((Scheme.Modules.pullback (rigSection c z ε)).obj ((Scheme.Modules.pullback g₁).obj (M i).L) ≅
      SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁ ≪≫ Scheme.Modules.pullbackUnitIso ζT⟩

theorem pullHomIso_self (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) (i : ι) :
    pullHomIso (homIso c ε f M hM i i) (baseChangeSnd c (δ f i)) (𝟙 _) (𝟙 _) (δ_pr₁ c f i) (δ_pr₂ c f i) =
      Iso.refl _ := by
  have S : rigSection c (u i) ε ≫ 𝟙 _ = 𝟙 _ ≫ rigSection c (u i) ε := by simp
  have K := key c ε f M hM i i (δ f i) _ rfl (𝟙 _) (𝟙 _) (δ_pr₁ c f i) (δ_pr₂ c f i) (𝟙 _) (𝟙 _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) S S (f i).1 (Category.id_comp _) (Category.id_comp _)
  exact iso_eq_of_map_rigSection_eq c ε (u i) hH0 ((M i).isInvertible.pullback _) ((M i).isInvertible.pullback _)
    (nonempty_rigidification c ε f M i (u i) (𝟙 _) (𝟙 _) S (f i).1 (Category.id_comp _)) _ _ (by
      rw [K]
      simp)

section comp
variable (i j k : ι)

abbrev ζT3 : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ T :=
  (ρ₁₂ (f i) (f j) (f k)).1 ≫ wT f i j

abbrev χ₁ : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ U i :=
  (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₁ (f i) (f j)).1
abbrev χ₂ : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ U j :=
  (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₂ (f i) (f j)).1
abbrev χ₃ : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ U k :=
  (ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₂ (f j) (f k)).1

lemma hχ₁ : χ₁ f i j k ≫ (f i).1 = ζT3 f i j k := Category.assoc _ _ _
lemma hχ₂ : χ₂ f i j k ≫ (f j).1 = ζT3 f i j k := by
  show ((ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₂ (f i) (f j)).1) ≫ (f j).1 =
    (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₁ (f i) (f j)).1 ≫ (f i).1
  rw [Category.assoc, pr₂_comp_eq_wT]
lemma hχ₃ : χ₃ f i j k ≫ (f k).1 = ζT3 f i j k := by
  show ((ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₂ (f j) (f k)).1) ≫ (f k).1 =
    (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₁ (f i) (f j)).1 ≫ (f i).1
  rw [Category.assoc, pr₂_comp_eq_wT]
  show (ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₁ (f j) (f k)).1 ≫ (f j).1 = _
  rw [← Category.assoc, show (ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₁ (f j) (f k)).1 =
      (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₂ (f i) (f j)).1 from pullback.condition.symm, Category.assoc,
    pr₂_comp_eq_wT]

lemma S₁' : rigSection c _ ε ≫ (sq₃F c f i j k).p₁ = χ₁ f i j k ≫ rigSection c (u i) ε :=
  rigSection_baseChangeSnd c ε _
lemma S₂' : rigSection c _ ε ≫ (sq₃F c f i j k).p₂ = χ₂ f i j k ≫ rigSection c (u j) ε :=
  rigSection_baseChangeSnd c ε _
lemma S₃' : rigSection c _ ε ≫ (sq₃F c f i j k).p₃ = χ₃ f i j k ≫ rigSection c (u k) ε :=
  rigSection_baseChangeSnd c ε _

set_option maxHeartbeats 3200000 in

theorem pullHomIso_comp (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    pullHomIso (Y' := Limits.pullback c (strMap₁₂ (pr₂ (f i) (f j)) (pr₁ (f j) (f k)))) (homIso c ε f M hM i j) (sq₃F c f i j k).p₁₂ (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₂
        (sq₃F c f i j k).p₁₂_p₁ (sq₃F c f i j k).p₁₂_p₂ ≪≫
      pullHomIso (Y' := Limits.pullback c (strMap₁₂ (pr₂ (f i) (f j)) (pr₁ (f j) (f k)))) (homIso c ε f M hM j k) (sq₃F c f i j k).p₂₃ (sq₃F c f i j k).p₂ (sq₃F c f i j k).p₃
        (sq₃F c f i j k).p₂₃_p₂ (sq₃F c f i j k).p₂₃_p₃ =
      pullHomIso (Y' := Limits.pullback c (strMap₁₂ (pr₂ (f i) (f j)) (pr₁ (f j) (f k)))) (homIso c ε f M hM i k) (sq₃F c f i j k).p₁₃ (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₃
        (sq₃F c f i j k).p₁₃_p₁ (sq₃F c f i j k).p₁₃_p₃ := by
  have K₁₂ := key c ε f M hM i j (ρ₁₂ (f i) (f j) (f k)) (sq₃F c f i j k).p₁₂ rfl (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₂
    (sq₃F c f i j k).p₁₂_p₁ (sq₃F c f i j k).p₁₂_p₂ (χ₁ f i j k) (χ₂ f i j k) rfl rfl (S₁' c ε f i j k) (S₂' c ε f i j k)
    (ζT3 f i j k) (hχ₁ f i j k) (hχ₂ f i j k)
  have K₂₃ := key c ε f M hM j k (ρ₂₃ (f i) (f j) (f k)) (sq₃F c f i j k).p₂₃ rfl (sq₃F c f i j k).p₂ (sq₃F c f i j k).p₃
    (sq₃F c f i j k).p₂₃_p₂ (sq₃F c f i j k).p₂₃_p₃ (χ₂ f i j k) (χ₃ f i j k) pullback.condition.symm rfl
    (S₂' c ε f i j k) (S₃' c ε f i j k) (ζT3 f i j k) (hχ₂ f i j k) (hχ₃ f i j k)
  have K₁₃ := key c ε f M hM i k (ρ₁₃ (f i) (f j) (f k)) (sq₃F c f i j k).p₁₃ rfl (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₃
    (sq₃F c f i j k).p₁₃_p₁ (sq₃F c f i j k).p₁₃_p₃ (χ₁ f i j k) (χ₃ f i j k) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) (S₁' c ε f i j k) (S₃' c ε f i j k) (ζT3 f i j k) (hχ₁ f i j k) (hχ₃ f i j k)
  exact iso_eq_of_map_rigSection_eq c ε _ hH0 ((M i).isInvertible.pullback _) ((M k).isInvertible.pullback _)
    (nonempty_rigidification c ε f M k _ (sq₃F c f i j k).p₃ (χ₃ f i j k) (S₃' c ε f i j k) (ζT3 f i j k) (hχ₃ f i j k))
    _ _ (by
      rw [Iso.trans_hom, Functor.map_comp, K₁₂, K₂₃, K₁₃]
      exact (Category.assoc _ _ _).trans (congrArg
        (fun x => (Θ c ε f M i _ (sq₃F c f i j k).p₁ (χ₁ f i j k) (S₁' c ε f i j k) (ζT3 f i j k) (hχ₁ f i j k)).hom ≫ x)
        ((Θ c ε f M j _ (sq₃F c f i j k).p₂ (χ₂ f i j k) (S₂' c ε f i j k) (ζT3 f i j k) (hχ₂ f i j k)).inv_hom_id_assoc
          (Θ c ε f M k _ (sq₃F c f i j k).p₃ (χ₃ f i j k) (S₃' c ε f i j k) (ζT3 f i j k) (hχ₃ f i j k)).inv)))

end comp
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

end Datum
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

section FF
open AlgebraicGeometry.SmoothProperCurve

variable (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

abbrev πS : SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t :=
  ⟨pullback.fst t (specMap R R'), pullback.condition⟩

scoped instance flat_specMap : Flat (specMap R R') :=
  ((flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).1
scoped instance surjective_specMap : Surjective (specMap R R') :=
  ((flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
scoped instance isAffineHom_πS : IsAffineHom (πS (R := R) R' t).1 :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
scoped instance flat_πS : Flat (πS (R := R) R' t).1 :=
  MorphismProperty.pullback_fst (P := @Flat) _ _ inferInstance
scoped instance surjective_πS : Surjective (πS (R := R) R' t).1 :=
  MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance

scoped instance isAffineHom_q : IsAffineHom (baseChangeSnd c (πS (R := R) R' t)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (πS (R := R) R' t)).flip inferInstance
scoped instance flat_q : Flat (baseChangeSnd c (πS (R := R) R' t)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (πS (R := R) R' t)).flip inferInstance
scoped instance surjective_q : Surjective (baseChangeSnd c (πS (R := R) R' t)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (πS (R := R) R' t)).flip inferInstance

abbrev fS : Unit → SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t := fun _ => πS (R := R) R' t

set_option maxHeartbeats 3200000 in
theorem main_ff (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (M' : RigidifiedLineBundle c ε (pullback.snd t (specMap R R') ≫ specMap R R'))
    (hM' : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z (pullback.snd t (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ pullback.fst t (specMap R R') = p₂.1 ≫ pullback.fst t (specMap R R') →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L)) :
    ∃ M : RigidifiedLineBundle c ε t, Nonempty ((M.pullbackAlong (πS (R := R) R' t)).L ≅ M'.L) := by

  have hM : ∀ (i j : Unit) (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ : SchemeHomOver z (pullback.snd t (specMap R R') ≫ specMap R R'))
      (p₂ : SchemeHomOver z (pullback.snd t (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ (fS (R := R) R' t i).1 = p₂.1 ≫ (fS (R := R) R' t j).1 →
        Nonempty ((((fun _ : Unit => M') i).pullbackAlong p₁).L ≅ (((fun _ : Unit => M') j).pullbackAlong p₂).L) :=
    fun _ _ Z z p₁ p₂ h => hM' Z z p₁ p₂ h
  have HH := exists_iso_of_plainDescent_ff (baseChangeSnd c (πS (R := R) R' t))
    (sqF c (fS (R := R) R' t)) (sq₃F c (fS (R := R) R' t)) (fun _ => M'.L) (fun _ => M'.isInvertible)
    (fun i j => homIso c ε (fS (R := R) R' t) (fun _ : Unit => M') hM i j)
    (fun i => baseChangeSnd c (δ (fS (R := R) R' t) i)) (δ_pr₁ c (fS (R := R) R' t)) (δ_pr₂ c (fS (R := R) R' t))
    (fun i _ _ => pullHomIso_self c ε (fS (R := R) R' t) (fun _ : Unit => M') hM hH0 i)
    (fun i j k _ _ _ _ _ _ => pullHomIso_comp c ε (fS (R := R) R' t) (fun _ : Unit => M') hM i j k hH0)
  obtain ⟨L, hL, eL⟩ := HH
  have eᵢ : (Scheme.Modules.pullback (baseChangeSnd c (πS (R := R) R' t))).obj L ≅ M'.L := (eL ()).some
  refine ⟨RigidifiedLineBundle.ofInvertible (ε := ε) L hL, ?_⟩
  obtain ⟨a⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) (πS (R := R) R' t) hL
  obtain ⟨b⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε) (hL.pullback _) M'.isInvertible eᵢ
  obtain ⟨d⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M'
  exact ⟨a ≪≫ b ≪≫ d⟩

end FF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

end ExZar
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.ExZar"

open NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M' : RigidifiedLineBundle c ε (pullback.snd t (specMap R R') ≫ specMap R R'))
    (hM' : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z (pullback.snd t (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ pullback.fst t (specMap R R') = p₂.1 ≫ pullback.fst t (specMap R R') →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L)) :
    ∃ M : RigidifiedLineBundle c ε t,
      Nonempty ((M.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L ≅ M'.L) :=
  ExZar.main_ff c ε R' t hH0 M' hM'

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections (solution)
