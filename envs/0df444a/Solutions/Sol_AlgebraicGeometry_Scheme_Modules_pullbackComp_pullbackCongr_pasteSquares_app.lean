-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b4ee5b26-d435-5c00-a4ba-34b9057541e4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules.pullbackCongr Modules Modules.pullbackComp"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pseudofunctor_associativity pullbackCongr pullbackComp"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

theorem pullbackComp_paste (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    Functor.whiskerLeft (pullback h) (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (pullbackComp g h).hom (pullback f) ≫
        (pullbackComp f (g ≫ h)).hom ≫ eqToHom (by rw [Category.assoc]) := by
  have H0 := pseudofunctor_associativity f g h
  have H1 : Functor.whiskerLeft (pullback h) (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫ (Functor.isoWhiskerRight (pullbackComp g h) (pullback f)).hom ≫
        (pullbackComp f (g ≫ h)).hom ≫
        ((pullbackComp f (g ≫ h)).inv ≫ Functor.whiskerRight (pullbackComp g h).inv (pullback f) ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (pullback h) (pullbackComp f g).hom ≫
            (pullbackComp (f ≫ g) h).hom) := by
    rw [Iso.hom_inv_id_assoc, Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id,
      Functor.whiskerRight_id', Category.id_comp, Iso.inv_hom_id_assoc]
  rw [H0] at H1
  exact H1

theorem pullbackComp_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (M : X₃.Modules) :
    (pullbackComp f g).hom.app ((pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M =
      (pullback f).map ((pullbackComp g h).hom.app M) ≫ (pullbackComp f (g ≫ h)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  have H := NatTrans.congr_app (pullbackComp_paste f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    eqToHom_app] at H
  exact H

noncomputable def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) : pullback g ⋙ pullback f ≅ pullback m :=
  pullbackComp f g ≪≫ pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp [τ, pullbackCongr]

theorem τ_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (fg : X₀ ⟶ X₂) (gh : X₁ ⟶ X₃) (m : X₀ ⟶ X₃)
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = m) (M : X₃.Modules) :
    (τ f g fg e₁).hom.app ((pullback h).obj M) ≫ (τ fg h m e₃).hom.app M =
      (pullback f).map ((τ g h gh e₂).hom.app M) ≫ (τ f gh m (by rw [← e₂, ← Category.assoc, e₁, e₃])).hom.app M := by
  subst e₁ e₂ e₃
  simp only [τ_hom_app, eqToHom_refl, Category.comp_id]
  rw [pullbackComp_paste_app]

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  simp [τ, pullbackCongr]

noncomputable def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : pullback g ⋙ pullback f ≅ pullback k ⋙ pullback h :=
  pullbackComp f g ≪≫ pullbackCongr e ≪≫ (pullbackComp h k).symm

theorem sqIso_hom_app {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) :
    (sqIso e).hom.app M = (τ f g (h ≫ k) e).hom.app M ≫ (τ h k (h ≫ k) rfl).inv.app M := by
  simp [sqIso, τ, pullbackCongr]

theorem map_sqIso_hom_app {W X Y Z V : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) (G : W.Modules ⥤ V.Modules) :
    G.map ((sqIso e).hom.app M) =
      G.map ((τ f g (h ≫ k) e).hom.app M) ≫ G.map ((τ h k (h ≫ k) rfl).inv.app M) := by
  rw [sqIso_hom_app, G.map_comp]

section Route

variable {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
  (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
  (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
  (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s)

include e G E F in
theorem route_comm : s₀ ≫ d = m ≫ s := by
  rw [← e, ← Category.assoc, E, Category.assoc, F, ← Category.assoc, G]

set_option maxHeartbeats 3200000 in

theorem route (M : X.Modules) :
    (sqIso E).hom.app ((pullback b).obj M) ≫ (pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((pullback s).obj M) =
      (pullback s₀).map ((τ a b d e).hom.app M) ≫
        (τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M ≫
          (τ m s (m ≫ s) rfl).inv.app M := by
  have hn : (r ≫ s₁) ≫ b = m ≫ s := by rw [Category.assoc, F, ← Category.assoc, G]

  have P1 := τ_paste_app r s₁ b (r ≫ s₁) (p ≫ s) (m ≫ s) rfl F hn M
  have P2 := τ_paste_app r p s m (p ≫ s) (m ≫ s) G rfl rfl M
  have P3 := τ_paste_app s₀ a b (r ≫ s₁) d (m ≫ s) E e hn M

  have P1' := (Iso.eq_comp_inv ((τ r (p ≫ s) (m ≫ s) (by rw [← Category.assoc, G])).app M)).mpr P1.symm

  have P2i : ((τ r p m G).app ((pullback s).obj M) ≪≫ (τ m s (m ≫ s) rfl).app M).inv =
      ((pullback r).mapIso ((τ p s (p ≫ s) rfl).app M) ≪≫
        (τ r (p ≫ s) (m ≫ s) (by rw [← Category.assoc, G])).app M).inv :=
    congrArg Iso.inv (Iso.ext P2)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at P2i

  have hmap : (pullback r).map ((sqIso F).hom.app M) =
      (pullback r).map ((τ s₁ b (p ≫ s) F).hom.app M) ≫ (pullback r).map ((τ p s (p ≫ s) rfl).inv.app M) := by
    rw [sqIso_hom_app]; exact (pullback r).map_comp _ _
  dsimp only [Iso.app_inv] at P1'
  erw [reassoc_of% hmap, sqIso_hom_app]
  erw [Category.assoc]
  erw [reassoc_of% P1']
  erw [Iso.inv_hom_id_app_assoc]
  have TAIL : (τ r (p ≫ s) (m ≫ s) (by rw [← Category.assoc, G])).inv.app M ≫
      (pullback r).map ((τ p s (p ≫ s) rfl).inv.app M) ≫ (τ r p m G).hom.app ((pullback s).obj M) =
        (τ m s (m ≫ s) rfl).inv.app M := by
    erw [← reassoc_of% P2i, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  exact (congrArg (fun k => (τ s₀ a (r ≫ s₁) E).hom.app ((pullback b).obj M) ≫
      (τ (r ≫ s₁) b (m ≫ s) hn).hom.app M ≫ k) TAIL).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (τ m s (m ≫ s) rfl).inv.app M) P3).trans (Category.assoc _ _ _)))

end Route

section Head

variable {X X₀' X₁' X₂' Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head (M : X.Modules) :
    (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h₁ := route a₁ b₁ d e₁ s₀ s₁ s r₁ p₁ m G₁ E₁ F₁ M
  have h₂ := route a₂ b₂ d e₂ s₀ s₂ s r₂ p₂ m G₂ E₂ F₂ M
  have h₂' := (Iso.inv_comp_eq ((pullback s₀).mapIso ((τ a₂ b₂ d e₂).app M))).mpr h₂
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun k => (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M) ≫ k) h₂').trans h₁.symm

end Head

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules.pullbackCongr Modules Modules.pullbackComp"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pseudofunctor_associativity pullbackCongr pullbackComp"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem route' {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (sqIso E).hom.app ((pullback b).obj M) ≫ (pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((pullback s).obj M) =
      (pullback s₀).map ((τ a b d e).hom.app M) ≫ (sqIso H).hom.app M := by
  rw [sqIso_hom_app (e := H)]
  exact route a b d e s₀ s₁ s r p m G E F M

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {X X₀ X₁ Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X) (d : X₀ ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀) (s₁ : Y₁ ⟶ X₁) (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (Scheme.Modules.pullbackComp s₀ a ≪≫ Scheme.Modules.pullbackCongr E ≪≫
          (Scheme.Modules.pullbackComp r s₁).symm).hom.app ((Scheme.Modules.pullback b).obj M) ≫
      (Scheme.Modules.pullback r).map
          ((Scheme.Modules.pullbackComp s₁ b ≪≫ Scheme.Modules.pullbackCongr F ≪≫
            (Scheme.Modules.pullbackComp p s).symm).hom.app M) ≫
        (Scheme.Modules.pullbackComp r p ≪≫ Scheme.Modules.pullbackCongr G).hom.app
          ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map
          ((Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp s₀ d ≪≫ Scheme.Modules.pullbackCongr H ≪≫
          (Scheme.Modules.pullbackComp m s).symm).hom.app M :=
  AlgebraicGeometry.Scheme.Modules.route' a b d e s₀ s₁ s r p m G E F H M

end S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app (solution)
