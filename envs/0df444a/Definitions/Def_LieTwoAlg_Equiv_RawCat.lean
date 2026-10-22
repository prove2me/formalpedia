-- Prove2me | Definitions.Def_LieTwoAlg_Equiv_RawCat
-- name    : LieTwoAlg_Equiv_RawCat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:06.407533+00:00
-- url     : https://prove2.me/theorems/24887a08-e532-41d2-9570-51e5b25786c3
-- title:
--   Raw categories, functors, isomorphisms, and equivalence
-- statement:
--   A raw category consists of objects, morphism data, a predicate selecting lawful morphisms, identities, and diagrammatic composition. A raw functor preserves lawful morphisms, identities, and composites. An isomorphism is a lawful morphism with a lawful two-sided inverse.
--
--   Two raw categories $C$ and $D$ are equivalent when there are functors $S:C\to D$ and $T:D\to C$ and natural families of isomorphisms
--
--   $$
--   \alpha_X:T(S(X))\xrightarrow{\sim}X,\qquad \beta_Y:S(T(Y))\xrightarrow{\sim}Y.
--   $$
--
--   This is the reusable category interface for the one-categorical equivalences in Proposition 8 and Theorem 36. The category laws are asserted separately as theorem items for the concrete categories.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 4–9, 12, 30, Definitions 1–3; Proposition 8; Theorem 36

import Mathlib

set_option autoImplicit false

namespace LieTwoAlg.Equiv

universe u

/-- Raw category data, with laws deferred to theorem items. -/
structure RawCat where
  Ob : Type (u+1)
  Hom : Ob → Ob → Type u
  IsHom : ∀ {X Y : Ob}, Hom X Y → Prop
  id : ∀ X : Ob, Hom X X
  comp : ∀ {X Y Z : Ob}, Hom X Y → Hom Y Z → Hom X Z

structure RawFunctor (C D : RawCat.{u}) where
  obj : C.Ob → D.Ob
  map : ∀ {X Y : C.Ob}, C.Hom X Y → D.Hom (obj X) (obj Y)

def RawFunctor.IsFunctor {C D : RawCat.{u}} (F : RawFunctor C D) : Prop :=
  (∀ {X Y} (f : C.Hom X Y), C.IsHom f → D.IsHom (F.map f)) ∧
  (∀ X, F.map (C.id X) = D.id (F.obj X)) ∧
  (∀ {X Y Z} (f : C.Hom X Y) (g : C.Hom Y Z), C.IsHom f → C.IsHom g →
    F.map (C.comp f g) = D.comp (F.map f) (F.map g))

def RawCat.IsIso (C : RawCat.{u}) {X Y : C.Ob} (f : C.Hom X Y) : Prop :=
  C.IsHom f ∧ ∃ g : C.Hom Y X, C.IsHom g ∧ C.comp f g = C.id X ∧ C.comp g f = C.id Y

/-- The selected morphisms satisfy the ordinary category laws. -/
def RawCat.IsCategory (C : RawCat.{u}) : Prop :=
  (∀ X, C.IsHom (C.id X)) ∧
  (∀ {X Y Z} (f : C.Hom X Y) (g : C.Hom Y Z),
    C.IsHom f → C.IsHom g → C.IsHom (C.comp f g)) ∧
  (∀ {W X Y Z} (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z),
    C.IsHom f → C.IsHom g → C.IsHom h →
      C.comp (C.comp f g) h = C.comp f (C.comp g h)) ∧
  (∀ {X Y} (f : C.Hom X Y), C.IsHom f →
    C.comp (C.id X) f = f ∧ C.comp f (C.id Y) = f)

/-- 1-categorical equivalence by quasi-inverse functors and natural isomorphisms. -/
def RawCat.Equivalent (C D : RawCat.{u}) : Prop :=
  C.IsCategory ∧ D.IsCategory ∧
  ∃ (S : RawFunctor C D) (T : RawFunctor D C)
    (α : ∀ X : C.Ob, C.Hom (T.obj (S.obj X)) X)
    (β : ∀ Y : D.Ob, D.Hom (S.obj (T.obj Y)) Y),
    S.IsFunctor ∧ T.IsFunctor ∧ (∀ X, C.IsIso (α X)) ∧ (∀ Y, D.IsIso (β Y)) ∧
    (∀ {X X'} (f : C.Hom X X'), C.IsHom f →
      C.comp (T.map (S.map f)) (α X') = C.comp (α X) f) ∧
    (∀ {Y Y'} (g : D.Hom Y Y'), D.IsHom g →
      D.comp (S.map (T.map g)) (β Y') = D.comp (β Y) g)

end LieTwoAlg.Equiv


