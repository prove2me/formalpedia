-- Prove2me | Definitions.Def_Mathlib_CategoryTheory_Corepresentable
-- name    : Mathlib_CategoryTheory_Corepresentable
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/82bd634c-a212-570c-bf2b-4992375bf081
-- title:
--   Representability from an initial object of the category of elements
-- statement:
--   For a functor $F : C \to \mathbf{Type}$ on a category $C$, Mathlib's category of elements $F.\mathrm{Elements}$ has as objects the pairs $(X, x)$ with $x \in F(X)$, a morphism $(X,x) \to (Y,y)$ being an arrow $f : X \to Y$ of $C$ with $F(f)(x) = y$. The first construction, `corepresentableByOfIsInitial`, takes an element $e = (X, x)$ together with a proof that $e$ is initial in $F.\mathrm{Elements}$ and produces a term of Mathlib's structure `F.CorepresentableBy X`: the bijection $(X \to Y) \simeq F(Y)$ it carries sends $f$ to $F(f)(x)$, its inverse sending $y \in F(Y)$ to the underlying arrow of the unique morphism $e \to (Y,y)$, and the required compatibility with composition is part of the structure. Thus $x$ is exhibited as a universal element. The lemma `isCorepresentable_of_hasInitial_elements` deduces `F.IsCorepresentable` from the existence of an initial object in $F.\mathrm{Elements}$, and `isCorepresentable_iff_hasInitial_elements` states the resulting equivalence, the forward direction being Mathlib's construction of an initial element from a corepresentation.
--
--   The second half is the contravariant counterpart. For $F : C^{\mathrm{op}} \to \mathbf{Type}$, objects of $F.\mathrm{Elements}$ are pairs $(X, x)$ with $X$ in $C^{\mathrm{op}}$ and $x \in F(X)$; given such an element that is initial, `representableByOfIsInitial` yields `F.RepresentableBy e.1.unop`, the bijection $(Y \to X) \simeq F(\mathrm{op}\,Y)$ sending $f$ to $F(f^{\mathrm{op}})(x)$. The companion lemmas `isRepresentable_of_hasInitial_elements` and `isRepresentable_iff_hasInitial_elements` give representability of $F$ and the equivalence with the existence of an initial object of $F.\mathrm{Elements}$.
--
--   **Relation to Mathlib.** Placed in Mathlib's `CategoryTheory.Functor` namespace and phrased entirely with Mathlib's `Elements`, `RepresentableBy`, `CorepresentableBy`, `IsRepresentable` and `IsCorepresentable`; it supplies the direction from an initial element to a (co)representation, complementing Mathlib's passage from a (co)representation to an initial element.
--
--   **Where it is used.** This criterion is used in the deformation-theoretic part of the development, where representability of a deformation functor is obtained by exhibiting an initial object in its category of elements, in the style of de Smit and Lenstra's treatment of universal deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_CategoryTheory_Corepresentable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe w v u

namespace CategoryTheory.Functor

open Limits

variable {C : Type u} [Category.{v} C]

section Corepresentable

variable {F : C ⥤ Type w}

@[simps]
def corepresentableByOfIsInitial (e : F.Elements) (he : IsInitial e) :
    F.CorepresentableBy e.1 where
  homEquiv {Y} :=
    { toFun f := F.map f e.2
      invFun y := (he.to (F.elementsMk Y y)).val
      left_inv f := congrArg Subtype.val
        (he.hom_ext (he.to (F.elementsMk Y (F.map f e.2))) ⟨f, rfl⟩)
      right_inv y := (he.to (F.elementsMk Y y)).property }
  homEquiv_comp {Y Y'} g f := by simp [FunctorToTypes.map_comp_apply]

lemma isCorepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsCorepresentable :=
  (corepresentableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isCorepresentable

lemma isCorepresentable_iff_hasInitial_elements :
    F.IsCorepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isCorepresentable_of_hasInitial_elements⟩

end Corepresentable

section Representable

variable {F : Cᵒᵖ ⥤ Type w}

@[simps]
def representableByOfIsInitial (e : F.Elements) (he : IsInitial e) :
    F.RepresentableBy e.1.unop where
  homEquiv {Y} :=
    { toFun f := F.map f.op e.2
      invFun y := (he.to (F.elementsMk (Opposite.op Y) y)).val.unop
      left_inv f := congrArg (fun g => Quiver.Hom.unop (Subtype.val g))
        (he.hom_ext (he.to (F.elementsMk (Opposite.op Y) (F.map f.op e.2))) ⟨f.op, rfl⟩)
      right_inv y := (he.to (F.elementsMk (Opposite.op Y) y)).property }
  homEquiv_comp {Y Y'} g f := by simp [FunctorToTypes.map_comp_apply]

lemma isRepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsRepresentable :=
  (representableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isRepresentable

lemma isRepresentable_iff_hasInitial_elements :
    F.IsRepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isRepresentable_of_hasInitial_elements⟩

end Representable

end CategoryTheory.Functor


