-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59
-- name    : QAlgorithms_Papers_Independent_Intake100_P59
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:02:48.985288+00:00
-- url     : https://prove2.me/theorems/1508c1de-3a09-4668-9140-a7136ad8a75a
-- title:
--   Definitions for Orbifolds as stacks?
-- statement:
--   The objects the formalized statements of *Orbifolds as stacks?* (arXiv:0806.4160) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsCFG`: Definition 4.2, PDF p.18: a category fibered in groupoids. Every arrow admits the unique lifting of base triangles required by (2); this is a condition on all arrows, not only a chosen class of cartesian ones. `IsHomLift` records equality of both projected endpoints and the base arrow.
--   - `OverFunctor`: Definition 4.8, PDF p.19: a functor strictly over the fixed base. The corresponding morphisms below are required to be vertical, as explicitly used in the proof of 2-Yoneda on PDF pp.23–24.
--   - `yonedaEvaluation`: The evaluation functor of Lemma 4.19, PDF p.23. The representable CFG is the slice `Over X` with the domain projection; the target is the strict fiber, whose arrows lie over the base identity.
-- source:
--   Orbifolds as stacks?, arXiv:0806.4160v2, https://arxiv.org/abs/0806.4160v2

import Mathlib

/-!
Statements from Eugene Lerman, *Orbifolds as stacks?*, arXiv:0806.4160v2.
The smooth geometric interfaces not constructed in this module are explicitly
inventoried in this unit's HARD.md and GAPS.json. No surrogate geometry is used.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P59

open CategoryTheory

universe u v uC vC uD vD uE vE

/-- Definition 4.2, PDF p.18: a category fibered in groupoids.
Every arrow admits the unique lifting of base triangles required by (2);
this is a condition on all arrows, not only a chosen class of cartesian ones.
`IsHomLift` records equality of both projected endpoints and the base arrow. -/
structure IsCFG {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (p : D ⥤ C) : Prop where
  lift : ∀ (x : D) (Y : C) (f : Y ⟶ p.obj x),
    ∃ (y : D) (h : y ⟶ x), p.IsHomLift f h
  triangle : ∀ {x y z : D} (f : x ⟶ z) (h : y ⟶ z)
    (g : p.obj x ⟶ p.obj y), g ≫ p.map h = p.map f →
      ∃! k : x ⟶ y, p.map k = g ∧ k ≫ h = f

/-- The identity projection is a CFG even when the base is not a groupoid. -/
example {C : Type uC} [Category.{vC} C] : IsCFG (𝟭 C) where
  lift x Y f := ⟨Y, f, IsHomLift.map (𝟭 C) f⟩
  triangle f h g hcomm := ⟨g, ⟨rfl, hcomm⟩, fun k hk => hk.1⟩

/-- Definition 4.8, PDF p.19: a functor strictly over the fixed base.
The corresponding morphisms below are required to be vertical, as explicitly
used in the proof of 2-Yoneda on PDF pp.23–24. -/
structure OverFunctor {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (p : D ⥤ C) (q : E ⥤ C) where
  val : D ⥤ E
  commutes : val ⋙ q = p

namespace OverFunctor

variable {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    {p : D ⥤ C} {q : E ⥤ C}

/-- Vertical natural transformations, with their ordinary componentwise composition. -/
instance category : Category (OverFunctor p q) where
  Hom F G := {α : F.val ⟶ G.val //
    ∀ x : D, q.IsHomLift (𝟙 (p.obj x)) (α.app x)}
  id F := ⟨𝟙 F.val, fun x =>
    IsHomLift.id (congrArg (fun K : D ⥤ C => K.obj x) F.commutes)⟩
  comp α β := ⟨α.1 ≫ β.1, fun x => by
    haveI := α.2 x
    haveI := β.2 x
    exact IsHomLift.comp_of_lift_id q (p.obj x) (α.1.app x) (β.1.app x)⟩
  id_comp α := Subtype.ext (Category.id_comp α.1)
  comp_id α := Subtype.ext (Category.comp_id α.1)
  assoc α β γ := Subtype.ext (Category.assoc α.1 β.1 γ.1)

/-- Identity transformations in the over-base Hom category project to identities. -/
example (F : OverFunctor p q) (x : D) :
    q.IsHomLift (𝟙 (p.obj x)) ((𝟙 F : F ⟶ F).1.app x) :=
  (𝟙 F : F ⟶ F).2 x

end OverFunctor

/-- The evaluation functor of Lemma 4.19, PDF p.23.
The representable CFG is the slice `Over X` with the domain projection;
the target is the strict fiber, whose arrows lie over the base identity. -/
def yonedaEvaluation {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (p : D ⥤ C) (X : C) :
    OverFunctor (Over.forget X) p ⥤ p.Fiber X where
  obj F := ⟨F.val.obj (Over.mk (𝟙 X)),
    congrArg (fun K : Over X ⥤ C => K.obj (Over.mk (𝟙 X))) F.commutes⟩
  map α := ⟨α.1.app (Over.mk (𝟙 X)), α.2 (Over.mk (𝟙 X))⟩
  map_id F := rfl
  map_comp α β := rfl

/-- Evaluation on objects really is evaluation at the identity, with no choice of pullbacks. -/
example {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (p : D ⥤ C) (X : C)
    (F : OverFunctor (Over.forget X) p) :
    ((yonedaEvaluation p X).obj F).1 = F.val.obj (Over.mk (𝟙 X)) := rfl

end QAlgorithms.Papers.Independent.Intake100.P59


