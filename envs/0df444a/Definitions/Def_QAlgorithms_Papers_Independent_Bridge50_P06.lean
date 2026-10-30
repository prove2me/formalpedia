-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P06
-- name    : QAlgorithms_Papers_Independent_Bridge50_P06
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:13:27.343992+00:00
-- url     : https://prove2.me/theorems/1bdaeb27-8656-42a6-a078-5121a6e19991
-- title:
--   Definitions for Four Equivalent Versions of Non-Abelian Gerbes
-- statement:
--   The objects the formalized statements of *Four Equivalent Versions of Non-Abelian Gerbes* (arXiv:1103.4815) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LocallyFullyFaithful`: Full faithfulness on each Hom-category means bijectivity on every set of 2-morphisms, not essential surjectivity on 1-morphisms (Appendix B, PDF p. 60).
--   - `ChosenLifts`: The two families of chosen lifts in Lemma B.1 (PDF pp. 59--60). `objectComparison` includes an adjoint inverse and the zigzag identities. No pseudofunctor laws or compatibility between the chosen lifts are assumed.
--   - `conjugatedArrow`: The specific conjugated arrow used to construct G in Lemma B.1, PDF p. 60: tilde(g) = (xi_Y2 composed with g) composed with xi_Y1 inverse. Lean's composition is written from left to right.
--   - `inverseArrow`: The prescribed underlying arrow of the inverse pseudofunctor (PDF p. 60). This is computed from the chosen lifts; it is not an independent inverse.
--   - `inverseCounitComponent`: The prescribed object component of b : G composed with F to id_C in the construction of Lemma B.1 (PDF p. 61).
--   - `identityChosenLifts`: Identity-pseudofunctor lift data, a sanity instance of B.1's hypotheses. It is defined for arbitrary bicategories, including those with noninvertible 2-morphisms and those with no objects.
-- source:
--   Four Equivalent Versions of Non-Abelian Gerbes, arXiv:1103.4815v3, https://arxiv.org/abs/1103.4815v3

import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
Statements from Nikolaus--Waldorf, arXiv:1103.4815v3.
The geometric nodes deferred by this draft are listed in the assigned unit's HARD.md.
-/

namespace QAlgorithms.Papers.Independent.Bridge50.P06

open CategoryTheory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe uC uD vC vD wC wD

variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]

/-- Full faithfulness on each Hom-category means bijectivity on every set of
2-morphisms, not essential surjectivity on 1-morphisms (Appendix B, PDF p. 60). -/
def LocallyFullyFaithful (F : Pseudofunctor C D) : Prop :=
  ∀ (X1 X2 : C) (f g : X1 ⟶ X2),
    Function.Bijective (fun (eta : f ⟶ g) => F.map₂ eta)

/-- The two families of chosen lifts in Lemma B.1 (PDF pp. 59--60).
`objectComparison` includes an adjoint inverse and the zigzag identities.
No pseudofunctor laws or compatibility between the chosen lifts are assumed. -/
structure ChosenLifts (F : Pseudofunctor C D) where
  objectLift : D → C
  objectComparison (Y : D) : Bicategory.Equivalence Y (F.obj (objectLift Y))
  morphismLift {X1 X2 : C} (g : F.obj X1 ⟶ F.obj X2) : X1 ⟶ X2
  morphismComparison {X1 X2 : C} (g : F.obj X1 ⟶ F.obj X2) :
    g ≅ F.map (morphismLift g)

/-- The specific conjugated arrow used to construct G in Lemma B.1,
PDF p. 60: tilde(g) = (xi_Y2 composed with g) composed with xi_Y1 inverse.
Lean's composition is written from left to right. -/
def conjugatedArrow {F : Pseudofunctor C D} (L : ChosenLifts F)
    {Y1 Y2 : D} (g : Y1 ⟶ Y2) :
    F.obj (L.objectLift Y1) ⟶ F.obj (L.objectLift Y2) :=
  (L.objectComparison Y1).inv ≫ (g ≫ (L.objectComparison Y2).hom)

/-- The prescribed underlying arrow of the inverse pseudofunctor (PDF p. 60).
This is computed from the chosen lifts; it is not an independent inverse. -/
def inverseArrow {F : Pseudofunctor C D} (L : ChosenLifts F)
    {Y1 Y2 : D} (g : Y1 ⟶ Y2) : L.objectLift Y1 ⟶ L.objectLift Y2 :=
  L.morphismLift (conjugatedArrow L g)

/-- The prescribed object component of b : G composed with F to id_C
in the construction of Lemma B.1 (PDF p. 61). -/
def inverseCounitComponent {F : Pseudofunctor C D} (L : ChosenLifts F)
    (X : C) : L.objectLift (F.obj X) ⟶ X :=
  L.morphismLift (L.objectComparison (F.obj X)).inv

/-- Identity-pseudofunctor lift data, a sanity instance of B.1's hypotheses.
It is defined for arbitrary bicategories, including those with noninvertible
2-morphisms and those with no objects. -/
def identityChosenLifts (C : Type uC) [Bicategory.{wC, vC} C] :
    ChosenLifts (Pseudofunctor.id C) where
  objectLift := fun X => X
  objectComparison := fun X => Bicategory.Equivalence.id X
  morphismLift := fun g => g
  morphismComparison := fun g => Iso.refl g

example (X : C) : (identityChosenLifts C).objectLift X = X := by
  rfl

example {X1 X2 : C} (g : X1 ⟶ X2) :
    (identityChosenLifts C).morphismLift g = g := by
  rfl

example : LocallyFullyFaithful (Pseudofunctor.id C) := by
  intro X1 X2 f g
  exact Function.bijective_id

end QAlgorithms.Papers.Independent.Bridge50.P06


