-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P43
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:47:18.944954+00:00
-- url     : https://prove2.me/theorems/2d3a75eb-9496-4c90-be22-621a1aea17e3
-- title:
--   Definitions for Higher gauge theory I: 2-Bundles
-- statement:
--   The objects the formalized statements of *Higher gauge theory I: 2-Bundles* (arXiv:math/0410328) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bundleCategoryStruct`: The raw bundle-category operations of §1.3.1, PDF p. 11. Objects are arbitrary arrows to B; maps are commuting triangles.
--   - `IsRightAction`: §1.4.3, equations (34), PDF pp. 15–16: a right action as equations on all generalized elements, equivalent to the two action diagrams. All operations are actual maps of C, so internal smoothness is retained when C is a smooth-space category.
--   - `RightGSpace`: §1.4.4, PDF p. 16: an internal right G-space. No freeness, faithfulness, transitivity or nonemptiness condition is imposed.
--   - `RightGMap`: §1.4.4, equation (35), PDF p. 16: a map commuting with the action. Testing on all generalized elements does not assume that C is concrete.
--   - `rightGSpaceCategoryStruct`: The prescribed raw identities and composition from §1.4.4, p. 16. Closure uses only the commuting action squares; category laws are not assumed on the resulting objects.
--   - `InternalRelation`: §1.1.4, PDF pp. 7–8: an internal equivalence relation, expressed using generalized elements. Joint monicity prevents extra relation witnesses.
--   - `CoverTheory`: The five standing cover axioms, §1.1.5, PDF p. 8. This is the abstract formulation explicitly allowed by the source. It does not identify arbitrary regular epimorphisms with smooth covers.
--   - `CechData`: The two specified pullback cones constructing U[2] and U[3], §1.1.5, PDF pp. 9–10. No global pullback-existence assumption is made.
--   - `cechDiagonal`: The diagonal j[00], equation (17), PDF p. 9, constructed by universality.
--   - `cechSkip`: The skip map j[02], equation (20), PDF p. 10, constructed by universality.
--   - `SatisfiesGamma`: §1.5.1, equation (39), PDF p. 17: multiplicativity alone; the diagonal unit law is deliberately absent.
--   - `TwoPullbackCone`: §2.1.3, equation (70), PDF p. 29: a weak pullback cone, carrying its specified invertible comparison cell.
--   - `TwoConeMorphism`: §2.1.3, equations (71)–(72), PDF p. 30: a cone morphism with both invertible comparison cells and their pasting equation. The ambient associators are explicit.
--   - `IsWeakTwoPullback`: §2.1.3, equations (73)–(74), PDF p. 30: the weak universal property. A lift exists, and every other lift is joined to it by a unique invertible cell compatible with both cone comparison cells.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, https://arxiv.org/abs/math/0410328v3

import Mathlib

/-!
Statements from Toby Bartels, Higher gauge theory I: 2-Bundles,
arXiv:math/0410328v3. New definitions are local to this paper.
The categorical statements use the source's explicitly permitted abstract
arrow-theoretic formulation. No concrete smooth cover realization is asserted.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

/-- The raw bundle-category operations of §1.3.1, PDF p. 11.
Objects are arbitrary arrows to B; maps are commuting triangles. -/
def bundleCategoryStruct (B : C) : CategoryStruct (Over B) where
  Hom E Eprime := Over.Hom E Eprime
  id E := Over.homMk (𝟙 E.left) (by simp)
  comp f g := Over.homMk (f.left ≫ g.left) (by simp [Category.assoc])

/-- Sanity: the identity on a bundle is the identity on its total space. -/
example (B : C) (E : Over B) :
    ((bundleCategoryStruct B).id E).left = 𝟙 E.left := rfl

variable [CartesianMonoidalCategory C]

/-- §1.4.3, equations (34), PDF pp. 15–16: a right action as equations
on all generalized elements, equivalent to the two action diagrams.
All operations are actual maps of C, so internal smoothness is retained
when C is a smooth-space category. -/
def IsRightAction (G F : C) [GrpObj G] (r : F ⊗ G ⟶ F) : Prop :=
  (∀ (T : C) (a : T ⟶ F) (x y : T ⟶ G),
    lift (lift a x ≫ r) y ≫ r = lift a (lift x y ≫ MonObj.mul) ≫ r) ∧
  (∀ (T : C) (a : T ⟶ F),
    lift a (toUnit T ≫ MonObj.one (X := G)) ≫ r = a)

/-- Sanity: the terminal space has the trivial right action of every
internal group, including groups with a nonfaithful action on it. -/
example (G : C) [GrpObj G] :
    IsRightAction G (𝟙_ C) (toUnit ((𝟙_ C) ⊗ G)) := by
  constructor
  · intro T a x y
    exact toUnit_unique _ _
  · intro T a
    exact toUnit_unique _ _

/-- §1.4.4, PDF p. 16: an internal right G-space. No freeness,
faithfulness, transitivity or nonemptiness condition is imposed. -/
structure RightGSpace (G : C) [GrpObj G] where
  space : C
  actionMap : space ⊗ G ⟶ space
  actionLaws : IsRightAction G space actionMap

/-- §1.4.4, equation (35), PDF p. 16: a map commuting with the action.
Testing on all generalized elements does not assume that C is concrete. -/
structure RightGMap {G : C} [GrpObj G] (A D : RightGSpace G) where
  map : A.space ⟶ D.space
  equivariant : ∀ (T : C) (a : T ⟶ A.space) (x : T ⟶ G),
    (lift a x ≫ A.actionMap) ≫ map = lift (a ≫ map) x ≫ D.actionMap

/-- The prescribed raw identities and composition from §1.4.4, p. 16.
Closure uses only the commuting action squares; category laws are not
assumed on the resulting objects. -/
def rightGSpaceCategoryStruct (G : C) [GrpObj G] :
    CategoryStruct (RightGSpace G) where
  Hom A D := RightGMap A D
  id A := ⟨𝟙 A.space, by intro T a x; simp⟩
  comp f g := ⟨f.map ≫ g.map, by
    intro T a x
    calc
      (lift a x ≫ _) ≫ (f.map ≫ g.map) =
          (lift (a ≫ f.map) x ≫ _) ≫ g.map := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ g.map) (f.equivariant T a x)
      _ = lift (a ≫ (f.map ≫ g.map)) x ≫ _ := by
        simpa only [Category.assoc] using g.equivariant T (a ≫ f.map) x⟩

/-- Sanity: composition keeps the actual underlying maps in source order. -/
example (G : C) [GrpObj G] {A D E : RightGSpace G}
    (f : RightGMap A D) (g : RightGMap D E) :
    ((rightGSpaceCategoryStruct G).comp f g).map = f.map ≫ g.map := rfl

/-- §1.1.4, PDF pp. 7–8: an internal equivalence relation, expressed
using generalized elements. Joint monicity prevents extra relation witnesses. -/
structure InternalRelation (U : C) where
  relationSpace : C
  first : relationSpace ⟶ U
  second : relationSpace ⟶ U
  jointlyMonic : ∀ (T : C) (a b : T ⟶ relationSpace),
    a ≫ first = b ≫ first → a ≫ second = b ≫ second → a = b
  reflexive : ∀ (T : C) (x : T ⟶ U),
    ∃ a : T ⟶ relationSpace, a ≫ first = x ∧ a ≫ second = x
  euclidean : ∀ (T : C) (a b : T ⟶ relationSpace),
    a ≫ first = b ≫ first →
      ∃ c : T ⟶ relationSpace,
        c ≫ first = a ≫ second ∧ c ≫ second = b ≫ second

/-- The five standing cover axioms, §1.1.5, PDF p. 8.
This is the abstract formulation explicitly allowed by the source.
It does not identify arbitrary regular epimorphisms with smooth covers. -/
structure CoverTheory where
  covers : ∀ {U B : C}, (U ⟶ B) → Prop
  isomorphisms : ∀ {U B : C} (j : U ⟶ B), IsIso j → covers j
  composites : ∀ {U V B : C} (j : U ⟶ V) (k : V ⟶ B),
    covers j → covers k → covers (j ≫ k)
  pullbacks : ∀ {U B X : C} (j : U ⟶ B) (f : X ⟶ B), covers j →
    ∃ (P : C) (p1 : P ⟶ U) (p2 : P ⟶ X),
      IsPullback p1 p2 j f ∧ covers p2
  quotients : ∀ {U : C} (R : InternalRelation U), covers R.first →
    ∃ (Q : C) (q : U ⟶ Q) (h : R.first ≫ q = R.second ≫ q),
      covers q ∧ Nonempty (IsColimit (Cofork.ofπ q h))
  kernelQuotients : ∀ {U B P : C} (j : U ⟶ B) (p1 p2 : P ⟶ U),
    covers j → (h : IsPullback p1 p2 j j) →
      Nonempty (IsColimit (Cofork.ofπ j h.w))

/-- Sanity: all isomorphisms are covers, including the identity.
This checks that CoverTheory carries the source's first axiom. -/
example (S : CoverTheory (C := C)) (U : C) : S.covers (𝟙 U) :=
  S.isomorphisms _ (inferInstance : IsIso (𝟙 U))

/-- The two specified pullback cones constructing U[2] and U[3],
§1.1.5, PDF pp. 9–10. No global pullback-existence assumption is made. -/
structure CechData {U B : C} (j : U ⟶ B) where
  pairSpace : C
  first : pairSpace ⟶ U
  second : pairSpace ⟶ U
  square : IsPullback first second j j
  tripleSpace : C
  pair01 : tripleSpace ⟶ pairSpace
  pair12 : tripleSpace ⟶ pairSpace
  tripleSquare : IsPullback pair01 pair12 second first

/-- The diagonal j[00], equation (17), PDF p. 9, constructed by universality. -/
noncomputable def cechDiagonal {U B : C} {j : U ⟶ B} (K : CechData j) :
    U ⟶ K.pairSpace :=
  K.square.lift (𝟙 U) (𝟙 U) (by simp)

/-- The skip map j[02], equation (20), PDF p. 10, constructed by universality. -/
noncomputable def cechSkip {U B : C} {j : U ⟶ B} (K : CechData j) :
    K.tripleSpace ⟶ K.pairSpace :=
  K.square.lift (K.pair01 ≫ K.first) (K.pair12 ≫ K.second) (by
    calc
      (K.pair01 ≫ K.first) ≫ j = (K.pair01 ≫ K.second) ≫ j := by
        simp only [Category.assoc, K.square.w]
      _ = (K.pair12 ≫ K.first) ≫ j := by rw [K.tripleSquare.w]
      _ = (K.pair12 ≫ K.second) ≫ j := by
        simp only [Category.assoc, K.square.w])

/-- §1.5.1, equation (39), PDF p. 17: multiplicativity alone;
the diagonal unit law is deliberately absent. -/
def SatisfiesGamma {U B : C} {j : U ⟶ B} (K : CechData j)
    (G : C) [GrpObj G] (g : K.pairSpace ⟶ G) : Prop :=
  lift (K.pair01 ≫ g) (K.pair12 ≫ g) ≫ MonObj.mul = cechSkip K ≫ g

/-- Sanity: the constructed diagonal has both components equal to identity. -/
example {U B : C} {j : U ⟶ B} (K : CechData j) :
    cechDiagonal K ≫ K.first = 𝟙 U ∧ cechDiagonal K ≫ K.second = 𝟙 U := by
  constructor <;> simp [cechDiagonal]

end Ordinary

section WeakPullbacks

open CategoryTheory.Bicategory

variable {D : Type u} [Bicategory.{w, v} D]

/-- §2.1.3, equation (70), PDF p. 29: a weak pullback cone, carrying
its specified invertible comparison cell. -/
structure TwoPullbackCone {X Y Z : D} (f : X ⟶ Z) (g : Y ⟶ Z) where
  vertex : D
  first : vertex ⟶ X
  second : vertex ⟶ Y
  comparison : first ≫ f ≅ second ≫ g

/-- §2.1.3, equations (71)–(72), PDF p. 30: a cone morphism with
both invertible comparison cells and their pasting equation.
The ambient associators are explicit. -/
structure TwoConeMorphism {X Y Z : D} {f : X ⟶ Z} {g : Y ⟶ Z}
    (A P : TwoPullbackCone f g) where
  map : A.vertex ⟶ P.vertex
  firstCell : A.first ≅ map ≫ P.first
  secondCell : A.second ≅ map ≫ P.second
  coherence : A.comparison.hom =
    (firstCell.hom ▷ f) ≫ (α_ map P.first f).hom ≫
      (map ◁ P.comparison.hom) ≫ (α_ map P.second g).inv ≫ (secondCell.inv ▷ g)

/-- §2.1.3, equations (73)–(74), PDF p. 30: the weak universal
property. A lift exists, and every other lift is joined to it by a
unique invertible cell compatible with both cone comparison cells. -/
def IsWeakTwoPullback {X Y Z : D} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoPullbackCone f g) : Prop :=
  ∀ A : TwoPullbackCone f g, ∃ u : TwoConeMorphism A P,
    ∀ uprime : TwoConeMorphism A P,
      ∃! nu : u.map ≅ uprime.map,
        u.firstCell.hom ≫ (nu.hom ▷ P.first) = uprime.firstCell.hom ∧
        u.secondCell.hom ≫ (nu.hom ▷ P.second) = uprime.secondCell.hom

/-- Sanity: comparison cells are invertible; they are not equations
between the cone's two composite 1-morphisms. -/
example {X Y Z : D} {f : X ⟶ Z} {g : Y ⟶ Z}
    (P : TwoPullbackCone f g) :
    P.comparison.hom ≫ P.comparison.inv = 𝟙 (P.first ≫ f) := by simp

end WeakPullbacks

end QAlgorithms.Papers.Independent.Intakenext100.P43


