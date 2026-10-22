-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14
-- name    : QAlgorithms_Papers_Independent_Gap48_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:45:27.687336+00:00
-- url     : https://prove2.me/theorems/749c1dce-4427-4bc3-be81-d01f804d664c
-- title:
--   Definitions for Higher-Dimensional Algebra V: 2-Groups
-- statement:
--   The objects the formalized statements of *Higher-Dimensional Algebra V: 2-Groups* (arXiv:math/0307200) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsWeakInverse`: Definition 1, PDF pp. 7–8: two-sided weak inverse, without chosen maps.
--   - `IsWeakTwoGroup`: Definition 2, PDF p. 8: arbitrary monoidal groupoid with weak inverses. Neither strict tensor inverses nor a trivial associator are required.
--   - `FirstTriangle`: The first zig-zag, PDF p. 10, with both unitors and the associator.
--   - `SecondTriangle`: The second zig-zag, PDF p. 10; no first-triangle hypothesis is built in.
--   - `WeakInverseData`: Chosen preliminary inverse data of PDF p. 19, before any zig-zag law.
--   - `CoherentInverseData`: Definition 7, PDF p. 10: specified adjoint equivalences for all objects. Together with invertibility of every arrow this is coherent 2-group structure.
--   - `chosenWeakInverseData`: Classical selection of the preliminary data, PDF pp. 19,25. This definition chooses only existing isomorphisms, without assuming triangles.
--   - `improvedUnitIso`: The full composite defining the improved unit, PDF p. 19. It leaves the counit unchanged and cancels the first x tensor y pair.
--   - `alternativeUnitIso`: The alternative diagram in Lemma 15, PDF p. 20: cancel the last pair.
--   - `ObjectClasses`: Intrinsic object isomorphism classes, PDF pp. 5,56,58. The underlying quotient does not assume a skeletal or strict presentation.
--   - `objectClass`: Projection of an actual object to its isomorphism class, PDF pp. 5,56.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, https://arxiv.org/abs/math/0307200v3

import Mathlib

/-!
Baez–Lauda, Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3.
Local definitions have complete bodies. Theorems are statements only.
Other inventoried results are explicitly deferred in this chunk's HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Definition 1, PDF pp. 7–8: two-sided weak inverse, without chosen maps. -/
def IsWeakInverse (x y : C) : Prop :=
  Nonempty (x ⊗ y ≅ 𝟙_ C) ∧ Nonempty (y ⊗ x ≅ 𝟙_ C)

/-- Definition 2, PDF p. 8: arbitrary monoidal groupoid with weak inverses.
Neither strict tensor inverses nor a trivial associator are required. -/
def IsWeakTwoGroup (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop :=
  (∀ (x y : C) (f : x ⟶ y), IsIso f) ∧
  (∀ x : C, ∃ y : C, IsWeakInverse x y)

/-- Sanity: the unit is a weak inverse of itself, even with nontrivial unitors. -/
example : IsWeakInverse (𝟙_ C) (𝟙_ C) :=
  ⟨⟨λ_ (𝟙_ C)⟩, ⟨ρ_ (𝟙_ C)⟩⟩

/-- Sanity: the discrete singleton is a nonempty weak 2-group. -/
example : IsWeakTwoGroup (Discrete PUnit) := by
  constructor
  · intro x y f
    infer_instance
  · intro x
    exact ⟨x, ⟨⟨eqToIso (Subsingleton.elim _ _)⟩,
      ⟨eqToIso (Subsingleton.elim _ _)⟩⟩⟩

/-- The first zig-zag, PDF p. 10, with both unitors and the associator. -/
def FirstTriangle {x y : C} (i : 𝟙_ C ≅ x ⊗ y) (e : y ⊗ x ≅ 𝟙_ C) : Prop :=
  i.hom ▷ x ≫ (α_ x y x).hom ≫ x ◁ e.hom =
    (λ_ x).hom ≫ (ρ_ x).inv

/-- The second zig-zag, PDF p. 10; no first-triangle hypothesis is built in. -/
def SecondTriangle {x y : C} (i : 𝟙_ C ≅ x ⊗ y) (e : y ⊗ x ≅ 𝟙_ C) : Prop :=
  y ◁ i.hom ≫ (α_ y x y).inv ≫ e.hom ▷ y =
    (ρ_ y).hom ≫ (λ_ y).inv

/-- Chosen preliminary inverse data of PDF p. 19, before any zig-zag law. -/
structure WeakInverseData (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  inverse : C → C
  unitIso : ∀ x, 𝟙_ C ≅ x ⊗ inverse x
  counitIso : ∀ x, inverse x ⊗ x ≅ 𝟙_ C

/-- Definition 7, PDF p. 10: specified adjoint equivalences for all objects.
Together with invertibility of every arrow this is coherent 2-group structure. -/
structure CoherentInverseData (C : Type u) [Category.{v} C] [MonoidalCategory C]
    extends WeakInverseData C where
  firstTriangle : ∀ x, FirstTriangle (unitIso x) (counitIso x)
  secondTriangle : ∀ x, SecondTriangle (unitIso x) (counitIso x)

/-- Sanity: all the chosen maps and both zig-zags exist on the singleton. -/
example : CoherentInverseData (Discrete PUnit) where
  inverse := fun x => x
  unitIso := fun _ => eqToIso (Subsingleton.elim _ _)
  counitIso := fun _ => eqToIso (Subsingleton.elim _ _)
  firstTriangle := fun _ => Subsingleton.elim _ _
  secondTriangle := fun _ => Subsingleton.elim _ _

/-- Classical selection of the preliminary data, PDF pp. 19,25.
This definition chooses only existing isomorphisms, without assuming triangles. -/
noncomputable def chosenWeakInverseData (h : IsWeakTwoGroup C) : WeakInverseData C where
  inverse x := Classical.choose (h.2 x)
  unitIso x := (Classical.choice ((Classical.choose_spec (h.2 x)).1)).symm
  counitIso x := Classical.choice ((Classical.choose_spec (h.2 x)).2)

/-- Sanity: the selected inverse is the object selected from the weak-inverse witness. -/
example (h : IsWeakTwoGroup C) (x : C) :
    (chosenWeakInverseData h).inverse x = Classical.choose (h.2 x) := rfl

/-- The full composite defining the improved unit, PDF p. 19.
It leaves the counit unchanged and cancels the first x tensor y pair. -/
def improvedUnitIso {x y : C} (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) : 𝟙_ C ≅ x ⊗ y :=
  i ≪≫ whiskerLeftIso x (λ_ y).symm ≪≫
    whiskerLeftIso x (whiskerRightIso e.symm y) ≪≫
    whiskerLeftIso x (α_ y x y) ≪≫ (α_ x y (x ⊗ y)).symm ≪≫
    whiskerRightIso i.symm (x ⊗ y) ≪≫ (α_ (𝟙_ C) x y).symm ≪≫
    whiskerRightIso (λ_ x) y

/-- The alternative diagram in Lemma 15, PDF p. 20: cancel the last pair. -/
def alternativeUnitIso {x y : C} (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) : 𝟙_ C ≅ x ⊗ y :=
  i ≪≫ whiskerLeftIso x (λ_ y).symm ≪≫
    whiskerLeftIso x (whiskerRightIso e.symm y) ≪≫
    whiskerLeftIso x (α_ y x y) ≪≫ (α_ x y (x ⊗ y)).symm ≪≫
    whiskerLeftIso (x ⊗ y) i.symm ≪≫ ρ_ (x ⊗ y)

/-- Sanity: both computed diagrams reduce to the sole arrow on the singleton. -/
example (x y : Discrete PUnit) (i : 𝟙_ (Discrete PUnit) ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ (Discrete PUnit)) :
    (improvedUnitIso i e).hom = (Iso.refl (𝟙_ (Discrete PUnit))).hom ≫ i.hom ∧
    (alternativeUnitIso i e).hom = i.hom :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end Inverses

/-- Intrinsic object isomorphism classes, PDF pp. 5,56,58.
The underlying quotient does not assume a skeletal or strict presentation. -/
def ObjectClasses (C : Type u) [Category.{v} C] : Type u :=
  Quotient (CategoryTheory.isIsomorphicSetoid C)

/-- Projection of an actual object to its isomorphism class, PDF pp. 5,56. -/
def objectClass {C : Type u} [Category.{v} C] (x : C) : ObjectClasses C :=
  Quotient.mk (CategoryTheory.isIsomorphicSetoid C) x

/-- Sanity: an actual isomorphism identifies precisely the intended representatives. -/
example {C : Type u} [Category.{v} C] {x y : C} (i : x ≅ y) :
    objectClass x = objectClass y := Quotient.sound ⟨i⟩

end QAlgorithms.Papers.Independent.Gap48.P14


