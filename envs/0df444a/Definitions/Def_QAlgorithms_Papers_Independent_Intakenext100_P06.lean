-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P06
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T22:44:52.544737+00:00
-- url     : https://prove2.me/theorems/ba130d0d-cbf1-4870-b215-2af9ab94b531
-- title:
--   Definitions for Hoàng Xuân Sính's Thesis: Categorifying Group Theory
-- statement:
--   The objects the formalized statements of *Hoàng Xuân Sính's Thesis: Categorifying Group Theory* (arXiv:2308.05119) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GrEquivalence`: Appendix A, Definitions 7,9–11, PDF pp. 18–19: strong monoidal functors in both directions and monoidal unit/counit isomorphisms. The printed GF ⇒ 1_N is corrected to GF ⇒ 1_M, as on PDF p. 17.
--   - `PicEquivalence`: Appendix A, Definitions 8,12, PDF pp. 18–19: symmetry is preserved by both strong monoidal functors, in addition to all monoidal comparisons.
--   - `Restrained`: Definition 6, PDF p. 13: every self-symmetry is the identity.
--   - `StrictCoherence`: Section 4 and Theorem 14, PDF pp. 9,19: strictness means identity coherence with the necessary endpoint equalities. It imposes no strict object-inverse axiom.
--   - `classGroup`: Section 3, PDF p. 7: the intrinsic group on isomorphism classes, using the pinned accepted construction with tensor as multiplication.
--   - `CoreObjects`: Section 5, PDF p. 11: only weakly tensor-invertible objects of an arbitrary monoidal category are retained.
--   - `coreForget`: Section 5, PDF p. 11: forget only the invertibility proofs.
--   - `ChainCategory`: Section 5, PDF p. 13: objects of the category of a two-term complex in degrees 1 → 0 are the actual elements of degree zero.
--   - `ChainTensorData`: Section 5, PDF p. 13: all tensor and coherence data of the concrete two-term construction. Zero labels are identity coherence maps after the endpoint equalities from the abelian group laws.
--   - `redirectObject`: Section 3, PDF p. 7: replacing the deleted object by the specified isomorphic survivor. The other objects remain literally the same.
--   - `redirectIso`: Section 3, PDF p. 7: the specified rerouting isomorphism.
--   - `RemovedObjects`: Section 3, PDF p. 7: delete exactly g, retaining all arrows between the remaining objects, before transporting monoidal data.
--   - `leftCoordinate`: Section 3, PDF pp. 7–8: left coordinates f tensor 1_(x inverse). Both endpoints are transported by the chosen weak-inverse isomorphism; no skeletal unitor is silently assumed to be the identity.
--   - `rightCoordinate`: Section 3, PDF p. 7: the printed automorphism-group identification uses right coordinates 1_(x inverse) tensor f, including counit transport.
--   - `actionCoordinate`: Section 3, PDF p. 7: the explicit conjugation action 1_x tensor a tensor 1_(x inverse), with right-unitor and inverse transport.
--   - `associatorCoordinate`: Section 3, PDF p. 8: the associator in left-action coordinates. Printed: 1_(xyz inverse) tensor alpha. Changed: alpha tensor 1_(xyz inverse). Reason: equations (6),(7) use the conjugation left action, incompatible with the unconverted printed right coordinate. Skeletality supplies the explicit endpoint transport of the associator before taking its coordinate.
--   - `pulledCoboundary`: Section 3, equation (7), PDF p. 8, and Theorem 15, pp. 19–20: the unnormalized coboundary with the action pulled back along phi. It takes values in the TARGET unit-automorphism group.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, https://arxiv.org/abs/2308.05119v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_objectClasses_group

/-!
John C. Baez, Hoàng Xuân Sính's Thesis: Categorifying Group Theory,
arXiv:2308.05119v2. Statements only; compilation is pending batch handoff.
The two imported paper modules are pinned accepted-library sources.
All new definitions are local to this paper. Deferred nodes are inventoried
individually in HARD.md and GAPS.json; none is replaced by a weaker statement.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory
open QAlgorithms.Papers.Independent.Gap48.P14
open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

/-- Appendix A, Definitions 7,9–11, PDF pp. 18–19: strong monoidal
functors in both directions and monoidal unit/counit isomorphisms.
The printed GF ⇒ 1_N is corrected to GF ⇒ 1_M, as on PDF p. 17. -/
structure GrEquivalence (C : Type u) (D : Type u1)
    [Category.{v} C] [Category.{v1} D]
    [MonoidalCategory C] [MonoidalCategory D] where
  e : C ≌ D
  forward : e.functor.Monoidal
  backward : e.inverse.Monoidal
  unit_monoidal : letI := forward; letI := backward
    NatTrans.IsMonoidal e.unitIso.hom
  counit_monoidal : letI := forward; letI := backward
    NatTrans.IsMonoidal e.counitIso.hom

/-- Sanity: the singleton has a full monoidal self-equivalence. -/
example : GrEquivalence (Discrete PUnit.{1}) (Discrete PUnit.{1}) where
  e := CategoryTheory.Equivalence.refl
  forward := inferInstance
  backward := inferInstance
  unit_monoidal := {
    unit := Subsingleton.elim _ _
    tensor := fun _ _ => Subsingleton.elim _ _ }
  counit_monoidal := {
    unit := Subsingleton.elim _ _
    tensor := fun _ _ => Subsingleton.elim _ _ }

/-- Appendix A, Definitions 8,12, PDF pp. 18–19: symmetry is preserved
by both strong monoidal functors, in addition to all monoidal comparisons. -/
structure PicEquivalence (C : Type u) (D : Type u1)
    [Category.{v} C] [Category.{v1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [SymmetricCategory D]
    extends GrEquivalence C D where
  forward_symmetry : letI := toGrEquivalence.forward
    ∀ x y : C,
      Functor.LaxMonoidal.μ e.functor x y ≫ e.functor.map (β_ x y).hom =
        (β_ (e.functor.obj x) (e.functor.obj y)).hom ≫
          Functor.LaxMonoidal.μ e.functor y x
  backward_symmetry : letI := toGrEquivalence.backward
    ∀ x y : D,
      Functor.LaxMonoidal.μ e.inverse x y ≫ e.inverse.map (β_ x y).hom =
        (β_ (e.inverse.obj x) (e.inverse.obj y)).hom ≫
          Functor.LaxMonoidal.μ e.inverse y x

/-- The unique symmetry on the discrete singleton, used only for sanity
examples. All coherence equations hold because each hom type is a subsingleton. -/
local instance singletonSymmetric : SymmetricCategory (Discrete PUnit.{1}) where
  braiding := fun _ _ => eqToIso (Subsingleton.elim _ _)
  braiding_naturality_right := by intros; exact Subsingleton.elim _ _
  braiding_naturality_left := by intros; exact Subsingleton.elim _ _
  hexagon_forward := by intros; exact Subsingleton.elim _ _
  hexagon_reverse := by intros; exact Subsingleton.elim _ _
  symmetry := by intros; exact Subsingleton.elim _ _

/-- Sanity: the singleton equivalence preserves its specified symmetry. -/
example : PicEquivalence (Discrete PUnit.{1}) (Discrete PUnit.{1}) where
  e := CategoryTheory.Equivalence.refl
  forward := inferInstance
  backward := inferInstance
  unit_monoidal := {
    unit := Subsingleton.elim _ _
    tensor := fun _ _ => Subsingleton.elim _ _ }
  counit_monoidal := {
    unit := Subsingleton.elim _ _
    tensor := fun _ _ => Subsingleton.elim _ _ }
  forward_symmetry := by intros; exact Subsingleton.elim _ _
  backward_symmetry := by intros; exact Subsingleton.elim _ _

/-- Definition 6, PDF p. 13: every self-symmetry is the identity. -/
def Restrained (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] : Prop :=
  ∀ x : C, (β_ x x).hom = 𝟙 (x ⊗ x)

/-- Sanity: restraint is satisfied by the discrete singleton. -/
example : Restrained (Discrete PUnit.{1}) := fun _ => Subsingleton.elim _ _

/-- Section 4 and Theorem 14, PDF pp. 9,19: strictness means identity
coherence with the necessary endpoint equalities. It imposes no strict
object-inverse axiom. -/
structure StrictCoherence (C : Type u) [Category.{v} C]
    [MonoidalCategory C] : Prop where
  assocObj : ∀ x y z : C, (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)
  leftObj : ∀ x : C, (𝟙_ C) ⊗ x = x
  rightObj : ∀ x : C, x ⊗ (𝟙_ C) = x
  assocHom : ∀ x y z, (α_ x y z).hom = eqToHom (assocObj x y z)
  leftHom : ∀ x, (λ_ x).hom = eqToHom (leftObj x)
  rightHom : ∀ x, (ρ_ x).hom = eqToHom (rightObj x)

/-- Sanity: identity coherence is inhabited, independently of inverse choices. -/
example : StrictCoherence (Discrete PUnit) where
  assocObj := fun _ _ _ => Subsingleton.elim _ _
  leftObj := fun _ => Subsingleton.elim _ _
  rightObj := fun _ => Subsingleton.elim _ _
  assocHom := fun _ _ _ => Subsingleton.elim _ _
  leftHom := fun _ => Subsingleton.elim _ _
  rightHom := fun _ => Subsingleton.elim _ _

/-- Section 3, PDF p. 7: the intrinsic group on isomorphism classes,
using the pinned accepted construction with tensor as multiplication. -/
noncomputable def classGroup {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (h : IsWeakTwoGroup C) : Group (ObjectClasses C) :=
  Classical.choose (objectClasses_group h)

/-- Sanity: the selected group multiplies actual representatives by tensor. -/
example {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (h : IsWeakTwoGroup C) (x y : C) :
    letI := classGroup h
    objectClass x * objectClass y = objectClass (x ⊗ y) :=
  (Classical.choose_spec (objectClasses_group h)).1 x y

/-- Section 5, PDF p. 11: only weakly tensor-invertible objects of
an arbitrary monoidal category are retained. -/
def CoreObjects (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  {x : C // ∃ y : C, IsWeakInverse x y}

/-- Section 5, PDF p. 11: core arrows are actual isomorphisms;
noninvertible ambient morphisms are excluded. -/
instance coreCategory {C : Type u} [Category.{v} C] [MonoidalCategory C] :
    Category (CoreObjects C) where
  Hom x y := x.val ≅ y.val
  id _ := Iso.refl _
  comp f g := f ≪≫ g
  id_comp := fun f => Iso.refl_trans f
  comp_id := fun f => Iso.trans_refl f
  assoc := fun f g h => Iso.trans_assoc f g h

/-- Section 5, PDF p. 11: forget only the invertibility proofs. -/
def coreForget {C : Type u} [Category.{v} C] [MonoidalCategory C] :
    CoreObjects C ⥤ C where
  obj x := x.val
  map f := f.hom

/-- Sanity: the core always contains the ambient tensor unit. -/
example {C : Type u} [Category.{v} C] [MonoidalCategory C] : CoreObjects C :=
  ⟨𝟙_ C, ⟨𝟙_ C, ⟨⟨λ_ (𝟙_ C)⟩, ⟨ρ_ (𝟙_ C)⟩⟩⟩⟩

/-- Section 5, PDF p. 13: objects of the category of a two-term
complex in degrees 1 → 0 are the actual elements of degree zero. -/
def ChainCategory {A : Type u} {B : Type v} [AddCommGroup A]
    [AddCommGroup B] (_d : B →+ A) := A

/-- Section 5, PDF p. 13: inherit exactly the degree-zero abelian group
on the differential-tagged object type; no additional algebra is chosen. -/
instance chainAddCommGroup {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B] (d : B →+ A) :
    AddCommGroup (ChainCategory d) :=
  inferInstanceAs (AddCommGroup A)

/-- Sanity: addition on the tagged object type is the original addition. -/
example {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (d : B →+ A) (x y : A) :
    ((x : ChainCategory d) + (y : ChainCategory d)) = (x + y : A) := rfl

/-- Section 5, PDF p. 13: actual subtype arrows dh=y-x, identity 0,
and vertical composition h' + h. A two-term complex needs no additional
square-zero or exactness hypothesis. -/
instance chainCategory {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B] (d : B →+ A) : Category (ChainCategory d) where
  Hom x y := {b : B // d b = y - x}
  id x := ⟨0, by
    change d 0 = (x : A) - (x : A)
    exact (map_zero d).trans (sub_self (x : A)).symm⟩
  comp f g := ⟨g.val + f.val, by rw [map_add, g.property, f.property]; abel⟩
  id_comp := by
    intros
    apply Subtype.ext
    simp
  comp_id := by
    intros
    apply Subtype.ext
    simp
  assoc := by
    intros
    apply Subtype.ext
    dsimp
    abel

/-- Sanity: identities and composition retain the page's actual labels. -/
example {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (d : B →+ A) {x y z : ChainCategory d} (f : x ⟶ y) (g : y ⟶ z) :
    (𝟙 x : x ⟶ x).val = 0 ∧ (f ≫ g).val = g.val + f.val := ⟨rfl, rfl⟩

/-- Section 5, PDF p. 13: all tensor and coherence data of the
concrete two-term construction. Zero labels are identity coherence
maps after the endpoint equalities from the abelian group laws. -/
structure ChainTensorData {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B] (d : B →+ A)
    (m : MonoidalCategory (ChainCategory d)) : Prop where
  tensorObj : letI := m; ∀ x y : ChainCategory d, x ⊗ y = x + y
  tensorUnit : letI := m; (𝟙_ (ChainCategory d)) = (0 : A)
  tensorHom : letI := m
    ∀ {x y z t : ChainCategory d} (f : x ⟶ y) (g : z ⟶ t),
      (f ⊗ₘ g).val = f.val + g.val
  associator : letI := m; ∀ x y z : ChainCategory d, (α_ x y z).hom.val = 0
  leftUnitor : letI := m; ∀ x : ChainCategory d, (λ_ x).hom.val = 0
  rightUnitor : letI := m; ∀ x : ChainCategory d, (ρ_ x).hom.val = 0

/-- Section 3, PDF p. 7: replacing the deleted object by the specified
isomorphic survivor. The other objects remain literally the same. -/
noncomputable def redirectObject {C : Type u} [Category.{v} C]
    (g survivor x : C) : C := by
  classical
  exact if x = g then survivor else x

/-- Section 3, PDF p. 7: the specified rerouting isomorphism. -/
noncomputable def redirectIso {C : Type u} [Category.{v} C]
    {g survivor : C} (f : g ≅ survivor) (x : C) :
    x ≅ redirectObject g survivor x := by
  classical
  by_cases h : x = g
  · simpa [redirectObject, h] using (eqToIso h ≪≫ f)
  · simpa [redirectObject, h] using (Iso.refl x)

/-- Section 3, PDF p. 7: delete exactly g, retaining all arrows
between the remaining objects, before transporting monoidal data. -/
abbrev RemovedObjects {C : Type u} [Category.{v} C] (g : C) :=
  ObjectProperty.FullSubcategory (fun x : C => x ≠ g)

/-- Sanity: redirection sends the removed object to the named survivor. -/
example {C : Type u} [Category.{v} C] (g survivor : C) :
    redirectObject g survivor g = survivor := by
  classical
  simp [redirectObject]

/-- Sanity: a remaining object carries its actual non-deletion certificate. -/
example {C : Type u} [Category.{v} C] {g survivor : C} (h : survivor ≠ g) :
    RemovedObjects g := ⟨survivor, h⟩

section AutomorphismCoordinates

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Section 3, PDF pp. 7–8: left coordinates f tensor 1_(x inverse).
Both endpoints are transported by the chosen weak-inverse isomorphism;
no skeletal unitor is silently assumed to be the identity. -/
noncomputable def leftCoordinate (h : IsWeakTwoGroup C) (x : C)
    (f : Aut x) : Aut (𝟙_ C) :=
  (chosenWeakInverseData h).unitIso x ≪≫
    (f ⊗ᵢ Iso.refl ((chosenWeakInverseData h).inverse x)) ≪≫
    ((chosenWeakInverseData h).unitIso x).symm

/-- Section 3, PDF p. 7: the printed automorphism-group identification
uses right coordinates 1_(x inverse) tensor f, including counit transport. -/
noncomputable def rightCoordinate (h : IsWeakTwoGroup C) (x : C)
    (f : Aut x) : Aut (𝟙_ C) :=
  ((chosenWeakInverseData h).counitIso x).symm ≪≫
    (Iso.refl ((chosenWeakInverseData h).inverse x) ⊗ᵢ f) ≪≫
    (chosenWeakInverseData h).counitIso x

/-- Section 3, PDF p. 7: the explicit conjugation action
1_x tensor a tensor 1_(x inverse), with right-unitor and inverse transport. -/
noncomputable def actionCoordinate (h : IsWeakTwoGroup C) (x : C)
    (a : Aut (𝟙_ C)) : Aut (𝟙_ C) :=
  let d := chosenWeakInverseData h
  let q := d.unitIso x ≪≫ whiskerRightIso (ρ_ x).symm (d.inverse x)
  q ≪≫ ((Iso.refl x ⊗ᵢ a) ⊗ᵢ Iso.refl (d.inverse x)) ≪≫ q.symm

/-- Sanity: all three actual transported coordinates are the identity
in the one-object, one-arrow case. -/
example (h : IsWeakTwoGroup (Discrete PUnit)) (x : Discrete PUnit)
    (f : Aut x) (a : Aut (𝟙_ (Discrete PUnit))) :
    leftCoordinate h x f = 1 ∧ rightCoordinate h x f = 1 ∧
      actionCoordinate h x a = 1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply Iso.ext
    exact Subsingleton.elim _ _

/-- Section 3, PDF p. 8: the associator in left-action coordinates.
Printed: 1_(xyz inverse) tensor alpha. Changed: alpha tensor 1_(xyz inverse).
Reason: equations (6),(7) use the conjugation left action, incompatible
with the unconverted printed right coordinate. Skeletality supplies the
explicit endpoint transport of the associator before taking its coordinate. -/
noncomputable def associatorCoordinate (h : IsWeakTwoGroup C) (hs : Skeletal C)
    (x y z : C) : Aut (𝟙_ C) :=
  leftCoordinate h ((x ⊗ y) ⊗ z)
    ((α_ x y z) ≪≫ eqToIso (hs ⟨α_ x y z⟩).symm)

/-- Sanity: on the singleton the associator cochain is zero
(multiplicatively, the identity automorphism). -/
example (h : IsWeakTwoGroup (Discrete PUnit)) (hs : Skeletal (Discrete PUnit))
    (x y z : Discrete PUnit) : associatorCoordinate h hs x y z = 1 := by
  apply Iso.ext
  exact Subsingleton.elim _ _

end AutomorphismCoordinates

/-- Section 3, equation (7), PDF p. 8, and Theorem 15, pp. 19–20:
the unnormalized coboundary with the action pulled back along phi.
It takes values in the TARGET unit-automorphism group. -/
noncomputable def pulledCoboundary
    {C : Type u} {D : Type u1} [Category.{v} C] [Category.{v1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (hD : IsWeakTwoGroup D) (phi : C → D)
    (f : C → C → Aut (𝟙_ D)) (x y z : C) : Aut (𝟙_ D) :=
  actionCoordinate hD (phi x) (f y z) * (f (x ⊗ y) z)⁻¹ *
    f x (y ⊗ z) * (f x y)⁻¹

/-- Sanity: the zero cochain of the singleton has zero coboundary
(multiplicatively, identity). No normalization condition is an input. -/
example (h : IsWeakTwoGroup (Discrete PUnit)) (x y z : Discrete PUnit) :
    pulledCoboundary h id (fun _ _ => 1) x y z = 1 := by
  apply Iso.ext
  exact Subsingleton.elim _ _

end QAlgorithms.Papers.Independent.Intakenext100.P06


