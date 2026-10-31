-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
-- name    : QAlgorithms_Papers_Independent_Intake100_P20
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T16:26:44.361503+00:00
-- url     : https://prove2.me/theorems/9ad31a0d-518c-40d4-b5f9-b43dbc473cc9
-- title:
--   Definitions for Group Objects and Internal Categories
-- statement:
--   The objects the formalized statements of *Group Objects and Internal Categories* (arXiv:math/0212065) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GroupMaps`: PDF pp. 1–3: the three maps of an unbundled group object in Set.
--   - `GroupDiagrams`: PDF pp. 1–3: associativity, both units, and both inverse diagrams.
--   - `mapsOfGroup`: PDF p. 3: read the ordinary group operations as the structure maps.
--   - `groupOfMaps`: PDF pp. 2–3: the group computed from the diagrammatic operations.
--   - `GroupObjectInGrp`: PDF pp. 3–4: all three maps must be homomorphisms for the ORIGINAL ambient group multiplication. The internal multiplication is independent data.
--   - `GroupObjectInTop`: PDF p. 3: a group object in Top uses joint continuity of multiplication. The unit map is explicitly included; it is the constant map from a singleton.
--   - `SmoothGroupObject`: PDF p. 3 and footnote 3: a group object on a fixed real smooth manifold. The identity point defines an automatically smooth map from the point manifold.
--   - `ActionDiagrams`: PDF pp. 4–5: the two diagrams for a left action; inversion is unused.
--   - `actionOfMap`: PDF pp. 4–5: the ordinary action computed from the actual action map.
--   - `tensorRing`: PDF p. 5 and footnote 5: the canonical ℤ-module presentation of Ab, with its TENSOR monoidal structure. This is Mathlib's actual ring construction. We use the category of small ℤ-modules: Mathlib's tensor monoidal instance requires the module universe to equal the scalar universe, here Type 0.
--   - `TensorActionDiagrams`: PDF p. 5: unit and associativity of a tensor action, evaluated on pure tensors. Linearity of the map on the tensor product gives BOTH distributivities.
--   - `CategoryMaps`: PDF pp. 6–8: source, target, identity and composition, in total-arrow coordinates. compose g f denotes g after f and is used only if target f = source g. Outside that domain its value has no mathematical significance.
--   - `CategoryDiagrams`: PDF pp. 6–8: every category diagram, including endpoint compatibility. Associativity is quantified over composable triples, with no identification of nested pullback TYPES.
--   - `categoryOfMaps`: PDF pp. 6–8: the ordinary category constructed from an internal Set category. Its hom types are the source-target fibres of the ORIGINAL arrow set.
--   - `TotalArrow`: PDF pp. 6–8: the set of all arrows of a small category.
--   - `mapsOfCategory`: PDF pp. 6–8: the reverse construction uses the original category's arrows. A canonical filler is supplied for noncomposable pairs; it is never compared.
--   - `totalArrowEquiv`: The reconstruction keeps the original total arrow, not merely its endpoints.
--   - `totalHomEquiv`: The hom of an ordinary category is recovered as the matching total-arrow fibre.
--   - `emptyCategoryMaps`: The empty category and all its diagrams are retained.
--   - `InternalCategoryInGrp`: PDF p. 8: structure maps are homomorphisms; composition is a homomorphism on the composable-pair subgroup, including its identity element.
--   - `FunctorDiagrams`: PDF p. 8: functors in total-arrow coordinates preserve endpoints, identities and composition. No action on off-domain composites is required.
--   - `productCategoryMaps`: PDF p. 8: the cartesian product category.
--   - `pointCategoryMaps`: PDF p. 8: the one-object discrete terminal category called 0 in the paper.
--   - `GroupObjectInCat`: PDF p. 8: a STRICT group object in Cat, with pointwise group operations on objects and arrows. Their associativity, units, and both inverse laws come from the given Group structures; multiplication, unit and inversion must all be functors. Group inversion is not an assumed categorical inverse of arrows.
--   - `splitAction`: PDF p. 9: the conjugation action belonging to the specified splitting.
--   - `splitCoordinates`: PDF p. 9: the computed split coordinates, including the kernel witness.
--   - `splitAssembly`: PDF p. 9: the inverse map sends (k,x) to k e(x).
--   - `CrossedModule`: PDF p. 9: exactly the two crossed-module axioms, with an action by GROUP AUTOMORPHISMS, as clarified on p. 10.
--   - `crossedCategoryMaps`: PDF pp. 9–10: the actual crossed-module category on the semidirect product. The formula for composition is used ONLY on composable pairs.
--   - `sourceHom`: PDF p. 8: bundle the source homomorphism already in the internal data.
--   - `targetHom`: PDF p. 8: bundle the target homomorphism already in the internal data.
--   - `identityHom`: PDF p. 8: bundle the identity homomorphism already in the internal data.
--   - `kernelBoundary`: PDF p. 11: restrict the ACTUAL target to the ACTUAL source kernel.
--   - `kernelAction`: PDF p. 11: x acts on the kernel by identity(x) k identity(x) inverse.
--   - `categoryCoordinates`: PDF pp. 9,11: the canonical coordinate map for the original category.
--   - `crossedKernelMap`: PDF pp. 10–11: the canonical inclusion into the source kernel of the reconstructed category. It does not depend on a choice of an equivalence.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, https://arxiv.org/abs/math/0212065v1

import Mathlib

/-!
Statements from Forrester-Barker, *Group Objects and Internal Categories*,
arXiv:math/0212065v1. Page numbers are PDF page numbers.

All new interfaces are local to this paper. Cartesian diagrams in concrete
categories are written elementwise. The tensor product below is over ℤ.
Category composition is stored as a total function, as in the accepted
Renew46.P18 interface, but is used and compared only on composable pairs.
Its values on other pairs are immaterial and are never part of reconstruction.
No categorical inverse for arrows is assumed.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory
open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF pp. 1–3: the three maps of an unbundled group object in Set. -/
structure GroupMaps (G : Type u) where
  mul : G → G → G
  unit : G
  inverse : G → G

/-- PDF pp. 1–3: associativity, both units, and both inverse diagrams. -/
structure GroupDiagrams {G : Type u} (D : GroupMaps G) : Prop where
  assoc : ∀ a b c, D.mul (D.mul a b) c = D.mul a (D.mul b c)
  unit_left : ∀ a, D.mul D.unit a = a
  unit_right : ∀ a, D.mul a D.unit = a
  inverse_left : ∀ a, D.mul (D.inverse a) a = D.unit
  inverse_right : ∀ a, D.mul a (D.inverse a) = D.unit

/-- PDF p. 3: read the ordinary group operations as the structure maps. -/
def mapsOfGroup (G : Type u) [Group G] : GroupMaps G :=
  ⟨(· * ·), 1, Inv.inv⟩

/-- PDF pp. 2–3: the group computed from the diagrammatic operations. -/
def groupOfMaps {G : Type u} (D : GroupMaps G) (h : GroupDiagrams D) : Group G where
  mul := D.mul
  one := D.unit
  inv := D.inverse
  mul_assoc := h.assoc
  one_mul := h.unit_left
  mul_one := h.unit_right
  inv_mul_cancel := h.inverse_left

/-- The conversion preserves the actual multiplication, unit, and inverse. -/
example {G : Type u} (D : GroupMaps G) (h : GroupDiagrams D) (a b : G) :
    (groupOfMaps D h).mul a b = D.mul a b ∧
    (groupOfMaps D h).one = D.unit ∧
    (groupOfMaps D h).inv a = D.inverse a := ⟨rfl, rfl, rfl⟩

/-- PDF pp. 3–4: all three maps must be homomorphisms for the ORIGINAL
ambient group multiplication. The internal multiplication is independent data. -/
def GroupObjectInGrp {G : Type u} [Group G] (D : GroupMaps G) : Prop :=
  GroupDiagrams D ∧ D.unit = 1 ∧ D.mul 1 1 = 1 ∧
  (∀ a b c d, D.mul (a * c) (b * d) = D.mul a b * D.mul c d) ∧
  D.inverse 1 = 1 ∧ (∀ a b, D.inverse (a * b) = D.inverse a * D.inverse b)

/-- Sanity: all group-object diagrams and homomorphism laws hold on the
one-element group; the forward hypotheses are not globally vacuous. -/
example : GroupObjectInGrp (mapsOfGroup PUnit) := by
  refine ⟨?_, rfl, rfl, ?_, rfl, ?_⟩
  · constructor <;> intros <;> exact Subsingleton.elim _ _
  · intros; exact Subsingleton.elim _ _
  · intros; exact Subsingleton.elim _ _

/-- PDF p. 3: a group object in Top uses joint continuity of multiplication.
The unit map is explicitly included; it is the constant map from a singleton. -/
def GroupObjectInTop {G : Type u} [TopologicalSpace G] (D : GroupMaps G) : Prop :=
  GroupDiagrams D ∧ Continuous (fun p : G × G => D.mul p.1 p.2) ∧
  Continuous (fun _ : PUnit.{1} => D.unit) ∧ Continuous D.inverse

/-- PDF p. 3 and footnote 3: a group object on a fixed real smooth manifold.
The identity point defines an automatically smooth map from the point manifold. -/
def SmoothGroupObject {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type u} [TopologicalSpace G] [ChartedSpace E G] (D : GroupMaps G) : Prop :=
  GroupDiagrams D ∧
  ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
    (fun p : G × G => D.mul p.1 p.2) ∧
  ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ D.inverse

/-- PDF pp. 4–5: the two diagrams for a left action; inversion is unused. -/
def ActionDiagrams {M : Type u} [Monoid M] {X : Type v} (n : M × X → X) : Prop :=
  (∀ x, n (1, x) = x) ∧ (∀ a b x, n (a * b, x) = n (a, n (b, x)))

/-- PDF pp. 4–5: the ordinary action computed from the actual action map. -/
def actionOfMap {M : Type u} [Monoid M] {X : Type v}
    (n : M × X → X) (h : ActionDiagrams n) : MulAction M X where
  smul a x := n (a, x)
  one_smul := h.1
  mul_smul := h.2

/-- Empty acted-on sets require no exceptional convention. -/
example {M : Type u} [Monoid M] {X : Type v} (n : M × X → X)
    (h : ActionDiagrams n) (a : M) (x : X) :
    @SMul.smul M X (actionOfMap n h).toSMul a x = n (a, x) := rfl

/-- PDF p. 5 and footnote 5: the canonical ℤ-module presentation of Ab,
with its TENSOR monoidal structure. This is Mathlib's actual ring construction.
We use the category of small ℤ-modules: Mathlib's tensor monoidal instance
requires the module universe to equal the scalar universe, here Type 0. -/
noncomputable def tensorRing (M : ModuleCat.{0} ℤ) [MonObj M] : Ring M :=
  ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing M

/-- PDF p. 5: unit and associativity of a tensor action, evaluated on pure
 tensors. Linearity of the map on the tensor product gives BOTH distributivities. -/
def TensorActionDiagrams (M : ModuleCat.{0} ℤ) [MonObj M]
    (A : Type v) [AddCommGroup A]
    (n : TensorProduct ℤ M A →ₗ[ℤ] A) : Prop :=
  (∀ a, n ((MonObj.one (X := M) (1 : ℤ)) ⊗ₜ[ℤ] a) = a) ∧
  (∀ x y : M, ∀ a : A,
    n ((MonObj.mul (X := M) (x ⊗ₜ[ℤ] y)) ⊗ₜ[ℤ] a) =
      n (x ⊗ₜ[ℤ] n (y ⊗ₜ[ℤ] a)))

/-- Sanity: the zero abelian group is a tensor module, including when the
acting tensor ring is itself zero. -/
example (M : ModuleCat.{0} ℤ) [MonObj M] :
    TensorActionDiagrams M PUnit (0 : TensorProduct ℤ M PUnit →ₗ[ℤ] PUnit) := by
  constructor <;> intros <;> exact Subsingleton.elim _ _

/-- PDF pp. 6–8: source, target, identity and composition, in total-arrow
coordinates. compose g f denotes g after f and is used only if target f = source g.
Outside that domain its value has no mathematical significance. -/
structure CategoryMaps (A : Type u) (O : Type v) where
  source : A → O
  target : A → O
  identity : O → A
  compose : A → A → A

/-- PDF pp. 6–8: every category diagram, including endpoint compatibility.
Associativity is quantified over composable triples, with no identification of
nested pullback TYPES. -/
structure CategoryDiagrams {A : Type u} {O : Type v} (D : CategoryMaps A O) : Prop where
  source_identity : ∀ x, D.source (D.identity x) = x
  target_identity : ∀ x, D.target (D.identity x) = x
  source_compose : ∀ f g, D.target f = D.source g →
    D.source (D.compose g f) = D.source f
  target_compose : ∀ f g, D.target f = D.source g →
    D.target (D.compose g f) = D.target g
  identity_compose : ∀ f, D.compose (D.identity (D.target f)) f = f
  compose_identity : ∀ f, D.compose f (D.identity (D.source f)) = f
  assoc : ∀ f g h, D.target f = D.source g → D.target g = D.source h →
    D.compose h (D.compose g f) = D.compose (D.compose h g) f

/-- PDF pp. 6–8: the ordinary category constructed from an internal Set category.
Its hom types are the source-target fibres of the ORIGINAL arrow set. -/
def categoryOfMaps {A : Type u} {O : Type v} (D : CategoryMaps A O)
    (h : CategoryDiagrams D) : Category.{u} O where
  Hom x y := {f : A // D.source f = x ∧ D.target f = y}
  id x := ⟨D.identity x, h.source_identity x, h.target_identity x⟩
  comp f g := ⟨D.compose g.val f.val,
    (h.source_compose f.val g.val (f.property.2.trans g.property.1.symm)).trans f.property.1,
    (h.target_compose f.val g.val (f.property.2.trans g.property.1.symm)).trans g.property.2⟩
  id_comp := by
    intro x y f
    apply Subtype.ext
    change D.compose f.val (D.identity x) = f.val
    exact (congrArg (fun o => D.compose f.val (D.identity o)) f.property.1).symm.trans
      (h.compose_identity f.val)
  comp_id := by
    intro x y f
    apply Subtype.ext
    change D.compose (D.identity y) f.val = f.val
    exact (congrArg (fun o => D.compose (D.identity o) f.val) f.property.2).symm.trans
      (h.identity_compose f.val)
  assoc := by
    intro x y z q f g k
    apply Subtype.ext
    exact h.assoc f.val g.val k.val
      (f.property.2.trans g.property.1.symm) (g.property.2.trans k.property.1.symm)

/-- PDF pp. 6–8: the set of all arrows of a small category. -/
def TotalArrow (O : Type v) [Category.{u} O] := Σ x : O, Σ y : O, (x ⟶ y)

/-- PDF pp. 6–8: the reverse construction uses the original category's arrows.
A canonical filler is supplied for noncomposable pairs; it is never compared. -/
noncomputable def mapsOfCategory (O : Type v) [Category.{u} O] :
    CategoryMaps (TotalArrow O) O := by
  classical
  exact
    { source := fun f => f.1
      target := fun f => f.2.1
      identity := fun x => ⟨x, x, 𝟙 x⟩
      compose := fun g f => if h : f.2.1 = g.1 then
        ⟨f.1, g.2.1, f.2.2 ≫ eqToHom h ≫ g.2.2⟩ else f }

/-- The reconstruction keeps the original total arrow, not merely its endpoints. -/
def totalArrowEquiv {A : Type u} {O : Type v} (D : CategoryMaps A O)
    (h : CategoryDiagrams D) :
    letI := categoryOfMaps D h
    A ≃ TotalArrow O := by
  letI := categoryOfMaps D h
  exact
    { toFun := fun a => ⟨D.source a, D.target a, ⟨a, rfl, rfl⟩⟩
      invFun := fun f => f.2.2.val
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨x, y, ⟨f, hs, ht⟩⟩
        cases hs
        cases ht
        rfl }

/-- The hom of an ordinary category is recovered as the matching total-arrow fibre. -/
noncomputable def totalHomEquiv (O : Type v) [Category.{u} O] (x y : O) :
    (x ⟶ y) ≃ {a : TotalArrow O // a.1 = x ∧ a.2.1 = y} where
  toFun f := ⟨⟨x, y, f⟩, rfl, rfl⟩
  invFun a := eqToHom a.property.1.symm ≫ a.val.2.2 ≫ eqToHom a.property.2
  left_inv := by intro f; simp
  right_inv := by
    rintro ⟨⟨a, b, f⟩, ha, hb⟩
    cases ha
    cases hb
    simp

/-- The empty category and all its diagrams are retained. -/
def emptyCategoryMaps : CategoryMaps Empty Empty where
  source := id
  target := id
  identity := id
  compose _ f := f

/-- Sanity: no nonemptiness hypothesis entered the category interface. -/
example : CategoryDiagrams emptyCategoryMaps where
  source_identity := by intro x; cases x
  target_identity := by intro x; cases x
  source_compose := by intro f; cases f
  target_compose := by intro f; cases f
  identity_compose := by intro f; cases f
  compose_identity := by intro f; cases f
  assoc := by intro f; cases f

/-- PDF p. 8: structure maps are homomorphisms; composition is a homomorphism
on the composable-pair subgroup, including its identity element. -/
structure InternalCategoryInGrp {A : Type u} {O : Type v}
    [Group A] [Group O] (D : CategoryMaps A O) : Prop where
  category : CategoryDiagrams D
  source_one : D.source 1 = 1
  source_mul : ∀ a b, D.source (a * b) = D.source a * D.source b
  target_one : D.target 1 = 1
  target_mul : ∀ a b, D.target (a * b) = D.target a * D.target b
  identity_one : D.identity 1 = 1
  identity_mul : ∀ x y, D.identity (x * y) = D.identity x * D.identity y
  compose_one : D.compose 1 1 = 1
  interchange : ∀ f g a b, D.target f = D.source g → D.target a = D.source b →
    D.compose (g * b) (f * a) = D.compose g f * D.compose b a

/-- PDF p. 8: functors in total-arrow coordinates preserve endpoints, identities
and composition. No action on off-domain composites is required. -/
def FunctorDiagrams {A : Type u} {O : Type v} {B : Type w} {P : Type z}
    (D : CategoryMaps A O) (E : CategoryMaps B P) (fo : O → P) (fa : A → B) : Prop :=
  (∀ a, E.source (fa a) = fo (D.source a) ∧ E.target (fa a) = fo (D.target a)) ∧
  (∀ x, fa (D.identity x) = E.identity (fo x)) ∧
  (∀ f g, D.target f = D.source g → fa (D.compose g f) = E.compose (fa g) (fa f))

/-- PDF p. 8: the cartesian product category. -/
def productCategoryMaps {A : Type u} {O : Type v} {B : Type w} {P : Type z}
    (D : CategoryMaps A O) (E : CategoryMaps B P) : CategoryMaps (A × B) (O × P) where
  source a := (D.source a.1, E.source a.2)
  target a := (D.target a.1, E.target a.2)
  identity x := (D.identity x.1, E.identity x.2)
  compose b a := (D.compose b.1 a.1, E.compose b.2 a.2)

/-- PDF p. 8: the one-object discrete terminal category called 0 in the paper. -/
def pointCategoryMaps : CategoryMaps PUnit.{1} PUnit.{1} :=
  ⟨fun _ => PUnit.unit, fun _ => PUnit.unit, fun _ => PUnit.unit,
    fun _ _ => PUnit.unit⟩

/-- Sanity: the point is a category, distinct from the empty category. -/
example : CategoryDiagrams pointCategoryMaps where
  source_identity := by intro x; exact Subsingleton.elim _ _
  target_identity := by intro x; exact Subsingleton.elim _ _
  source_compose := by intros; exact Subsingleton.elim _ _
  target_compose := by intros; exact Subsingleton.elim _ _
  identity_compose := by intros; exact Subsingleton.elim _ _
  compose_identity := by intros; exact Subsingleton.elim _ _
  assoc := by intros; exact Subsingleton.elim _ _

/-- Sanity: the singleton internal category satisfies every Grp diagram,
including the identity and multiplication laws on composable pairs. -/
example : InternalCategoryInGrp pointCategoryMaps := by
  constructor
  · constructor <;> intros <;> exact Subsingleton.elim _ _
  all_goals
    intros
    exact Subsingleton.elim _ _

/-- PDF p. 8: a STRICT group object in Cat, with pointwise group operations
on objects and arrows. Their associativity, units, and both inverse laws come
from the given Group structures; multiplication, unit and inversion must all be
functors. Group inversion is not an assumed categorical inverse of arrows. -/
def GroupObjectInCat {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) : Prop :=
  CategoryDiagrams D ∧
  FunctorDiagrams (productCategoryMaps D D) D (fun x => x.1 * x.2) (fun a => a.1 * a.2) ∧
  FunctorDiagrams pointCategoryMaps D (fun _ => 1) (fun _ => 1) ∧
  FunctorDiagrams D D Inv.inv Inv.inv

/-- PDF p. 9: the conjugation action belonging to the specified splitting. -/
def splitAction {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) : O →* MulAut s.ker :=
  (MulAut.conjNormal : A →* MulAut s.ker).comp e

/-- PDF p. 9: the computed split coordinates, including the kernel witness. -/
def splitCoordinates {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) (h : ∀ x, s (e x) = x) (a : A) :
    SemidirectProduct s.ker O (splitAction s e) :=
  ⟨⟨a * (e (s a))⁻¹, by
      change s (a * (e (s a))⁻¹) = 1
      simp only [map_mul, map_inv, h, mul_inv_cancel]⟩, s a⟩

/-- PDF p. 9: the inverse map sends (k,x) to k e(x). -/
def splitAssembly {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A)
    (a : SemidirectProduct s.ker O (splitAction s e)) : A := a.left.val * e a.right

/-- Sanity: the coordinate formulas preserve the multiplication order. -/
example {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) (h : ∀ x, s (e x) = x) (a : A) :
    (splitCoordinates s e h a).left.val = a * (e (s a))⁻¹ ∧
    splitAssembly s e (splitCoordinates s e h a) =
      (a * (e (s a))⁻¹) * e (s a) := ⟨rfl, rfl⟩

/-- PDF p. 9: exactly the two crossed-module axioms, with an action by
GROUP AUTOMORPHISMS, as clarified on p. 10. -/
def CrossedModule {C : Type u} {G : Type v} [Group C] [Group G]
    (boundary : C →* G) (action : G →* MulAut C) : Prop :=
  (∀ g c, boundary (action g c) = g * boundary c * g⁻¹) ∧
  (∀ c d, action (boundary c) d = c * d * c⁻¹)

/-- Sanity: the one-element groups form a crossed module. -/
example : CrossedModule (MonoidHom.id PUnit) (1 : PUnit →* MulAut PUnit) := by
  constructor <;> intro a b <;> exact Subsingleton.elim _ _

/-- PDF pp. 9–10: the actual crossed-module category on the semidirect product.
The formula for composition is used ONLY on composable pairs. -/
def crossedCategoryMaps {C : Type u} {G : Type v} [Group C] [Group G]
    (boundary : C →* G) (action : G →* MulAut C) :
    CategoryMaps (SemidirectProduct C G action) G where
  source a := a.right
  target a := boundary a.left * a.right
  identity x := ⟨1, x⟩
  compose b a := ⟨b.left * a.left, a.right⟩

/-- Sanity: vertical composition is b.left * a.left, not the semidirect product. -/
example {C : Type u} {G : Type v} [Group C] [Group G]
    (d : C →* G) (r : G →* MulAut C) (a b : SemidirectProduct C G r) :
    (crossedCategoryMaps d r).source a = a.right ∧
    ((crossedCategoryMaps d r).compose b a).left = b.left * a.left := ⟨rfl, rfl⟩

/-- PDF p. 8: bundle the source homomorphism already in the internal data. -/
def sourceHom {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) : A →* O where
  toFun := D.source
  map_one' := h.source_one
  map_mul' := h.source_mul

/-- PDF p. 8: bundle the target homomorphism already in the internal data. -/
def targetHom {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) : A →* O where
  toFun := D.target
  map_one' := h.target_one
  map_mul' := h.target_mul

/-- PDF p. 8: bundle the identity homomorphism already in the internal data. -/
def identityHom {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) : O →* A where
  toFun := D.identity
  map_one' := h.identity_one
  map_mul' := h.identity_mul

/-- PDF p. 11: restrict the ACTUAL target to the ACTUAL source kernel. -/
def kernelBoundary {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) : (sourceHom D h).ker →* O :=
  (targetHom D h).comp (sourceHom D h).ker.subtype

/-- PDF p. 11: x acts on the kernel by identity(x) k identity(x) inverse. -/
def kernelAction {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) : O →* MulAut (sourceHom D h).ker :=
  splitAction (sourceHom D h) (identityHom D h)

/-- PDF pp. 9,11: the canonical coordinate map for the original category. -/
def categoryCoordinates {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) :
    A → SemidirectProduct (sourceHom D h).ker O (kernelAction D h) :=
  splitCoordinates (sourceHom D h) (identityHom D h) h.category.source_identity

/-- PDF pp. 10–11: the canonical inclusion into the source kernel of the
reconstructed category. It does not depend on a choice of an equivalence. -/
def crossedKernelMap {C : Type u} {G : Type v} [Group C] [Group G]
    (action : G →* MulAut C) (c : C) :
    (SemidirectProduct.rightHom : SemidirectProduct C G action →* G).ker :=
  ⟨⟨c, 1⟩, rfl⟩

/-- Sanity: extracting the boundary and action retains the ORIGINAL target
and identity-conjugation maps, with no arbitrary replacement homomorphisms. -/
example {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D)
    (k : (sourceHom D h).ker) (x : O) (a : A) :
    kernelBoundary D h k = D.target k.val ∧
    ((kernelAction D h x) k).val = D.identity x * k.val * (D.identity x)⁻¹ ∧
    (categoryCoordinates D h a).right = D.source a := ⟨rfl, rfl, rfl⟩

end QAlgorithms.Papers.Independent.Intake100.P20


