-- Prove2me | Definitions.Def_PretorsionImageClosed_Statement
-- name    : PretorsionImageClosed_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:07.583009+00:00
-- url     : https://prove2.me/theorems/7afd4c53-0d10-4082-99ad-21e8c2db6508
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Statement.lean

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.SetTheory.Cardinal.Finite
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits
universe u
section General
variable {C : Type*} [Category C]
def IsTrivial (Z : ObjectProperty C) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (W : C) (_ : Z W) (g : X ⟶ W) (h : W ⟶ Y), g ≫ h = f
def IsPrekernel (Z : ObjectProperty C) {T X F : C} (u : T ⟶ X) (v : X ⟶ F) : Prop :=
  IsTrivial Z (u ≫ v) ∧
    ∀ {Y : C} (u' : Y ⟶ X), IsTrivial Z (u' ≫ v) → ∃! h : Y ⟶ T, h ≫ u = u'
def IsPrecokernel (Z : ObjectProperty C) {T X F : C} (u : T ⟶ X) (v : X ⟶ F) : Prop :=
  IsTrivial Z (u ≫ v) ∧
    ∀ {Y : C} (v' : X ⟶ Y), IsTrivial Z (u ≫ v') → ∃! h : F ⟶ Y, v ≫ h = v'
def IsShortPreexact (Z : ObjectProperty C) {T X F : C} (u : T ⟶ X) (v : X ⟶ F) : Prop :=
  IsPrekernel Z u v ∧ IsPrecokernel Z u v
def IsPretorsionTheory (T F : ObjectProperty C) : Prop :=
  (∀ {X Y : C} (f : X ⟶ Y), T X → F Y → IsTrivial (T ⊓ F) f) ∧
    ∀ X : C, ∃ (T' F' : C) (u : T' ⟶ X) (v : X ⟶ F'),
      T T' ∧ F F' ∧ IsShortPreexact (T ⊓ F) u v
variable [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable (C) in
/-- A subcategory in the sense of the manuscript's conventions: a property of
objects closed under isomorphisms and direct summands (retracts) and under
finite direct sums (binary direct sums and the zero objects). Full
subcategories are given by their objects. -/
structure Subcategory where
  /-- The objects of the subcategory. -/
  prop : ObjectProperty C
  /-- Closed under direct summands, hence under isomorphisms. -/
  prop_of_retract : ∀ {X Y : C}, Retract X Y → prop Y → prop X
  /-- Closed under finite direct sums: under binary direct sums ... -/
  prop_biprod : ∀ {X Y : C}, prop X → prop Y → prop (X ⊞ Y)
  /-- ... and containing the zero objects (the empty direct sum). -/
  prop_of_isZero : ∀ {X : C}, IsZero X → prop X
variable (C) in
/-- The pretorsion theories of `C` whose components are subcategories; the set
`PT(Λ)` of the manuscript. -/
structure PretorsionTheory where
  /-- The first component. -/
  T : Subcategory C
  /-- The second component. -/
  F : Subcategory C
  isPretorsionTheory : IsPretorsionTheory T.prop F.prop
def PretorsionTheory.LE (P Q : PretorsionTheory C) : Prop :=
  P.T.prop ≤ Q.T.prop ∧ Q.F.prop ≤ P.F.prop
def PretorsionTheory.middle (P : PretorsionTheory C) : ObjectProperty C :=
  P.T.prop ⊓ P.F.prop
def Gen (Z : Subcategory C) : ObjectProperty C := fun X =>
  ∃ (Y : C) (_ : Z.prop Y) (p : Y ⟶ X), Epi p
def Cogen (Z : Subcategory C) : ObjectProperty C := fun X =>
  ∃ (Y : C) (_ : Z.prop Y) (i : X ⟶ Y), Mono i
def IsImageClosed [HasImages C] (Z : ObjectProperty C) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), Z X → Z Y → Z (image f)
def indCard (Z : ObjectProperty C) : ℕ :=
  Nat.card (Skeleton (ObjectProperty.FullSubcategory (fun X : C => Z X ∧ Indecomposable X)))
end General
section Modules
theorem isNoetherianRing_mop (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] : IsNoetherianRing Λᵐᵒᵖ :=
  IsNoetherianRing.of_finite k Λᵐᵒᵖ
abbrev Mod (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] : Type (u + 1) :=
  FGModuleCat.{u} Λᵐᵒᵖ
def TheoremA : Prop :=
  ∀ (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ],
    haveI := isNoetherianRing_mop k Λ
    ∀ Z : Subcategory (Mod k Λ),
      (IsImageClosed Z.prop ↔ Z.prop = Gen Z ⊓ Cogen Z) ∧
      (IsImageClosed Z.prop ↔ ∃ P : PretorsionTheory (Mod k Λ), P.middle = Z.prop)
def CompleteLattice : Prop :=
  ∀ (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ],
    haveI := isNoetherianRing_mop k Λ
    ∃ _ : _root_.CompleteLattice (PretorsionTheory (Mod k Λ)),
      (∀ P Q : PretorsionTheory (Mod k Λ), P ≤ Q ↔ P.LE Q) ∧
      (∀ S : Set (PretorsionTheory (Mod k Λ)), S.Nonempty →
        (sInf S).T.prop = ⨅ P ∈ S, P.T.prop ∧
        (sInf S).F.prop = ⨅ (F : Subcategory (Mod k Λ))
          (_ : IsPretorsionTheory (⨅ P ∈ S, P.T.prop) F.prop ∧ ∀ P ∈ S, P.F.prop ≤ F.prop),
            F.prop) ∧
      (∀ S : Set (PretorsionTheory (Mod k Λ)), S.Nonempty →
        (sSup S).T.prop = ⨅ (T : Subcategory (Mod k Λ))
          (_ : IsPretorsionTheory T.prop (⨅ P ∈ S, P.F.prop) ∧ ∀ P ∈ S, P.T.prop ≤ T.prop),
            T.prop ∧
        (sSup S).F.prop = ⨅ P ∈ S, P.F.prop) ∧
      ((⊥ : PretorsionTheory (Mod k Λ)).T.prop = fun X => IsZero X) ∧
      ((⊥ : PretorsionTheory (Mod k Λ)).F.prop = ⊤) ∧
      ((⊤ : PretorsionTheory (Mod k Λ)).T.prop = ⊤) ∧
      ((⊤ : PretorsionTheory (Mod k Λ)).F.prop = fun X => IsZero X)
end Modules
section TypeA
variable (k : Type u) [Field k]
abbrev LinRep (n : ℕ) : Type (u + 1) := Fin n ⥤ FGModuleCat.{u} k
variable {k}
def rho {n : ℕ} (Z : ObjectProperty (LinRep k n)) : ℕ :=
  Nat.card (Skeleton (ObjectProperty.FullSubcategory (fun X : LinRep k n =>
    Z X ∧ Indecomposable X ∧ ∃ i : Fin n, i.val + 1 = n ∧ ¬ IsZero (X.obj i))))
end TypeA
section Gandhi
open Polynomial
abbrev Rq : Type := ℤ[X]
def q : Rq := X
def IsDelta (f g : Rq[X]) : Prop :=
  g * (1 + C (q - 1) * X) = f.comp (1 + C q * X) - f
def IsGandhiFirst (B : ℕ → Rq[X]) : Prop :=
  B 1 = 1 ∧ ∀ m, 2 ≤ m → IsDelta (X ^ 2 * B (m - 1)) (B m)
def IsGandhiSecond (Cs : ℕ → Rq[X]) : Prop :=
  Cs 1 = 1 ∧ ∀ m, 2 ≤ m → ∃ g, IsDelta (X * Cs (m - 1)) g ∧ Cs m = (1 + C q * X) * g
end Gandhi
section TheoremB
open Polynomial
variable (k : Type u) [Field k] (n : ℕ)
def ImageClosedSubcategory : Type (u + 1) :=
  { Z : Subcategory (LinRep k n) // IsImageClosed Z.prop }
def pretorsionWeight (P : PretorsionTheory (LinRep k n)) : Rq[X] :=
  X ^ rho P.T.prop * C (q ^ indCard P.middle)
def imageClosedWeight (Z : ImageClosedSubcategory k n) : Rq[X] :=
  X ^ rho Z.1.prop * C (q ^ indCard Z.1.prop)
def GandhiPretorsion : Prop :=
  (∃ B, IsGandhiFirst B) ∧
  ∀ (k : Type u) [Field k] (n : ℕ),
    Finite (PretorsionTheory (LinRep k n)) ∧
    ∀ B, IsGandhiFirst B →
      ∑ᶠ P : PretorsionTheory (LinRep k n), pretorsionWeight k n P = B (n + 1)
def GandhiImageClosed : Prop :=
  (∃ Cs, IsGandhiSecond Cs) ∧
  ∀ (k : Type u) [Field k] (n : ℕ),
    Finite (ImageClosedSubcategory k n) ∧
    ∀ Cs, IsGandhiSecond Cs →
      ∑ᶠ Z : ImageClosedSubcategory k n, imageClosedWeight k n Z = Cs (n + 1)
def TheoremBPretorsion : Prop :=
  (∃ B, IsGandhiFirst B) ∧
  ∀ (k : Type u) [Field k] (n : ℕ),
    Finite (PretorsionTheory (LinRep k n)) ∧
    ∀ B, IsGandhiFirst B →
      ∑ᶠ P : PretorsionTheory (LinRep k n), q ^ indCard P.middle = (B (n + 1)).eval 1
def TheoremBImageClosed : Prop :=
  (∃ Cs, IsGandhiSecond Cs) ∧
  ∀ (k : Type u) [Field k] (n : ℕ),
    Finite (ImageClosedSubcategory k n) ∧
    ∀ Cs, IsGandhiSecond Cs →
      ∑ᶠ Z : ImageClosedSubcategory k n, q ^ indCard Z.1.prop = (Cs (n + 1)).eval 1
end TheoremB
end PretorsionImageClosed.Statement


