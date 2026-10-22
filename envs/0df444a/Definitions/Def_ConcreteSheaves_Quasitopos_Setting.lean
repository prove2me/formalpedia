-- Prove2me | Definitions.Def_ConcreteSheaves_Quasitopos_Setting
-- name    : ConcreteSheaves_Quasitopos_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:45.823843+00:00
-- url     : https://prove2.me/theorems/3fa5b4d2-ab89-4cf4-a721-8e90529bd4c8
-- title:
--   Concrete sites, concrete sheaves, and quasitopos structure
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a chosen terminal object $T$. A covering family is represented by its presieve of arrows into an object. The site is **concrete** when representable presheaves satisfy the sheaf condition, maps between domains are distinguished by their action on maps out of $T$, and every point of a covered domain lifts through a covering arrow.
--
--   For a presheaf $P:D^{\mathrm{op}}\to\mathrm{Set}$, a plot over $X$ determines a function $\operatorname{Hom}(T,X)\to P(T)$ by restriction along points. The presheaf is **concrete** when this function determines the plot uniquely. A **$D$ space** is a presheaf that is both concrete and a sheaf for $K$; its maps are natural transformations. Its underlying set is $P(T)$.
--
--   The definition file also records the presheaf $\Omega(X)=\{0,1\}^{\operatorname{Hom}(T,X)}$, the subspace condition on a map of $D$ spaces, and concretization, which identifies plots with the same underlying function. A **weak subobject classifier** classifies strong monomorphisms by a unique characteristic map and a pullback square. **Local cartesian closure** requires every slice category to have finite products and product with every slice object to admit a right adjoint. A **quasitopos** has this closure, finite colimits, and a weak subobject classifier.
--
--   These definitions provide the common meaning of the goal and its thirteen milestones.
--
--   **Formalization Note** The category and its homs live in universe $u$, and presheaves take values in $\mathrm{Type}_u$. Covering families are presieves; the sheaf condition is the coverage form of `Presieve.IsSheafFor`. A terminal object is passed as explicit data. The classifier's terminal object is included in the predicate so Proposition 40 can state its existence without assuming a result of Proposition 39. The quasitopos predicate takes finite limits as an instance, as Definition 38 presupposes. The product functor in each slice is $X\times-$, equivalent by symmetry to the paper's $-\times X$. Truth values are `Bool`. Concretization is the image of the plot-to-underlying-function map, canonically the quotient described in Definition 46.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, pp. 17–20, 24, 26, 30, 32–33, 38, Definitions 8, 11, 15, 18–20, 33, 38, 42–43, 46 and Proposition 30

import Mathlib

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {D : Type u} [SmallCategory D]

/-- Definition 15, with covering families represented as presieves. -/
def IsSheafCov (K : Coverage D) (P : Dᵒᵖ ⥤ Type u) : Prop :=
  ∀ ⦃X : D⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R

/-- Definitions 19 and 46: a plot is determined by its function on points. -/
def IsConcrete (T : D) (P : Dᵒᵖ ⥤ Type u) : Prop :=
  ∀ X : D, Function.Injective
    (fun φ : P.obj (op X) => fun d : T ⟶ X => P.map d.op φ)

/-- Definition 18: subcanonicity, enough points, and pointwise covering. -/
structure IsConcreteSite (K : Coverage D) (T : D) (hT : IsTerminal T) : Prop where
  subcanonical : ∀ X : D, IsSheafCov K (yoneda.obj X)
  faithful : ∀ ⦃X Y : D⦄ (f g : X ⟶ Y),
    (∀ x : T ⟶ X, x ≫ f = x ≫ g) → f = g
  jointlySurj : ∀ ⦃X : D⦄ (R : Presieve X), R ∈ K X →
    ∀ x : T ⟶ X, ∃ (Y : D) (f : Y ⟶ X), R f ∧ ∃ y : T ⟶ Y, y ≫ f = x

/-- Definition 20. -/
def IsDSpace (K : Coverage D) (T : D) : ObjectProperty (Dᵒᵖ ⥤ Type u) :=
  fun P => IsSheafCov K P ∧ IsConcrete T P

/-- D spaces and natural transformations between them. -/
abbrev DSpace (K : Coverage D) (T : D) : Type (u+1) :=
  (IsDSpace K T).FullSubcategory

/-- The underlying set of a D space is its value at the site's terminal object. -/
def underlying (K : Coverage D) (T : D) : DSpace K T ⥤ Type u :=
  (IsDSpace K T).ι ⋙ (evaluation _ _).obj (op T)

/-- Proposition 30's presheaf of truth-valued functions on the points of a domain. -/
def omegaPresheaf (T : D) : Dᵒᵖ ⥤ Type u where
  obj X := (T ⟶ X.unop) → Bool
  map := fun {_ _} f => ↾(fun φ d => φ (d ≫ f.unop))
  map_id := by
    intro X
    ext φ d
    simp
  map_comp := by
    intro X Y Z f g
    ext φ d
    simp

/-- Definition 33: plots whose point functions land in `A` lift uniquely to `A`. -/
def IsSubspace {K : Coverage D} {T : D} {A X : DSpace K T}
    (i : A ⟶ X) : Prop :=
  ∀ ⦃E : D⦄ (φ : X.obj.obj (op E)),
    (∀ d : T ⟶ E, X.obj.map d.op φ ∈ Set.range (i.hom.app (op T))) →
      ∃! ψ : A.obj.obj (op E), i.hom.app (op E) ψ = φ

/-- Definition 46: plots modulo equality of their underlying point functions. -/
def concretization (T : D) (P : Dᵒᵖ ⥤ Type u) : Dᵒᵖ ⥤ Type u where
  obj X := Set.range (fun φ : P.obj (op X.unop) =>
    fun d : T ⟶ X.unop => P.map d.op φ)
  map := fun {_ _} f => ↾(fun h => ⟨fun d => h.1 (d ≫ f.unop), by
    obtain ⟨φ, hφ⟩ := h.2
    refine ⟨P.map f φ, ?_⟩
    funext d
    calc
      P.map d.op (P.map f φ) = P.map (d ≫ f.unop).op φ := by simp
      _ = h.1 (d ≫ f.unop) := congrFun hφ _⟩)
  map_id := by
    intro X
    ext h
    simp
  map_comp := by
    intro X Y Z f g
    ext h
    simp

/-- The quotient map sending each plot to its underlying function. -/
def concretizationπ (T : D) (P : Dᵒᵖ ⥤ Type u) : P ⟶ concretization T P where
  app := fun X => ↾(fun φ => ⟨fun d => P.map d.op φ, ⟨φ, rfl⟩⟩)
  naturality := by
    intro X Y f
    ext φ
    simp [concretization]

/-- Definition 38: classification of strong monomorphisms by pullback. -/
def HasWeakSubobjectClassifier (C : Type v) [Category.{w} C] : Prop :=
  ∃ (T Ω : C) (hT : IsTerminal T) (t : T ⟶ Ω),
    ∀ ⦃A X : C⦄ (i : A ⟶ X), StrongMono i →
      ∃! χ : X ⟶ Ω, IsPullback i (hT.from A) χ t

/-- Definitions 42–43: every slice has exponentials. -/
def IsLocallyCartesianClosed (C : Type v) [Category.{w} C] : Prop :=
  ∀ B : C, ∃ hprod : HasBinaryProducts (Over B),
    letI : HasBinaryProducts (Over B) := hprod
    ∀ X : Over B, (prod.functor.obj X).IsLeftAdjoint

/-- Definition 8, with the finite limits assumed in Definition 38. -/
def IsQuasitopos (C : Type v) [Category.{w} C] [HasFiniteLimits C] : Prop :=
  IsLocallyCartesianClosed C ∧ HasFiniteColimits C ∧ HasWeakSubobjectClassifier C

end ConcreteSheaves.Quasitopos


