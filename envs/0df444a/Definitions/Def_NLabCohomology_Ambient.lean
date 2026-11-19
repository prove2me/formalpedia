-- Prove2me | Definitions.Def_NLabCohomology_Ambient
-- name    : NLabCohomology_Ambient
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T20:44:48.93833+00:00
-- url     : https://prove2.me/theorems/ebb52f50-8380-47f8-a456-b6cc1ebb4a67
-- title:
--   The ambient (∞,1)-category, terminal and pointed objects
-- statement:
--   This definition file fixes the ambient environment for the nLab general definition of cohomology: an **(∞,1)-category** $\mathbf{H}$, presented as a simplicial category whose hom simplicial sets are Kan complexes — a fibrant simplicial category, one of the standard models of (∞,1)-categories.
--
--   The structure `InfinityOneCategory` bundles a type of objects; for each pair $X, A$ of objects a hom simplicial set $\mathbf{H}(X,A)$ required to be a **Kan complex** (the hom ∞-groupoid); an identity $0$-simplex for each object; and a degreewise composition of simplices that is natural in the simplex category and strictly associative and unital. The $0$-simplices of $\mathbf{H}(X,A)$ are the morphisms $X \to A$ of $\mathbf{H}$; the higher simplices encode the higher homotopies between them.
--
--   A simplicial set $K$ is declared **contractible** when it has a $0$-simplex and every map $\partial\Delta[n+1] \to K$ from the boundary of a positive-dimensional standard simplex extends to $\Delta[n+1]$. For Kan complexes this is equivalent to weak contractibility (trivial $\pi_0$ and trivial higher homotopy groups at every basepoint). A **terminal object** of $\mathbf{H}$ is an object $*$ such that every hom ∞-groupoid $\mathbf{H}(X,*)$ is contractible, and a **pointed object** is an object $A$ equipped with a cocycle $* \to A$.
--
--   These are exactly the ambient notions used by the "General definition" subsection of the nLab entry: the hom ∞-groupoid $\mathbf{H}(X,A)$, the pointed-object structure $* \to A$ behind the trivial cocycle, and the terminal object $*$.
--
--   **Formalization Note.** The model is single-universe and composition is strict (as in any simplicial category); the Kan condition on hom-complexes is what makes them ∞-groupoids. Contractibility is expressed by boundary extension rather than by homotopy groups, which Mathlib's simplicial-set library does not yet provide in general; the equivalence with weak contractibility for Kan complexes is a standard fact that solvers may formalize as needed.
-- source:
--   nLab, 'cohomology', section 3 (Definition), subsection 'General definition'; https://ncatlab.org/nlab/show/cohomology#Definition (page last revised August 11, 2026). Ambient notions: the (∞,1)-category 𝐇 and its hom ∞-groupoids; the pointed-object structure * → A.

import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# The ambient (∞,1)-category for the nLab general definition of cohomology

This file fixes the ambient environment of the nLab entry "cohomology", section
"Definition / General definition": an (∞,1)-category `𝐇`, presented as a
simplicial category whose hom simplicial sets are Kan complexes (a fibrant
simplicial category, one of the standard models of (∞,1)-categories). It also
defines contractible simplicial sets, terminal objects of `𝐇`, and pointed
objects, as used by the trivial-cocycle clause of the general definition.
-/

universe u

open CategoryTheory Simplicial Opposite

namespace NLabCohomology

/-- A model of an (∞,1)-category `𝐇`: a simplicial category whose hom simplicial
sets are Kan complexes. The `0`-simplices of `hom X A` are the morphisms `X ⟶ A`
of `𝐇`, and its higher simplices encode the higher morphisms of the hom
∞-groupoid `𝐇(X, A)`. -/
structure InfinityOneCategory where
  /-- The objects of `𝐇`. -/
  Obj : Type u
  /-- The hom ∞-groupoid `𝐇(X, A)`, as a simplicial set. -/
  hom : Obj → Obj → SSet.{u}
  /-- Every hom simplicial set is a Kan complex (an ∞-groupoid). -/
  kan : ∀ X Y : Obj, (hom X Y).KanComplex
  /-- The identity morphism of an object, as a `0`-simplex. -/
  id : ∀ X : Obj, hom X X _⦋0⦌
  /-- Composition of simplices, degreewise. -/
  comp : ∀ {X Y Z : Obj} {n : ℕ}, hom X Y _⦋n⦌ → hom Y Z _⦋n⦌ → hom X Z _⦋n⦌
  /-- Composition is simplicial: natural in the simplex category. -/
  comp_map : ∀ {X Y Z : Obj} {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
      (a : hom X Y _⦋n⦌) (b : hom Y Z _⦋n⦌),
      comp ((hom X Y).map f.op a) ((hom Y Z).map f.op b) = (hom X Z).map f.op (comp a b)
  /-- Identities are left units for composition. -/
  id_comp : ∀ {X Y : Obj} {n : ℕ} (b : hom X Y _⦋n⦌),
      comp ((hom X X).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (id X)) b = b
  /-- Identities are right units for composition. -/
  comp_id : ∀ {X Y : Obj} {n : ℕ} (a : hom X Y _⦋n⦌),
      comp a ((hom Y Y).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (id Y)) = a
  /-- Composition is associative. -/
  assoc : ∀ {W X Y Z : Obj} {n : ℕ}
      (a : hom W X _⦋n⦌) (b : hom X Y _⦋n⦌) (c : hom Y Z _⦋n⦌),
      comp (comp a b) c = comp a (comp b c)

/-- A simplicial set `K` is contractible when it has a `0`-simplex and every map
from the boundary of a positive-dimensional standard simplex into `K` extends to
the whole simplex. For a Kan complex this is equivalent to weak contractibility
(trivial `π₀` and trivial higher homotopy groups at every basepoint). -/
def IsContractible (K : SSet.{u}) : Prop :=
  Nonempty (K _⦋0⦌) ∧
  ∀ (n : ℕ) (f : (∂Δ[n + 1]).toSSet ⟶ K), ∃ g : Δ[n + 1] ⟶ K, (∂Δ[n + 1]).ι ≫ g = f

/-- A terminal object of an (∞,1)-category: an object `*` such that every hom
∞-groupoid `𝐇(X, *)` is contractible. -/
structure TerminalObject (H : InfinityOneCategory.{u}) where
  /-- The underlying object `*`. -/
  star : H.Obj
  /-- Every hom ∞-groupoid into `*` is contractible. -/
  contractible : ∀ X : H.Obj, IsContractible (H.hom X star)

/-- A pointed object of `𝐇`: an object `A` equipped with a morphism `* ⟶ A`
from the terminal object. -/
structure PointedObject (H : InfinityOneCategory.{u}) (T : TerminalObject H) where
  /-- The underlying coefficient object `A`. -/
  A : H.Obj
  /-- The pointing `* ⟶ A`, as a `0`-simplex of `𝐇(*, A)`. -/
  pt : H.hom T.star A _⦋0⦌

end NLabCohomology


