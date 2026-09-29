-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
-- name    : MaxLatticeFree_Geometry_Polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:13:53.350816+00:00
-- url     : https://prove2.me/theorems/3266de18-ee32-4ac3-8906-eff801da2f79
-- title:
--   Polyhedron in a subspace $W$, polytope, and facet
-- statement:
--   Three standard notions of polyhedral geometry, as used in the statements of Theorems 9 and 10 and Lemma 13.
--
--   1. A **polyhedron in the linear space $W$** is a set of the form
--   $$
--   S=W\cap\{x\in\mathbb R^n \mid \langle a_i,x\rangle\le b_i,\ i=1,\dots,t\}
--   $$
--   for finitely many $a_i\in\mathbb R^n$, $b_i\in\mathbb R$ ($t=0$ gives $W$ itself).
--   2. A **polytope** is the convex hull of finitely many points.
--   3. A **facet** of a convex set $S$ is a nonempty face of codimension one: a set $F=S\cap\{x\mid \langle a,x\rangle=b\}$, where $\langle a,x\rangle\le b$ holds for every $x\in S$, such that $F\neq\emptyset$ and $\dim(F)=\dim(S)-1$.
--
--   The facet notion does not depend on an ambient subspace, so "facet of $S$" and "facet of $S\cap V$" in Theorem 9 use the same definition.
--
--   **Formalization Note** Dimensions are the integer-valued `affDim` ($\dim\emptyset=-1$), and facets are required to be nonempty, so $\emptyset$ is never a facet and a single point has no facets.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, pp. 8–15 (polyhedra, polytopes and facets used throughout; standard notions)

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_affDim

namespace MaxLatticeFree.Geometry

/-- A *polyhedron in the linear space `W`*: the intersection of `W` with finitely many closed
half-spaces `{x | ⟪aᵢ, x⟫ ≤ bᵢ}` (`t = 0` gives `W` itself). -/
def IsPolyhedronIn {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (t : ℕ) (a : Fin t → EuclideanSpace ℝ (Fin n)) (b : Fin t → ℝ),
    S = (W : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | ∀ i, inner ℝ (a i) x ≤ b i}

/-- A *polytope*: the convex hull of a finite set of points. -/
def IsPolytope {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ F : Finset (EuclideanSpace ℝ (Fin n)), P = convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin n)))

/-- `F` is a *facet* of the convex set `S`: `F` is the face `S ∩ {x | ⟪a, x⟫ = b}` cut out by an
inequality `⟪a, x⟫ ≤ b` valid on `S`, `F` is nonempty, and `dim(F) = dim(S) - 1` (integer
dimensions with `dim ∅ = -1`, see `affDim`). The predicate does not depend on an ambient
subspace. -/
def IsFacet {n : ℕ} (S F : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  F.Nonempty ∧ affDim F = affDim S - 1 ∧
    ∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∀ x ∈ S, inner ℝ a x ≤ b) ∧
      F = S ∩ {x | inner ℝ a x = b}

end MaxLatticeFree.Geometry


