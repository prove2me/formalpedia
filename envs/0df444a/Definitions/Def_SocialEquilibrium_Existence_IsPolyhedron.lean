-- Prove2me | Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
-- name    : SocialEquilibrium_Existence_IsPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:37:11.606876+00:00
-- url     : https://prove2.me/theorems/af687020-61ab-435d-bee7-8605cd185706
-- title:
--   Convex cells, geometric polyhedra and polyhedra
-- statement:
--   This file fixes the three polyhedral notions of Debreu's §1.
--
--   1. A **convex cell** in a real vector space $E$ is the set of all convex combinations of finitely many points $z^1,\dots,z^r$ with $r\ge 1$:
--   $$C=\Bigl\{z \;\Big|\; z=\sum_{k=1}^r \zeta_k z^k,\ \zeta_k\ge 0,\ \sum_{k=1}^r\zeta_k=1\Bigr\},$$
--   that is, the convex hull of a nonempty finite set.
--   2. A **geometric polyhedron** is the union of a finite number of convex cells.
--   3. A **polyhedron** is a set $P$ that is homeomorphic, as a topological subspace, to a geometric polyhedron $Q$ lying in some Euclidean space $\mathbb R^m$. The set $Q$ is the *geometric antecedent* of $P$.
--
--   Polyhedra are the admissible action sets of the social equilibrium existence theorem. A polyhedron is compact, because a geometric polyhedron is a finite union of compact convex hulls.
--
--   **Formalization Note** The page says that two sets in $\mathbb R^n$ are homeomorphic and does not fix the dimension of the geometric antecedent. Here the antecedent may lie in any $\mathbb R^m$ (Mathlib's `EuclideanSpace ℝ (Fin m)`), and the homeomorphism is between subspaces (`P ≃ₜ Q`). The definition of polyhedron makes sense in any topological space; the theorems of the mission apply it to subsets of finite-dimensional real normed spaces, the paper's "finite Euclidean spaces". A geometric polyhedron may be the union of zero cells (the empty set). The paper does not exclude that case, and the theorems that use polyhedra also assume contractibility, which forces nonemptiness.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 887, §1 Topological Concepts (definitions of homeomorphic, convex cell, geometric polyhedron, polyhedron)

import Mathlib

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 887: a *convex cell* is the set of all convex combinations of finitely
many (at least one) points `z¹, …, zʳ`, i.e. the convex hull of a nonempty finite set. -/
def IsConvexCell {E : Type*} [AddCommGroup E] [Module ℝ E] (C : Set E) : Prop :=
  ∃ s : Finset E, s.Nonempty ∧ C = convexHull ℝ (↑s : Set E)

/-- Debreu (1952), §1, p. 887: a *geometric polyhedron* is the union of a finite number of
convex cells. -/
def IsGeometricPolyhedron {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ S : Finset (Set E), (∀ C ∈ S, IsConvexCell C) ∧ P = ⋃ C ∈ S, C

/-- Debreu (1952), §1, p. 887: a *polyhedron* is a set homeomorphic (as a topological subspace)
to a geometric polyhedron (its *geometric antecedent*) lying in some finite Euclidean space
`ℝᵐ`. -/
def IsPolyhedron {E : Type*} [TopologicalSpace E] (P : Set E) : Prop :=
  ∃ (m : ℕ) (Q : Set (EuclideanSpace ℝ (Fin m))), IsGeometricPolyhedron Q ∧ Nonempty (P ≃ₜ Q)

end SocialEquilibrium.Existence


