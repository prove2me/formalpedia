-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_Polytope
-- name    : ExtensionComplexity_TSP_Polytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:47:23.583144+00:00
-- url     : https://prove2.me/theorems/d59ab6cb-c425-468d-9811-e1f776aa3d41
-- title:
--   Polytopes, faces, facets and extensions
-- statement:
--   Let $\iota$ be a finite index set.
--
--   1. A **polytope** is a set $P\subseteq\mathbb R^{\iota}$ of the form $P=\mathrm{conv}(V)$ for a finite set $V$.
--   2. A **face** of $P$ is either $P$ itself or the intersection $\{x\in P : c^\top x=\delta\}$ of $P$ with a valid hyperplane, i.e. one with $c\neq 0$ and $c^\top x\le\delta$ for all $x\in P$. The empty set may be a face.
--   3. A face is **proper** if it is not $P$ itself, and a **facet** is a maximal proper face.
--   4. $Q$ has **at most $r$ facets** if its facets can be listed as a finite family of at most $r$ sets.
--   5. A polytope $Q\subseteq\mathbb R^{\kappa}$ is an **extension** of $P\subseteq\mathbb R^{\iota}$ if there is a linear map $\pi:\mathbb R^{\kappa}\to\mathbb R^{\iota}$ with $\pi(Q)=P$.
--
--   These are the notions of Appendix A and §3 of the paper. Faces and extensions carry lower bounds on extension complexity from one polytope to another (Lemma 9), and the number of facets of an extension is its size in Yannakakis's theorem (Theorem 3).
--
--   **Formalization Note** Facets are relative to the polytope itself (maximal proper faces), so they are meaningful for polytopes that are not full-dimensional. The count of facets uses an explicit `Finset` of sets, not `Set.ncard` (which would be $0$ on an infinite family).
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, Appendix A, pp. 17:20-17:21 (polytope, valid hyperplane, face, proper face, facet); p. 17:9, (2) (extension); p. 17:10, Theorem 3 (ii) (size of an extension = number of facets)

import Mathlib

namespace ExtensionComplexity.TSP

/-- **Polytope** (Appendix A, p. 17:20): the convex hull of a finite set of points of `ℝ^ι`. -/
def IsPolytope {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  ∃ V : Finset (ι → ℝ), P = convexHull ℝ (V : Set (ι → ℝ))

/-- **Face** (Appendix A, p. 17:20): a face of `P` is either `P` itself or the intersection of `P`
with a valid hyperplane `{x | c ⬝ᵥ x = δ}`, `c ≠ 0`, where valid means `c ⬝ᵥ x ≤ δ` for all
`x ∈ P`. The empty face is allowed (a valid hyperplane may miss `P`). -/
def IsFace {ι : Type*} [Fintype ι] (P F : Set (ι → ℝ)) : Prop :=
  F = P ∨ ∃ (c : ι → ℝ) (δ : ℝ), c ≠ 0 ∧ (∀ x ∈ P, c ⬝ᵥ x ≤ δ) ∧
    F = {x | x ∈ P ∧ c ⬝ᵥ x = δ}

/-- **Facet** (Appendix A, p. 17:20): a maximal proper face, i.e. a face `F ≠ P` contained in no
other proper face. -/
def IsFacet {ι : Type*} [Fintype ι] (P F : Set (ι → ℝ)) : Prop :=
  IsFace P F ∧ F ≠ P ∧ ∀ G : Set (ι → ℝ), IsFace P G → G ≠ P → F ⊆ G → G = F

/-- `Q` has **at most `r` facets**: its facets form a finite family, listed by a `Finset` of
cardinality at most `r` (p. 17:10, Theorem 3 (ii): "extension of size at most r (i.e., with at
most r facets)"). -/
def HasAtMostFacets {κ : Type*} [Fintype κ] (Q : Set (κ → ℝ)) (r : ℕ) : Prop :=
  ∃ fs : Finset (Set (κ → ℝ)), (∀ F, IsFacet Q F ↔ F ∈ fs) ∧ fs.card ≤ r

/-- **Extension** (p. 17:9, (2)): `Q ⊆ ℝ^κ` is an extension of `P ⊆ ℝ^ι` if `Q` is a polytope and
some linear map `π : ℝ^κ → ℝ^ι` satisfies `π(Q) = P`. -/
def IsExtension {κ ι : Type*} (Q : Set (κ → ℝ)) (P : Set (ι → ℝ)) : Prop :=
  IsPolytope Q ∧ ∃ π : (κ → ℝ) →ₗ[ℝ] (ι → ℝ), π '' Q = P

end ExtensionComplexity.TSP


