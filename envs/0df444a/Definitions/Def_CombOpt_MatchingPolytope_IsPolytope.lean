-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsPolytope
-- name    : CombOpt_MatchingPolytope_IsPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:24.404484+00:00
-- url     : https://prove2.me/theorems/2cf8afea-a867-4d28-9036-b51005e5e38b
-- title:
--   A polytope: a bounded polyhedron
-- statement:
--   A polyhedron $P\subseteq\mathbb R^n$ is a **polytope** if there exist $l,u\in\mathbb R^n$ such that $l\le x\le u$ (componentwise) for all $x\in P$.
--
--   By Theorem 6.11, polytopes are exactly the convex hulls of finite sets.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron

namespace CombOpt.MatchingPolytope

/-- **A polytope.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF p. 212): "a polyhedron P ⊆ ℝ^n is a polytope if there exist
l, u ∈ ℝ^n such that l ≤ x ≤ u for all x ∈ P."

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. `l ≤ x` is the componentwise order of `ι → ℝ`. -/
def IsPolytope {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  IsPolyhedron P ∧ ∃ l u : ι → ℝ, ∀ x ∈ P, l ≤ x ∧ x ≤ u

end CombOpt.MatchingPolytope


