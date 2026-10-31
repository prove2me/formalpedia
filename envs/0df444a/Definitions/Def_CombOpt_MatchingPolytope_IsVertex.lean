-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsVertex
-- name    : CombOpt_MatchingPolytope_IsVertex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:20.332211+00:00
-- url     : https://prove2.me/theorems/b6be4cc0-04df-4c4e-8792-9244321113d2
-- title:
--   A vertex of a polyhedron
-- statement:
--   A vector $v\in P$ is a **vertex** of the polyhedron $P$ if $\{v\}$ is a face of $P$.
--
--   By Theorem 6.10 a polytope is the convex hull of its vertices.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 205 (PDF p. 213)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsFace

namespace CombOpt.MatchingPolytope

/-- **A vertex.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 205 (PDF p. 213): "A vector v ∈ P is called a vertex if {v} is a face of P."

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. -/
def IsVertex {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (v : ι → ℝ) : Prop :=
  v ∈ P ∧ IsFace P {v}

end CombOpt.MatchingPolytope


