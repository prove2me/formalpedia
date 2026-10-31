-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
-- name    : CombOpt_MatchingPolytope_IsPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:23.907611+00:00
-- url     : https://prove2.me/theorems/61d461c7-2779-422b-b5d8-3aec71240b84
-- title:
--   A polyhedron: the solution set of finitely many linear inequalities
-- statement:
--   A set $P\subseteq\mathbb R^n$ is a **polyhedron** if it is the solution set of a finite system of linear inequalities:
--   $$P=\{x\in\mathbb R^n:\ Ax\le b\}$$
--   for some $m\ge0$, $A\in\mathbb R^{m\times n}$ and $b\in\mathbb R^m$.
--
--   Polyhedra are the objects of §6.2–6.3: polytopes, faces, vertices, facets and dimension are all defined for them.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. An equation is a pair of opposite inequalities; $m=0$ gives the whole space.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 203 (PDF p. 211)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **A polyhedron.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 203 (PDF p. 211): "A polyhedron is the solution set of a finite system of linear
inequalities."

`IsPolyhedron P` says `P = {x | A x ≤ b}` for some `m`, rows `A i` and right-hand sides `b i`.

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. An equation is the pair of inequalities `≤`, `≥`; `m = 0` gives the whole space. -/
def IsPolyhedron {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → ι → ℝ) (b : Fin m → ℝ), P = {x | ∀ i, A i ⬝ᵥ x ≤ b i}

end CombOpt.MatchingPolytope


