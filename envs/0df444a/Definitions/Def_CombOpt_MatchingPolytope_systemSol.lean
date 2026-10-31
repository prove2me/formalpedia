-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_systemSol
-- name    : CombOpt_MatchingPolytope_systemSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:19.286214+00:00
-- url     : https://prove2.me/theorems/98728d31-935a-4ef4-809d-ae64836cadce
-- title:
--   The solution set of a system $A'x=b',\ A''x\le b''$
-- statement:
--   For finite families of rows $a'_j$ with right-hand sides $b'_j$ and rows $a''_i$ with right-hand sides $b''_i$, this is the solution set
--   $$\{x\in\mathbb R^n:\ A'x=b',\ A''x\le b''\}=\{x:\ (a'_j)^\top x=b'_j \text{ for all } j,\ (a''_i)^\top x\le b''_i \text{ for all } i\}.$$
--
--   It is the polyhedron of Theorem 6.17 and Corollary 6.19.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. The rows are indexed by arbitrary types, so that the system with one row omitted is the same object over a smaller index type.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 213 (PDF p. 221), Theorem 6.17

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **The solution set of a system `A′x = b′, A″x ≤ b″`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 213 (PDF p. 221), Theorem 6.17: "P = {x ∈ ℝ^n : A′x = b′, A″x ≤ b″}".

The rows of `A′` are `A' j` (indexed by `κ'`), those of `A″` are `A'' i` (indexed by `κ''`).

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. The index types are arbitrary so that a subsystem (a row omitted) is the same object with a
smaller index type. -/
def systemSol {ι κ' κ'' : Type*} [Fintype ι] (A' : κ' → ι → ℝ) (b' : κ' → ℝ)
    (A'' : κ'' → ι → ℝ) (b'' : κ'' → ℝ) : Set (ι → ℝ) :=
  {x | (∀ j, A' j ⬝ᵥ x = b' j) ∧ ∀ i, A'' i ⬝ᵥ x ≤ b'' i}

end CombOpt.MatchingPolytope


