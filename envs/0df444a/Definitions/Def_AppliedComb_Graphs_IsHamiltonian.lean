-- Prove2me | Definitions.Def_AppliedComb_Graphs_IsHamiltonian
-- name    : AppliedComb_Graphs_IsHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:59:31.981735+00:00
-- url     : https://prove2.me/theorems/2aa4a2b5-6bca-4013-9f4e-01af7d2686f1
-- title:
--   Hamiltonian cycle and hamiltonian graph (Section 5.3)
-- statement:
--   Let $G = (V, E)$ be a graph. A **hamiltonian cycle** of $G$ is a finite sequence $(x_1, x_2, \dots, x_n)$ of vertices such that
--
--   1. every vertex of $G$ appears exactly once in the sequence;
--   2. $x_1 x_n$ is an edge of $G$;
--   3. $x_i x_{i+1}$ is an edge of $G$ for each $i = 1, 2, \dots, n-1$.
--
--   The graph $G$ is **hamiltonian** if it has a hamiltonian cycle.
--
--   Because no lower bound on $n$ is imposed, the complete graph $K_2$ is hamiltonian (the sequence $(x_1, x_2)$ works, its closing edge $x_1x_2$ being the same edge as its step), while a graph with one vertex, or with no vertices, is not (condition 2 needs a first and a last entry joined by an edge, and a graph has no loops).
--
--   **Formalization Note.** The sequence is a Lean `List V`; condition 1 is `Nodup` together with membership of every vertex, condition 3 is `List.IsChain G.Adj`, and condition 2 asserts that the first and last entries (`head?`, `getLast?`) exist and are adjacent. This is the book's notion, not Mathlib's `SimpleGraph.Walk.IsHamiltonianCycle`, which requires a cycle and hence at least three vertices.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 79, Section 5.3 (definition of hamiltonian)

import Mathlib

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 79. A *hamiltonian cycle* of a graph `G` is a sequence
`(x₁, x₂, …, xₙ)` of vertices such that (1) every vertex of `G` appears exactly once in the
sequence, (2) `x₁xₙ` is an edge of `G`, and (3) `xᵢxᵢ₊₁` is an edge of `G` for
`i = 1, …, n - 1`. The sequence is the list `xs`; condition (1) is `Nodup` plus membership of
every vertex, condition (3) is `IsChain G.Adj`, and condition (2) says the first and last
entries exist and are adjacent. No lower bound on the length is imposed, so `K₂` is
hamiltonian (as on the page), while a one-vertex graph is not (`x₁x₁` is never an edge). -/
def IsHamiltonianCycle {V : Type*} (G : SimpleGraph V) (xs : List V) : Prop :=
  xs.Nodup ∧ (∀ v : V, v ∈ xs) ∧ xs.IsChain G.Adj ∧
    ∃ a b : V, xs.head? = some a ∧ xs.getLast? = some b ∧ G.Adj a b

/-- Keller–Trotter, p. 79. A graph is *hamiltonian* if it has a hamiltonian cycle in the sense
of `IsHamiltonianCycle`. -/
def IsHamiltonian {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ xs : List V, IsHamiltonianCycle G xs

end AppliedComb.Graphs


