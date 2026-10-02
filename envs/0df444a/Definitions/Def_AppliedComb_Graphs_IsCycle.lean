-- Prove2me | Definitions.Def_AppliedComb_Graphs_IsCycle
-- name    : AppliedComb_Graphs_IsCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:00:22.134127+00:00
-- url     : https://prove2.me/theorems/736e5147-d58c-4788-8fa2-800a8964221a
-- title:
--   Cycles, odd cycles, acyclic graphs and trees (Section 5.1)
-- statement:
--   Let $G = (V, E)$ be a graph. A sequence $(x_1, x_2, \dots, x_n)$ of distinct vertices with $x_i x_{i+1} \in E$ for $i = 1, \dots, n-1$ is a **path**. When $n \ge 3$, such a path is a **cycle** if $x_1 x_n$ is also an edge of $G$; its **length** is $n$.
--
--   - $G$ **contains an odd cycle** if it has a cycle of odd length $n$ (equivalently, a subgraph isomorphic to $C_n$ with $n$ odd).
--   - $G$ is **acyclic** if it contains no cycle.
--   - $G$ is a **tree** if it is connected and acyclic.
--
--   **Formalization Note.** Cycles are Lean lists `xs` with `3 ≤ xs.length`, `xs.Nodup`, consecutive entries adjacent (`List.IsChain G.Adj`) and first and last entries adjacent. Connectedness is Mathlib's `SimpleGraph.Connected`: every two vertices are joined by a walk (equivalently a path) and the vertex set is nonempty. These are the book's notions; they do not use Mathlib's `Walk.IsCycle` or `SimpleGraph.IsTree`, though they agree with them.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 71–73, Section 5.1 (path, cycle, acyclic, tree); p. 72 (contains C_n)

import Mathlib

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 71. When `n ≥ 3`, a path `(x₁, x₂, …, xₙ)` of `n` distinct vertices
(consecutive entries adjacent) is a *cycle* when `x₁xₙ` is also an edge of `G`. Its length is
`n`, the length of the list `xs`. -/
def IsCycle {V : Type*} (G : SimpleGraph V) (xs : List V) : Prop :=
  3 ≤ xs.length ∧ xs.Nodup ∧ xs.IsChain G.Adj ∧
    ∃ a b : V, xs.head? = some a ∧ xs.getLast? = some b ∧ G.Adj a b

/-- Keller–Trotter, pp. 72, 82. `G` *contains an odd cycle* if it contains a cycle `Cₙ` with `n`
odd, i.e. a cycle in the sense of `IsCycle` whose length is odd. -/
def ContainsOddCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ xs : List V, IsCycle G xs ∧ Odd xs.length

/-- Keller–Trotter, p. 73. A graph is *acyclic* when it does not contain any cycle on three or
more vertices. -/
def IsAcyclic {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ∃ xs : List V, IsCycle G xs

/-- Keller–Trotter, p. 73. A *tree* is a connected acyclic graph. Connectedness is Mathlib's
`SimpleGraph.Connected` (any two vertices are joined by a walk, equivalently a path, and the
vertex set is nonempty). -/
def IsTree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ IsAcyclic G

end AppliedComb.Graphs


