-- Prove2me | Definitions.Def_AppliedComb_Graphs_IsEulerian
-- name    : AppliedComb_Graphs_IsEulerian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:59:57.17357+00:00
-- url     : https://prove2.me/theorems/44428bcb-a50c-4d84-a254-f10b68384a9d
-- title:
--   Eulerian circuit and eulerian graph (Section 5.3)
-- statement:
--   Let $G = (V, E)$ be a graph. An **eulerian circuit** of $G$ is a sequence $(x_0, x_1, \dots, x_t)$ of vertices of $G$, repetition allowed, such that
--
--   1. $x_0 = x_t$;
--   2. $x_i x_{i+1}$ is an edge of $G$ for every $i = 0, 1, \dots, t-1$;
--   3. for every edge $e \in E$ there is a unique integer $i$ with $0 \le i < t$ for which $e = x_i x_{i+1}$.
--
--   The graph $G$ is **eulerian** if it has an eulerian circuit. The book introduces this notion only for graphs without isolated vertices; the definition itself is stated for every graph, and the restriction appears as a hypothesis of the theorems that use it.
--
--   **Formalization Note.** The sequence is a nonempty Lean `List V` of length $t+1$ (so the one-vertex sequence, $t = 0$, is allowed, as on the page). Condition 3 is $\forall e \in E,\ \exists!\, i,\ i+1 < \text{length} \wedge e = \{x_i, x_{i+1}\}$, with the edge written as the unordered pair `s(xs[i], xs[i+1])`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 75, Section 5.3 (definition of eulerian)

import Mathlib

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 75. An *eulerian circuit* of a graph `G` is a sequence
`(x₀, x₁, …, x_t)` of vertices, repetition allowed, such that (1) `x₀ = x_t`, (2) `xᵢxᵢ₊₁` is
an edge of `G` for every `i = 0, …, t - 1`, and (3) for every edge `e` of `G` there is a unique
integer `i` with `0 ≤ i < t` for which `e = xᵢxᵢ₊₁`. The sequence is the nonempty list `xs`
of length `t + 1`. -/
def IsEulerianCircuit {V : Type*} (G : SimpleGraph V) (xs : List V) : Prop :=
  xs ≠ [] ∧ xs.head? = xs.getLast? ∧ xs.IsChain G.Adj ∧
    ∀ e ∈ G.edgeSet, ∃! i : ℕ, ∃ h : i + 1 < xs.length, e = s(xs[i], xs[i + 1])

/-- Keller–Trotter, p. 75. A graph is *eulerian* if it has an eulerian circuit. The book defines
this notion only for graphs without isolated vertices; that restriction is carried as a
hypothesis by the theorems that use it. -/
def IsEulerian {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ xs : List V, IsEulerianCircuit G xs

end AppliedComb.Graphs


