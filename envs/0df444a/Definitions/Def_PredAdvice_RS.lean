-- Prove2me | Definitions.Def_PredAdvice_RS
-- name    : PredAdvice_RS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:18.237058+00:00
-- url     : https://prove2.me/theorems/448d3616-f393-46be-b75f-eb72ad07a1f5
-- title:
--   The Ruzsa–Szemerédi function $RS(n)$
-- statement:
--   A **matching is induced** in a graph $G$ if the subgraph of $G$ induced by its endpoints contains only the matching edges. Among $n$-vertex simple graphs whose edges can be partitioned into at most $n$ induced matchings, let $m(n)$ be the maximum number of edges. The **Ruzsa–Szemerédi function** is
--   $$
--   RS(n)=\frac{n^2}{m(n)} ,
--   $$
--   so that $n^2/RS(n)$ is that maximum number of edges.
--
--   The module defines the predicate "the colour classes of an edge colouring are induced matchings" for any graph on any vertex type (two distinct edges of the same colour share no endpoint and no edge of $G$ joins their endpoints), the maximum $m(n)$, and $RS(n)$. The function governs every size bound of the mission.
--
--   **Formalization Note** $m(n)$ is a supremum over a bounded set of natural numbers, hence a maximum. For $n\ge 2$ a single edge is an induced matching, so $m(n)\ge1$; for $n\le1$ the real division returns $0$, and every statement assumes $n\ge2$.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4; §2, p.10

import Mathlib

set_option autoImplicit false

namespace PredAdvice

/-- An edge colouring of a simple graph `G` whose colour classes are **induced matchings**
(Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*,
STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4): "A matching is induced if the
subgraph induced by its endpoints contains only the matching edges."

**Formalization Note** For two distinct edges `e₁ ≠ e₂` of the same colour, no endpoint of `e₁`
equals an endpoint of `e₂` (the class is a matching), and no endpoint of `e₁` is adjacent in `G`
to an endpoint of `e₂` (the class is induced in `G`). For a matching this is exactly the condition
that the subgraph of `G` induced by its endpoints has only the matching edges. A colouring into a
type `κ` partitions the edges into at most `|κ|` induced matchings (unused colours are empty
classes). -/
def IsInducedMatchingColoring {W : Type*} (G : SimpleGraph W) {κ : Type*}
    (col : G.edgeSet → κ) : Prop :=
  ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ → col e₁ = col e₂ →
    ∀ a ∈ (e₁ : Sym2 W), ∀ b ∈ (e₂ : Sym2 W), a ≠ b ∧ ¬ G.Adj a b

/-- The maximum number of edges of an `n`-vertex graph whose edges can be partitioned into at most
`n` induced matchings (§1.1, p.4; §2, p.10). -/
noncomputable def maxInducedEdges (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), ∃ col : G.edgeSet → Fin n,
    IsInducedMatchingColoring G col ∧ G.edgeSet.ncard = m}

/-- The **Ruzsa–Szemerédi function** `RS(n)` (Kopelowitz, Korin, Roditty, *Using Small Advice to
Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4;
§2, p.10): "Among n-vertex graphs in which the edges can be partitioned into at most n induced
matchings, let n²/RS(n) be the maximum number of edges." So `RS(n) = n² / maxInducedEdges n`.

**Formalization Note** Graphs are simple undirected graphs on `Fin n`. The set of edge counts is
bounded by `n(n−1)/2`, so `sSup` on `ℕ` is a true maximum. For `n ≥ 2` a single edge is an
induced matching, so the maximum is at least `1` and `RS(n)` is the paper's value; for `n ≤ 1`
no graph has an edge and the real division returns `0`, which is why every statement of the
mission assumes `n ≥ 2`. -/
noncomputable def RS (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / (maxInducedEdges n : ℝ)

end PredAdvice


