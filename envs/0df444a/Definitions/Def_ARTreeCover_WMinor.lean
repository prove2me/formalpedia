-- Prove2me | Definitions.Def_ARTreeCover_WMinor
-- name    : ARTreeCover_WMinor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:51.370261+00:00
-- url     : https://prove2.me/theorems/88f2fc17-26b9-4c90-ba6a-8bad6455e2f9
-- title:
--   Weighted minors, in the branch-set model
-- statement:
--   A weighted graph $H$ on a vertex set $W$ is a **minor** of $G=(V,E,w)$ if there are pairwise disjoint nonempty sets $\beta(a)\subseteq V$, $a\in W$, each inducing a connected subgraph of $G$, such that every edge $ab$ of $H$ has an edge $xy\in E$ with $x\in\beta(a)$, $y\in\beta(b)$ and
--
--   $$w_H(ab)=w_G(xy).$$
--
--   The paper defines a minor as a graph obtained by a sequence of vertex deletions, edge deletions and edge contractions. A deleted or contracted edge disappears, and the edge surviving between two contracted sets is one of the $G$-edges between them, so it keeps that edge's weight; conversely every such choice arises by deleting the other edges first.
--
--   **Formalization Note** The unweighted part is the model of `RobertsonSeymour1986.GM5.IsMinor`; the weight clause must share the existential with the branch sets, so that definition cannot be reused as a conjunct.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), §2, p.9 (PDF p.12)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

namespace ARTreeCover

/-- `WMinor H G`: the weighted graph `H` (on its own vertex type `W`) is a minor of the weighted
graph `G`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), §2, p.9 (PDF p.12): "A minor of G is a graph
that is obtained from G by a sequence of vertex deletions, edge deletions and edge contractions."

Branch-set model: there are pairwise disjoint, nonempty vertex sets `β a ⊆ V` (`a ∈ W`), each
inducing a connected subgraph of `G`, such that every edge `ab` of `H` is witnessed by an edge `xy`
of `G` with `x ∈ β a`, `y ∈ β b`, and the weight of `ab` in `H` is the weight of `xy` in `G`.

**Formalization Note.** The unweighted part is the model of `RobertsonSeymour1986.GM5.IsMinor`
(platform id 75f53c97). Weights: a deleted edge disappears, a contracted edge disappears, and the
edge `ab` that survives between two contracted branch sets is one of the `G`-edges between them
(the others having been deleted), so it carries that edge's weight. Conversely every such choice
arises by deleting the other edges first. Quantifying over `H` on its own type builds in "up to
isomorphism". -/
def WMinor {W V : Type} (H : WGraph W) (G : WGraph V) : Prop :=
  ∃ β : W → Set V,
    (∀ a, (β a).Nonempty ∧ (G.graph.induce (β a)).Connected) ∧
    Pairwise (fun a b => Disjoint (β a) (β b)) ∧
    ∀ a b, H.graph.Adj a b →
      ∃ x ∈ β a, ∃ y ∈ β b, G.graph.Adj x y ∧ H.w s(a, b) = G.w s(x, y)

end ARTreeCover


