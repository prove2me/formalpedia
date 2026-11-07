-- Prove2me | Definitions.Def_TreeCoverLB_IsFracMatching
-- name    : TreeCoverLB_IsFracMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:00.28161+00:00
-- url     : https://prove2.me/theorems/3a780d4d-f632-482e-9230-88cdb5bf31a7
-- title:
--   Intersecting $r$-partite hypergraphs and fractional matchings
-- statement:
--   An **$r$-partite $r$-uniform hypergraph** has disjoint vertex classes $V_1,\dots,V_r$ and a finite family of edges, each containing exactly one vertex from each class. It is **intersecting** if every two edges share a vertex. A **fractional matching** assigns weights $f_e\ge 0$ to the edges with
--   $$
--   \sum_{e\ni v} f_e\le 1\quad\text{for every vertex } v;
--   $$
--   its value is $\sum_e f_e$, and $\nu^*$ is the largest value.
--
--   **Formalization Note** An edge is a word $x\in\prod_i V_i$ ($x_i$ is its vertex in class $i$), so the hypergraph is a finite set $S$ of words; two edges share a vertex iff the words agree in some coordinate, and the vertex $(i,a)$ lies in the edge $x$ iff $x_i=a$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §5.1, p.18 (PDF p.20)

import Mathlib

open Classical

namespace TreeCoverLB

/-- An `r`-partite `r`-uniform hypergraph with vertex classes `V_1, …, V_r` and edge set `S` is
**intersecting** if every two edges have a common vertex (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §5.1, p.18 (PDF p.20)).

**Formalization Note** An edge contains exactly one vertex from each class, so it is a word
`x ∈ ∏_i V_i` (`x i` = its vertex in class `i`), and the hypergraph is a finite set `S` of words;
two edges share a vertex iff the words agree in some coordinate. -/
def IsIntersecting {r : ℕ} {α : Fin r → Type*} (S : Finset ((i : Fin r) → α i)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ i, x i = y i

/-- A **fractional matching** on the `r`-partite `r`-uniform hypergraph with edge set `S`
(Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §5.1, p.18 (PDF p.20)): weights `f_e ≥ 0` on the edges with `Σ_{e ∋ v} f_e ≤ 1` for every
vertex `v`. Its value is `Σ_e f_e` (written `∑ x ∈ S, f x` in the theorems), and `ν*` is the largest
value.

**Formalization Note** Edges are words (see `IsIntersecting`); the vertex `v = (i, a)` lies in the
edge `x` iff `x i = a`. Only the values of `f` on `S` matter. -/
def IsFracMatching {r : ℕ} {α : Fin r → Type*} (S : Finset ((i : Fin r) → α i))
    (f : ((i : Fin r) → α i) → ℝ) : Prop :=
  (∀ x ∈ S, 0 ≤ f x) ∧ ∀ (i : Fin r) (a : α i), ∑ x ∈ S.filter (fun x => x i = a), f x ≤ 1

end TreeCoverLB


