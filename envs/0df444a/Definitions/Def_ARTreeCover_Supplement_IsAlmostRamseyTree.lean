-- Prove2me | Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyTree
-- name    : ARTreeCover_Supplement_IsAlmostRamseyTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:59.187497+00:00
-- url     : https://prove2.me/theorems/c62d1906-42e0-4aaa-a528-5280b7b69314
-- title:
--   Almost-Ramsey tree and almost-Ramsey HST for scale $\Delta$
-- statement:
--   Let $G$ be a weighted graph, $\Delta>0$, $s\ge0$ and $\alpha>0$. An **almost-Ramsey tree for scale $\Delta$ that satisfies $s$ vertices with stretch $\alpha$** (Definition 18) is a tree $T$ on the vertex set $V$ together with a set $S\subseteq V$ of at least $s$ vertices such that
--   $$d_G(u,v)\le d_T(u,v)\le\alpha\Delta\qquad\text{for every }u\in S\text{ and }v\in V\text{ with }d_G(u,v)\le\Delta.$$
--   It is a **spanning** almost-Ramsey tree if $T$ is a subgraph of $G$.
--
--   An **almost-Ramsey HST for scale $\Delta$ that satisfies $s$ vertices with stretch $\alpha$** is an HST $H$ whose leaves are exactly $V$, together with a set $S$ of at least $s$ vertices such that $d_G(u,v)\le\rho_H(u,v)\le\alpha\Delta$ for the same pairs.
--
--   Unlike Ramsey trees, only pairs within distance $\Delta$ of a satisfied vertex are constrained; this relaxation allows constant stretch for spanning trees (Theorems 24–28).
--
--   **Formalization Note** A tree is a forest of the mission (weights in $(0,\infty]$) whose graph is preconnected; spanning is the separate predicate of the mission (edges of $G$ with $G$'s weights). $s$ is a real number. Definition 18 assumes $G$ connected; the theorems using these predicates assume it.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 18, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `IsAlmostRamseyTree G T Δ s α`: `T` is an almost-Ramsey tree for scale `∆` that satisfies `s`
vertices with stretch `α`: `T` is a tree on `V`, and there is `S ⊆ V` with `|S| ≥ s` such that
`d_G(u, v) ≤ d_T(u, v) ≤ α∆` for every `u ∈ S` and every `v ∈ V` with `d_G(u, v) ≤ ∆`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 18, p.37 (PDF p.40): "an
almost-Ramsey tree for scale ∆ > 0, that satisfies s vertices with stretch α, is a tree T = (V, E′),
such that there exists a subset S ⊆ V of size |S| ≥ s, and for every u ∈ S and v ∈ V with
dG(u, v) ≤ ∆, dG(u, v) ≤ dT(u, v) ≤ α∆. If E′ ⊆ E, i.e., T is a sub-graph of G, we say that T is a
spanning almost-Ramsey tree of G."

**Formalization Note.**
1. A tree on `V` is a published `WForest V` (weights in `(0, ∞]`) whose graph is preconnected; on
   nonempty `V` this is `SimpleGraph.IsTree`. "Spanning" is the separate predicate
   `WForest.IsSpanning G` (edges of `G` with `G`'s weights).
2. Only the pairs `(u, v)` with `u ∈ S` and `d_G(u, v) ≤ ∆` are constrained; nothing is asked of
   other pairs. `s` is a real number ("`|S| ≥ s`"), `α∆` is `ENNReal.ofReal (α * Δ)`.
3. Definition 18 assumes `G` connected; the predicate is stated for any `G`, and the theorems
   using it assume connectivity. -/
def IsAlmostRamseyTree {V : Type} (G : WGraph V) (T : WForest V) (Δ s α : ℝ) : Prop :=
  T.graph.Preconnected ∧
    ∃ S : Finset V, s ≤ (S.card : ℝ) ∧
      ∀ u ∈ S, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ →
        G.dist u v ≤ T.dist u v ∧ T.dist u v ≤ ENNReal.ofReal (α * Δ)

/-- `IsAlmostRamseyHST G H Δ s α`: `H` is an almost-Ramsey HST for scale `∆` that satisfies `s`
vertices with stretch `α`: the leaves of `H` are all of `V`, and there is `S ⊆ V` with `|S| ≥ s`
such that `d_G(u, v) ≤ ρ_H(u, v) ≤ α∆` for every `u ∈ S` and every `v ∈ V` with `d_G(u, v) ≤ ∆`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 18, p.37 (PDF p.40): "an
almost-Ramsey HST for scale ∆ > 0, that satisfies s vertices with stretch α, is an HST H with leaves
L(H) = V, such that there exists a subset S ⊆ V with |S| ≥ s vertices, and for every u ∈ S and
v ∈ V with dG(u, v) ≤ ∆, dG(u, v) ≤ ρH(u, v) ≤ α∆."

**Formalization Note.** HSTs are the published `ARTreeCover.HST` (leaf ultrametric with values in
`[0, ∞]`). Conventions as for `IsAlmostRamseyTree`. -/
def IsAlmostRamseyHST {V : Type} (G : WGraph V) (H : HST V) (Δ s α : ℝ) : Prop :=
  H.leaves = Set.univ ∧
    ∃ S : Finset V, s ≤ (S.card : ℝ) ∧
      ∀ u ∈ S, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ →
        G.dist u v ≤ H.ρ u v ∧ H.ρ u v ≤ ENNReal.ofReal (α * Δ)

end ARTreeCover.Supplement


