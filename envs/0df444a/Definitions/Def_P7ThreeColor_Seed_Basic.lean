-- Prove2me | Definitions.Def_P7ThreeColor_Seed_Basic
-- name    : P7ThreeColor_Seed_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:55.347301+00:00
-- url     : https://prove2.me/theorems/ff915200-b748-46e4-8109-27087f13dee7
-- title:
--   §2, p. 6 — induced-path-free graphs, neighborhoods, domination, and 2-domination
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V(G)$. A graph is **$P_t$-free** when it has no induced subgraph isomorphic to the path on $t$ vertices. For $S\subseteq V(G)$, let $N(S)$ be the vertices outside $S$ adjacent to at least one vertex of $S$, and set $\bar S=S\cup N(S)$. Then
--
--   $$
--   S\text{ dominates }G\iff\bar S=V(G),\qquad
--   S\text{ 2-dominates }G\iff\overline{\bar S}=V(G).
--   $$
--
--   These definitions provide the graph vocabulary used by Theorem 4 and Corollary 5, including the distinction between ordinary and two-step domination.
--
--   **Formalization Note** Graphs have finite vertex types, and vertex sets are finite sets. The path exclusion uses induced containment (an injective map preserving adjacency and non-adjacency), not subgraph containment. The filter defining $N(S)$ uses classical decidability, so no decidability of adjacency is assumed.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, pp. 2–3, 6, §1–§2

import Mathlib

namespace P7ThreeColor.Seed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` is `P_t`-free: no induced subgraph of `G` is isomorphic to the path on `t` vertices. -/
def PFree {W : Type*} (t : ℕ) (H : SimpleGraph W) : Prop :=
  ¬ (SimpleGraph.pathGraph t).IsIndContained H

open Classical in
/-- `N(S)`: the vertices outside `S` with a neighbor in `S` (p. 6). -/
noncomputable def nbhd (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ S ∧ ∃ s ∈ S, G.Adj v s)

/-- `S̄ = S ∪ N(S)` (p. 6). -/
noncomputable def closure (G : SimpleGraph V) (S : Finset V) : Finset V := S ∪ nbhd G S

/-- `S` is dominating: `S̄ = V(G)` (p. 6). -/
def IsDominating (G : SimpleGraph V) (S : Finset V) : Prop := closure G S = Finset.univ

/-- `S` is 2-dominating: `S̄` dominates `G` (p. 6; equivalently every vertex is at distance ≤ 2 from `S`, p. 3). -/
def IsTwoDominating (G : SimpleGraph V) (S : Finset V) : Prop := IsDominating G (closure G S)

end P7ThreeColor.Seed


