-- Prove2me | Definitions.Def_DynEdgeOrient_Multigraph
-- name    : DynEdgeOrient_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:18.200975+00:00
-- url     : https://prove2.me/theorems/d518fc28-4ff4-4814-ace5-1343a450208a
-- title:
--   Loop-free multigraphs: $E(S)$, $E(S,T)$ and arboricity at most $\alpha$
-- statement:
--   A **graph** is a multigraph that may have parallel edges but no loops. It is given by a finite vertex set $V$, a set of edge labels $E$, and for each label $e$ its two endpoints $\mathrm{ends}(e)=(u,v)$; parallel edges are distinct labels with the same endpoints. A state of the graph is a finite set $F$ of labels. For vertex sets $S,T\subseteq V$:
--
--   1. $E(S)=E(G[S])$ is the set of edges of $F$ with both endpoints in $S$;
--   2. $E(S,T)$ is the set of edges of $F$ with one endpoint in $S$ and the other in $T$, without regard to direction (the paper uses it for disjoint $S,T$, and writes $E(S,v)=E(v,S)$ for $T=\{v\}$).
--
--   The graph has **arboricity at most $\alpha$** when every vertex set spans few edges:
--
--   $$
--   |E(S)|\le\alpha\,(|S|-1)\qquad\text{for every }S\subseteq V .
--   $$
--
--   This is the paper's $\alpha(G)=\max_{U\subseteq V,\,|U|\ge2}\lceil |E(U)|/(|U|-1)\rceil\le\alpha$. It is the sparsity measure of the whole mission: forests have arboricity $1$, planar graphs at most $3$.
--
--   **Formalization Note** Loop-freeness, $(\mathrm{ends}\,e)_1\neq(\mathrm{ends}\,e)_2$, is a hypothesis of every theorem rather than part of the type. The bound is in $\mathbb N$, where $|S|-1$ truncates to $0$ at $|S|\le1$; a loop-free graph has no edge inside such an $S$.
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 (arboricity) and §1.5, p.4 (notation)

import Mathlib

namespace DynEdgeOrient

/-!
# Loop-free multigraphs, edge counts and arboricity

S. Hiken, N. Wein, *Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n
Barrier*, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 (arboricity) and §1.5,
p.4 (notation).

**Formalization Note.**
* A graph is "a multigraph that permits multiple parallel edges but does not permit loops"
  (§1.5). It is encoded by a vertex type `V`, an edge-label type `E` and the endpoint map
  `ends : E → V × V`; a graph state is a finite set `F : Finset E` of labels. Parallel edges are
  distinct labels with the same endpoints. Loop-freeness is the separate hypothesis
  `∀ e, (ends e).1 ≠ (ends e).2`, carried by every theorem of the mission.
* `edgesIn ends F S` is the paper's `E(S) = E(G[S])`: the labels of `F` with both endpoints in `S`.
* `edgesBetween ends F S T` is the paper's `E(S, T)`: the labels with one endpoint in `S` and the
  other in `T`, without regard to direction. The paper uses it only for disjoint `S`, `T`
  (`E(S, v) = E(v, S)` is `edgesBetween ends F {v} S` with `v ∉ S`).
* Arboricity (p.1) is `α(G) = max_{U ⊆ V, |U| ≥ 2} ⌈|E(U)| / (|U| − 1)⌉`, so "arboricity ≤ α" is
  `|E(U)| ≤ α (|U| − 1)` for every `U`. `ArboricityLE` states it for every finite `S`, in `ℕ`;
  the truncated subtraction only matters at `|S| ≤ 1`, where a loop-free graph has no edge in `S`.
-/

variable {V E : Type*} [DecidableEq V]

/-- `E(S)`: the edges of the state `F` with both endpoints in `S` (Hiken–Wein, §1.5, p.4). -/
def edgesIn (ends : E → V × V) (F : Finset E) (S : Finset V) : Finset E :=
  F.filter (fun e => (ends e).1 ∈ S ∧ (ends e).2 ∈ S)

/-- `E(S, T)`: the edges of `F` with one endpoint in `S` and the other in `T`, undirected
(Hiken–Wein, §1.5, p.4). -/
def edgesBetween (ends : E → V × V) (F : Finset E) (S T : Finset V) : Finset E :=
  F.filter (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∈ T) ∨ ((ends e).1 ∈ T ∧ (ends e).2 ∈ S))

/-- Arboricity at most `α` (Hiken–Wein, §1, p.1): every vertex set `S` spans at most
`α (|S| − 1)` edges of `F`. -/
def ArboricityLE (ends : E → V × V) (F : Finset E) (α : ℕ) : Prop :=
  ∀ S : Finset V, (edgesIn ends F S).card ≤ α * (S.card - 1)

end DynEdgeOrient


