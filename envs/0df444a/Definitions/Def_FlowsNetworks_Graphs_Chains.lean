-- Prove2me | Definitions.Def_FlowsNetworks_Graphs_Chains
-- name    : FlowsNetworks_Graphs_Chains
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:04.915961+00:00
-- url     : https://prove2.me/theorems/c391b653-8e3f-4754-bc03-56918a91ef01
-- title:
--   Directed graph $[N; \mathcal A]$, chains from $S$ to $T$, and $S, T$ disconnecting sets of nodes
-- statement:
--   Following Chapter I (§1) and Chapter II (§4) of Ford and Fulkerson's *Flows in Networks*:
--
--   1. A **graph** $G = [N; \mathcal A]$ has a finite node set $N$ and a set $\mathcal A$ of ordered pairs $(x, y)$ of nodes with $x \ne y$, the **arcs**; there is at most one arc from $x$ to $y$, while both $(x, y)$ and $(y, x)$ may be arcs.
--   2. A **chain** is a sequence $x_1, \dots, x_n$ of $n \ge 2$ distinct nodes such that $(x_i, x_{i+1}) \in \mathcal A$ for $i = 1, \dots, n - 1$; it leads from $x_1$ to $x_n$.
--   3. For node sets $S, T$, a **chain from $S$ to $T$** is a chain whose first node is in $S$ and whose last node is in $T$.
--   4. An **$S, T$ disconnecting set of nodes** is a set $D \subseteq N$ that blocks all chains from $S$ to $T$: every chain from $S$ to $T$ contains a node of $D$. Nodes of $S$ and $T$ may belong to $D$.
--
--   **Formalization Note** A chain is recorded as the `List N` of its nodes (the arcs are determined by consecutive nodes). Intermediate nodes of a chain from $S$ to $T$ may lie in $S$ or $T$; this does not change the maximal number of node disjoint chains nor the blocking sets, since every such chain contains one whose only node in $S$ is the first and only node in $T$ the last.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–4 (§1: networks, chain (1.1)); Chapter II, p. 33 (§4: S, T disconnecting set of nodes)

import Mathlib

namespace FlowsNetworks.Graphs

/-- A directed graph `G = [N; 𝒜]` (Ford–Fulkerson, *Flows in Networks*, Chapter I, pp. 3–4;
Chapter II, §4): a finite node set `N` and a finite set `𝒜` of ordered pairs of nodes, the arcs.
There is at most one arc from `x` to `y`, both `(x, y)` and `(y, x)` may be arcs, and no arc leads
from a node to itself. -/
structure Digraph (N : Type) [Fintype N] [DecidableEq N] where
  /-- the arc set `𝒜 ⊆ N × N` -/
  arcs : Finset (N × N)
  /-- arcs are of the form `(x, y)` with `x ≠ y` -/
  loopless : ∀ p ∈ arcs, p.1 ≠ p.2

namespace Digraph

variable {N : Type} [Fintype N] [DecidableEq N]

/-- A chain (1.1) of `G` (Chapter I, p. 4), recorded by its list of nodes `x₁, …, x_n`: `n ≥ 2`
distinct nodes such that `(x_i, x_{i+1})` is an arc for each `i = 1, …, n − 1`. It leads from
`x₁` to `x_n`. -/
def IsChain (G : Digraph N) (l : List N) : Prop :=
  2 ≤ l.length ∧ l.Nodup ∧
    ∀ (i : ℕ) (h : i + 1 < l.length), (l[i], l[i + 1]) ∈ G.arcs

/-- A chain from `S` to `T`: a chain whose first node lies in `S` and whose last node lies in `T`.
-/
def IsChainFromTo (G : Digraph N) (S T : Finset N) (l : List N) : Prop :=
  G.IsChain l ∧ (∃ x ∈ l.head?, x ∈ S) ∧ ∃ y ∈ l.getLast?, y ∈ T

/-- An `S, T` disconnecting set of nodes (Chapter II, p. 33): a set `D` of nodes that blocks all
chains from `S` to `T`, i.e. every chain from `S` to `T` contains a node of `D`. Nodes of `S` and
`T` may belong to `D`. -/
def IsDisconnecting (G : Digraph N) (S T D : Finset N) : Prop :=
  ∀ l : List N, G.IsChainFromTo S T l → ∃ v ∈ l, v ∈ D

end Digraph

end FlowsNetworks.Graphs


