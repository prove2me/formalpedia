-- Prove2me | Definitions.Def_FlowsNetworks_Matrices_Digraph
-- name    : FlowsNetworks_Matrices_Digraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:14.848377+00:00
-- url     : https://prove2.me/theorems/87fa5f14-1d1b-429f-af84-1d8b0a8ef6c3
-- title:
--   Finite directed graph $[N; \mathcal A]$, subgraphs, local degrees $e_H(x)$, $i_H(x)$, the sets $A(X)$, $B(X)$ and the counts $|(X, y)|$, $|(y, X)|$
-- statement:
--   Following Chapter I (§1) and Chapter II (§11) of Ford and Fulkerson's *Flows in Networks*, this file sets up the objects of the subgraph problem for directed graphs.
--
--   1. A **directed graph** $G = [N; \mathcal A]$ consists of a finite set $N$ of **nodes** and a set $\mathcal A$ of ordered pairs $(x, y)$ of nodes, the **arcs**, with $x \neq y$ for every arc. There is at most one arc from $x$ to $y$, but both $(x, y)$ and $(y, x)$ may be arcs.
--   2. A **subgraph** $H = [N; \mathcal A']$ of $G$ has the same nodes and an arc set $\mathcal A' \subseteq \mathcal A$.
--   3. For a set $H$ of arcs and a node $x$, the **local degree** of $H$ at $x$ is the pair $e_H(x)$, $i_H(x)$: $e_H(x)$ is the number of arcs of $H$ entering $x$, and $i_H(x)$ the number of arcs of $H$ issuing from $x$.
--   4. For a set $X \subseteq N$ of nodes,
--   $$A(X) = \{\, y \in N \mid (x, y) \in \mathcal A \text{ for some } x \in X \,\}, \qquad B(X) = \{\, y \in N \mid (y, x) \in \mathcal A \text{ for some } x \in X \,\}.$$
--   5. For $X \subseteq N$ and a node $y$, $|(X, y)|$ is the number of arcs of $G$ from a node of $X$ to $y$, and $|(y, X)|$ the number of arcs of $G$ from $y$ to a node of $X$.
--
--   These are the objects of Theorem 11.1 (subgraphs with local degrees between prescribed bounds) and of Ore's Corollary 11.2 (subgraphs with prescribed local degrees).
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality; arcs are a `Finset (N × N)` with a looplessness field. A subgraph is identified with its arc set $\mathcal A' \subseteq \mathcal A$ (`IsSubgraph`), and `outDeg H x`, `inDeg H x` are $i_H(x)$, $e_H(x)$ for any finite arc set $H$. `succSet`, `predSet`, `numArcsTo`, `numArcsFrom` are $A(X)$, $B(X)$, $|(X, y)|$, $|(y, X)|$; all are natural-number valued.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–4 (§1, networks: finite, no loops, at most one arc from x to y); Chapter II, p. 60 (§10, A(x) extended to sets), p. 70 (§11, local degree, subgraph)

import Mathlib

namespace FlowsNetworks.Matrices

/-- A finite directed graph `G = [N; 𝒜]` (Ford–Fulkerson, *Flows in Networks*, Chapter I, §1,
pp. 3–4, and Chapter II, §11, p. 70). The node set `N` is a finite type; the arc set `𝒜` is a finite
set of ordered pairs of nodes, so there is at most one arc from `x` to `y` (both `(x, y)` and
`(y, x)` may be arcs), and no arc leads from a node to itself. -/
structure Digraph (N : Type) [Fintype N] [DecidableEq N] where
  /-- the arc set `𝒜 ⊆ N × N` -/
  arcs : Finset (N × N)
  /-- no arc leads from a node to itself -/
  loopless : ∀ p ∈ arcs, p.1 ≠ p.2

variable {N : Type} [Fintype N] [DecidableEq N]

/-- A subgraph `H = [N; 𝒜′]` of `G` (Chapter II, §11, p. 70) has the same node set and an arc set
`𝒜′ ⊆ 𝒜`; it is identified with its arc set `𝒜′`. -/
def IsSubgraph (G : Digraph N) (H : Finset (N × N)) : Prop :=
  H ⊆ G.arcs

/-- `i_H(x)`: the number of arcs of the arc set `H` issuing from the node `x`. -/
def outDeg (H : Finset (N × N)) (x : N) : ℕ :=
  (H.filter (fun p => p.1 = x)).card

/-- `e_H(x)`: the number of arcs of the arc set `H` entering the node `x`. -/
def inDeg (H : Finset (N × N)) (x : N) : ℕ :=
  (H.filter (fun p => p.2 = x)).card

/-- `A(X) = {y ∈ N | (x, y) ∈ 𝒜 for some x ∈ X}`: the nodes reached by an arc of `G` issuing
from `X` (Chapter II, p. 60, extended to sets). -/
def succSet (G : Digraph N) (X : Finset N) : Finset N :=
  (G.arcs.filter (fun p => p.1 ∈ X)).image Prod.snd

/-- `B(X) = {y ∈ N | (y, x) ∈ 𝒜 for some x ∈ X}`: the nodes from which an arc of `G` enters `X`. -/
def predSet (G : Digraph N) (X : Finset N) : Finset N :=
  (G.arcs.filter (fun p => p.2 ∈ X)).image Prod.fst

/-- `|(X, y)|`: the number of arcs of `G` leading from a node of `X` to the node `y`. -/
def numArcsTo (G : Digraph N) (X : Finset N) (y : N) : ℕ :=
  (G.arcs.filter (fun p => p.1 ∈ X ∧ p.2 = y)).card

/-- `|(y, X)|`: the number of arcs of `G` leading from the node `y` to a node of `X`. -/
def numArcsFrom (G : Digraph N) (y : N) (X : Finset N) : ℕ :=
  (G.arcs.filter (fun p => p.1 = y ∧ p.2 ∈ X)).card

end FlowsNetworks.Matrices


