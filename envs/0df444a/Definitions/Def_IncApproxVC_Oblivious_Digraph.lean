-- Prove2me | Definitions.Def_IncApproxVC_Oblivious_Digraph
-- name    : IncApproxVC_Oblivious_Digraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:41:56.415218+00:00
-- url     : https://prove2.me/theorems/e1555031-015b-46b5-a9d2-60f4d2ec5d79
-- title:
--   Simple directed graphs: $E_G(S,T)$, boundaries $\partial^\pm$, degrees, out-volume $\mathrm{vol}^+$, neighbourhoods $N^\pm$, the reversed graph
-- statement:
--   A **directed graph** $G=(V,E)$ on a finite vertex set $V$ is a finite set $E\subseteq V\times V$ of ordered pairs, its **edges**. Being a set, $E$ has no parallel edges; the graph is **simple** when moreover no edge is a loop $(v,v)$ (`Loopless`). The paper considers simple, unweighted, directed graphs throughout, so every statement of this mission about a graph assumes `Loopless`.
--
--   For vertex sets $S,T\subseteq V$ and $A\subseteq V$:
--   $$E_G(S,T)=\{(u,v)\in E\mid u\in S,\ v\in T\},\qquad \partial^+_G(A)=E_G(A,V\setminus A),\qquad \partial^-_G(A)=E_G(V\setminus A,A).$$
--   The **out-degree** and **in-degree** of $v$ are $\deg^+_G(v)=|\partial^+_G(\{v\})|$ and $\deg^-_G(v)=|\partial^-_G(\{v\})|$, and the **out-volume** of $A$ is $\mathrm{vol}^+_G(A)=\sum_{v\in A}\deg^+_G(v)$. The **out-neighbourhood** $N^+_G(A)$ is the set of heads of the edges of $\partial^+_G(A)$ (so it is disjoint from $A$), the **in-neighbourhood** $N^-_G(A)$ the set of tails of the edges of $\partial^-_G(A)$, and $N^\pm_G[A]=A\cup N^\pm_G(A)$. The **reversed graph** $\overleftarrow G$ has the edge $(v,u)$ for every edge $(u,v)$ of $G$, and $m=|E|$ is the number of edges.
--
--   **Formalization Note.** `Digraph V` is a structure with one field `edges : Finset (V × V)`; looplessness is the separate predicate `Loopless`, so that an initial graph plus insertions is again a `Digraph` without proof obligations. `vol` is the out-volume $\mathrm{vol}^+$; the paper's in-volume is not used by any statement of the mission.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 3, §2 (Graphs; Volumes and Boundaries)

import Mathlib

/-!
# Directed graphs, boundaries, degrees, volumes and neighbourhoods

Adena, Henzinger, Rutschmann, *Incremental Approximate Vertex Connectivity via Almost-Linear Time
Local Cut Algorithms*, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 3, §2 ("Graphs",
"Volumes and Boundaries").

"Unless explicitly stated otherwise, we always consider simple, unweighted, directed graphs."
A graph on a finite vertex type `V` is a finite set of ordered pairs (its edges). Being a finite
set, it has no parallel edges; `Loopless` is the remaining half of "simple" and is a hypothesis of
every statement of the mission that is about a graph.

* `edgesBetween G S T` is `E_G(S, T) = {(u, v) ∈ E | u ∈ S, v ∈ T}`.
* `outBoundary G A` is `∂⁺_G(A) = E_G(A, V \ A)`, `inBoundary G A` is `∂⁻_G(A) = E_G(V \ A, A)`.
* `outDeg G v` is `deg⁺_G(v) = |∂⁺_G({v})|`, `inDeg G v` is `deg⁻_G(v) = |∂⁻_G({v})|`.
* `vol G A` is the out-volume `vol⁺_G(A) = Σ_{v ∈ A} deg⁺_G(v)`.
* `outNbhd G A` is `N⁺_G(A)`, the heads of the edges of `∂⁺_G(A)` (so it is disjoint from `A`);
  `inNbhd G A` is `N⁻_G(A)`, the tails of the edges of `∂⁻_G(A)`; `closedOutNbhd G A` is
  `N⁺_G[A] = A ∪ N⁺_G(A)` and `closedInNbhd G A` is `N⁻_G[A] = A ∪ N⁻_G(A)`.
* `reverse G` is the reversed graph with every edge `(u, v)` replaced by `(v, u)`.
* `numEdges G` is `m = |E|`.
-/

namespace IncApproxVC.Oblivious

/-- A directed graph on the finite vertex type `V`: a finite set of ordered pairs, its edges.
There are no parallel edges; loops are excluded by the separate predicate `Loopless`. -/
structure Digraph (V : Type*) where
  /-- The edge set `E ⊆ V × V`. -/
  edges : Finset (V × V)

namespace Digraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No edge is a loop: together with the finite edge set this makes the graph simple. -/
def Loopless (G : Digraph V) : Prop :=
  ∀ e ∈ G.edges, e.1 ≠ e.2

/-- `E_G(S, T)`: the edges with tail in `S` and head in `T`. -/
def edgesBetween (G : Digraph V) (S T : Finset V) : Finset (V × V) :=
  G.edges.filter (fun e => e.1 ∈ S ∧ e.2 ∈ T)

/-- `∂⁺_G(A) = E_G(A, V \ A)`, the edges leaving `A`. -/
def outBoundary (G : Digraph V) (A : Finset V) : Finset (V × V) :=
  G.edgesBetween A Aᶜ

/-- `∂⁻_G(A) = E_G(V \ A, A)`, the edges entering `A`. -/
def inBoundary (G : Digraph V) (A : Finset V) : Finset (V × V) :=
  G.edgesBetween Aᶜ A

/-- The out-degree `deg⁺_G(v) = |∂⁺_G(v)| = |E_G({v}, V \ {v})|`. -/
def outDeg (G : Digraph V) (v : V) : ℕ :=
  (G.outBoundary {v}).card

/-- The in-degree `deg⁻_G(v) = |∂⁻_G(v)| = |E_G(V \ {v}, {v})|`. -/
def inDeg (G : Digraph V) (v : V) : ℕ :=
  (G.inBoundary {v}).card

/-- The out-volume `vol⁺_G(A) = Σ_{v ∈ A} deg⁺_G(v)`. -/
def vol (G : Digraph V) (A : Finset V) : ℕ :=
  ∑ v ∈ A, G.outDeg v

/-- The out-neighbourhood `N⁺_G(A) = {v | (u, v) ∈ ∂⁺_G(A)}`. -/
def outNbhd (G : Digraph V) (A : Finset V) : Finset V :=
  (G.outBoundary A).image Prod.snd

/-- The in-neighbourhood `N⁻_G(A) = {u | (u, v) ∈ ∂⁻_G(A)}`. -/
def inNbhd (G : Digraph V) (A : Finset V) : Finset V :=
  (G.inBoundary A).image Prod.fst

/-- `N⁺_G[A] = A ∪ N⁺_G(A)`. -/
def closedOutNbhd (G : Digraph V) (A : Finset V) : Finset V :=
  A ∪ G.outNbhd A

/-- `N⁻_G[A] = A ∪ N⁻_G(A)`. -/
def closedInNbhd (G : Digraph V) (A : Finset V) : Finset V :=
  A ∪ G.inNbhd A

/-- The reversed graph `←G`: the same vertices, every edge `(u, v)` replaced by `(v, u)`. -/
def reverse (G : Digraph V) : Digraph V :=
  ⟨G.edges.image Prod.swap⟩

/-- The number of edges `m = |E|`. -/
def numEdges (G : Digraph V) : ℕ :=
  G.edges.card

end Digraph

end IncApproxVC.Oblivious


