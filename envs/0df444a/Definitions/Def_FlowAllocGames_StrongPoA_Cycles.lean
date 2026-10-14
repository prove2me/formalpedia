-- Prove2me | Definitions.Def_FlowAllocGames_StrongPoA_Cycles
-- name    : FlowAllocGames_StrongPoA_Cycles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:32.982037+00:00
-- url     : https://prove2.me/theorems/7bff30a5-ee10-4d01-81ed-415898f22b88
-- title:
--   p. 30 — cycles of the circulation network G′ and decompositions C(f*) of a flow into unit-flow cycles
-- statement:
--   Let $G'$ be the circulation network of a flow allocation game: the graph $G=(V,E)$ together with an auxiliary node $s$, an edge $(v,s)$ and an edge $(s,v)$ for every $v\in V$. Its edges are the edges of $G$ and the auxiliary edges.
--
--   A **cycle** of $G'$ is a non-empty sequence of edges $p_1,\dots,p_k$ of $G'$ such that each $p_{j+1}$ starts at the node where $p_j$ ends, $p_k$ ends at the node where $p_1$ starts, and the start nodes of $p_1,\dots,p_k$ are pairwise distinct (a simple directed cycle). Its **size** is $|C|=k$, the number of its edges, auxiliary edges included.
--
--   For an integral flow $x$ on the edges of $G'$, a **decomposition of $x$ into cycles of unit flow** is a finite list $\mathcal C(x)=(C_1,\dots,C_k)$ of cycles of $G'$, repetitions allowed, such that for every edge $p$ of $G'$
--   $$x_p=\#\{(i,j): \text{the $j$-th edge of $C_i$ is } p\},$$
--   i.e. each edge carries exactly as many units of flow as there are cycle passages through it.
--
--   This is the decomposition $\mathcal C(f^*)$ used on p. 30 to define the parameter $d=\min_{f^*,\mathcal C(f^*)}\max_{C\in\mathcal C(f^*)}|C_i|$ of Theorem 16.
--
--   **Formalization Note** The paper decomposes $f^*$ in the game expanded into unit-capacity multi-edges, where $f^*$ is binary. Passing back to the original graph, each edge $p$ of $G'$ with $x_p$ units is used by exactly $x_p$ cycle passages, one per unit copy, which is the counting condition above; no expanded graph is built. Cycles are lists of edges, nodes of $G'$ are `Option V` with `none` the node $s$. The binder `[DecidableEq E]` is needed only to count occurrences of an edge in a list.
-- source:
--   arXiv:1908.01714v3, §4.2, p. 30 (decomposition C(f*) and the parameter d, above Theorem 16); §3.1, p. 17 (circulation network G′)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongPoA_Model

namespace FlowAllocGames.StrongPoA

/-- The edges of the circulation network `G′` (arXiv:1908.01714v3, §3.1, p. 17): `inl e` is an edge
`e` of `G`, `inr (inl v)` the auxiliary edge `(v, s)`, and `inr (inr v)` the auxiliary edge `(s, v)`.
The nodes of `G′` are `Option V`, with `none` the auxiliary node `s`. -/
abbrev ExtEdge (V E : Type*) := E ⊕ (V ⊕ V)

/-- The value of a flow of `G′` on an edge of `G′`. -/
def ExtFlow.val {V E : Type*} (x : ExtFlow V E) : ExtEdge V E → ℕ
  | .inl e => x.g e
  | .inr (.inl v) => x.toS v
  | .inr (.inr v) => x.fromS v

namespace Game

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : Game V E)

/-- The tail of an edge of `G′` (`none` is the auxiliary node `s`). -/
def extTail : ExtEdge V E → Option V
  | .inl e => some (G.tail e)
  | .inr (.inl v) => some v
  | .inr (.inr _) => none

/-- The head of an edge of `G′` (`none` is the auxiliary node `s`). -/
def extHead : ExtEdge V E → Option V
  | .inl e => some (G.head e)
  | .inr (.inl _) => none
  | .inr (.inr v) => some v

/-- A (simple, directed) cycle of `G′`, given as the list of its edges: non-empty, each edge starts
where the previous one ends, the last edge ends where the first starts, and no node is left twice.
Its size `|C|` (p. 30) is `C.length`. -/
def IsExtCycle (C : List (ExtEdge V E)) : Prop :=
  C ≠ [] ∧ C.IsChain (fun p q => G.extHead p = G.extTail q) ∧
    (∀ h : C ≠ [], G.extHead (C.getLast h) = G.extTail (C.head h)) ∧ (C.map G.extTail).Nodup

/-- `C(f*)` (p. 30): `Cs` is a decomposition of the integral flow `x` of `G′` into cycles of unit
flow, i.e. a list of cycles of `G′` in which every edge `p` of `G′` occurs, counted with
multiplicity over all cycles, exactly `x_p` times. -/
def IsUnitCycleDecomposition (x : ExtFlow V E) (Cs : List (List (ExtEdge V E))) : Prop :=
  (∀ C ∈ Cs, G.IsExtCycle C) ∧ ∀ p, x.val p = (Cs.map (fun C => C.count p)).sum

end Game

end FlowAllocGames.StrongPoA


