-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Network
-- name    : AtomicDynRouting_ResidenceTime_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:01.521422+00:00
-- url     : https://prove2.me/theorems/99d0d4ae-192f-4c3f-980f-0ea75cda545d
-- title:
--   §2.1, §2.3, §3.1, pp. 5, 7 — finite directed multigraph, directed paths, acyclicity, longest path length L_{vw}
-- statement:
--   This file fixes the network of Cao, Chen, Chen and Wang (§2.1). It is a general object, shared by every statement of the mission.
--
--   A **network** $G=(V,E)$ is a directed multigraph: a set $V$ of vertices, a set $E$ of edges, and maps assigning to each edge $e$ its tail and its head. Parallel edges are allowed, because edges form a set of their own rather than a set of vertex pairs.
--
--   A **directed $u$-$w$ path** is a finite sequence of edges $P=(e_1,\dots,e_m)$ with
--   $$\operatorname{tail}(e_1)=u,\qquad \operatorname{head}(e_i)=\operatorname{tail}(e_{i+1})\ (1\le i<m),\qquad \operatorname{head}(e_m)=w;$$
--   the empty sequence is the (trivial) $u$-$u$ path. Every edge has unit length (§2.3), so the length of a path is its number of edges.
--
--   The network is **acyclic** if it has no directed cycle, i.e. the only $v$-$v$ path is the empty one. In an acyclic network every directed walk is a simple path, which matches the paper's convention "All the paths discussed are directed and simple".
--
--   For vertices $v,w$, $L_{vw}$ denotes the length of a longest $v$-$w$ path (§3.1, p. 7).
--
--   **Formalization Note.** `Network V E` stores only `tail` and `head`; finiteness of $V$ and $E$ and acyclicity are hypotheses of every theorem. Paths are edge lists (`IsPathFrom u w P`). `longest v w` is the supremum in $\mathbb N$ of the lengths of $v$-$w$ paths; in a finite acyclic network these lengths are bounded by $|E|$, and every use in the mission is between two vertices joined by a path, so the supremum is a maximum. When no $v$-$w$ path exists the value is the junk $0$; no statement of the mission uses that case.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 5 (PDF 6), §2.1, §2.3; p. 7 (PDF 8), §3.1 (definition of L_{vw})

import Mathlib

namespace AtomicDynRouting.ResidenceTime

/-- A network `G = (V, E)` (Cao–Chen–Chen–Wang, §2.1, p. 5): a directed multigraph whose edge `e`
goes from `tail e` to `head e`. Edges form a type of their own, so parallel edges are allowed.
Finiteness (`Fintype V`, `Fintype E`) is a hypothesis of every theorem that uses the network. -/
structure Network (V E : Type) where
  tail : E → V
  head : E → V

namespace Network

variable {V E : Type} (N : Network V E)

/-- `N.IsPathFrom u w P`: the edge list `P = [e₁, …, eₘ]` is a directed `u`-`w` path, i.e.
`tail e₁ = u`, `head eᵢ = tail eᵢ₊₁` and `head eₘ = w`. The empty list is the `u`-`u` path.
In an acyclic network every such walk is simple (§2.1: "All the paths discussed are directed and
simple"). -/
def IsPathFrom : V → V → List E → Prop
  | u, w, [] => u = w
  | u, w, e :: P => N.tail e = u ∧ IsPathFrom (N.head e) w P

/-- The network is acyclic (§2.1): it has no directed cycle, i.e. the only closed walk is the empty
one. -/
def Acyclic : Prop := ∀ (v : V) (P : List E), N.IsPathFrom v v P → P = []

/-- `L_{vw}` (§3.1, p. 7): the length (number of edges, unit lengths, §2.3) of a longest `v`-`w`
path. In a finite acyclic network the lengths are bounded by `Fintype.card E`; the value is the
junk `0` when no `v`-`w` path exists. -/
noncomputable def longest (v w : V) : ℕ :=
  sSup {n : ℕ | ∃ P : List E, N.IsPathFrom v w P ∧ P.length = n}

end Network

end AtomicDynRouting.ResidenceTime


