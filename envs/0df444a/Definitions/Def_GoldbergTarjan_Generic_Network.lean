-- Prove2me | Definitions.Def_GoldbergTarjan_Generic_Network
-- name    : GoldbergTarjan_Generic_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:21:38.113305+00:00
-- url     : https://prove2.me/theorems/c554d0db-61cd-44a8-8879-3e722a79899a
-- title:
--   Flow network: capacities $c(v,w) \ge 0$ on all vertex pairs, positive exactly on the edges, no loops, source $s \ne$ sink $t$
-- statement:
--   A **flow network** in the sense of Goldberg and Tarjan consists of a finite vertex set $V$, two distinguished vertices, a **source** $s$ and a **sink** $t$ with $s \ne t$, and a real-valued **capacity** $c(v,w)$ defined on every ordered pair of vertices. The capacity is positive exactly on the edges of the underlying directed graph and zero on every other pair, so
--
--   $$c(v,w) \ge 0 \quad\text{for all } v,w \in V, \qquad E = \{(v,w) \in V \times V : c(v,w) > 0\}.$$
--
--   The graph has no loops: $c(v,v) = 0$ for every $v$. We write $n = |V|$ for the number of vertices and $m = |E|$ for the number of (directed) edges.
--
--   This is the model on which the generic push-relabel algorithm and all bounds of the mission are stated; the edge count $m$ enters the bounds on saturating and nonsaturating pushes.
--
--   **Formalization Note.** The vertex set is a type `V` (finite wherever the size is used, $n$ = `Fintype.card V`). The paper describes a directed graph $G=(V,E)$ with positive capacities on $E$ extended by $0$ to all pairs; here the capacity function on all pairs is primary and $E$ is recovered as its support (`Network.edges`), with $m$ = `Network.numEdges`. The no-loop condition is added because with a loop at $s$ the initialization of Fig. 2 would not be antisymmetric.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 923, §2 (definition of flow network and capacity)

import Mathlib

namespace GoldbergTarjan.Generic

/-- A flow network (Goldberg–Tarjan 1988, §2, p. 923). The vertex set is the type `V`
(finite in every use, `n = Fintype.card V`). The capacity function `c` is defined on all
vertex pairs: it is positive exactly on the edges and `0` on non-edges (the paper's
"We extend the capacity function to all vertex pairs by defining `c(v, w) = 0` if
`(v, w) ∉ E`"), so `c ≥ 0` everywhere. The graph has no loops (`c v v = 0`).
`s` is the source and `t` the sink, and they are distinct. -/
structure Network (V : Type) where
  /-- capacity `c(v, w)` of the vertex pair `(v, w)` -/
  c : V → V → ℝ
  /-- the source -/
  s : V
  /-- the sink -/
  t : V
  cap_nonneg : ∀ v w, 0 ≤ c v w
  cap_self : ∀ v, c v v = 0
  source_ne_sink : s ≠ t

variable {V : Type} [Fintype V]

/-- The edge set `E = {(v, w) | c(v, w) > 0}` of the network. -/
noncomputable def Network.edges (N : Network V) : Finset (V × V) :=
  Finset.univ.filter (fun p => 0 < N.c p.1 p.2)

/-- `m = |E|`, the number of (directed) edges. -/
noncomputable def Network.numEdges (N : Network V) : ℕ :=
  N.edges.card

end GoldbergTarjan.Generic


