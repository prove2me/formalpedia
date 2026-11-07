-- Prove2me | Definitions.Def_ContractionLemma_Net
-- name    : ContractionLemma_Net
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:23.001193+00:00
-- url     : https://prove2.me/theorems/d3002fb0-eef9-41a3-b219-3c1590443894
-- title:
--   Boolean tensor network $G$ and its contraction $Z(G)$
-- statement:
--   A **network** (Boolean tensor network) is a graph $G$ on vertices $V$ and edges $E$, possibly with multiple edges but without loops, in which every edge carries one bit and every vertex $v$ carries a table $T_v$ reading the bits on its own edges $E(v)$. The values of the tables, the entries of the network, lie in a commutative ring. The **contraction** of $G$ is
--
--   $$
--   Z(G)=\sum_{x\in\{0,1\}^E}\ \prod_{v\in V} T_v\big(x|_{E(v)}\big).
--   $$
--
--   The degree of a vertex counts its incident edges with multiplicity. An isolated vertex has a constant table and contributes a constant factor. Every other object of this mission is built from this one.
--
--   **Formalization Note** Parallel edges are distinct elements of $E$, hence distinct bits. A table is a function of the assignment to the subtype of incident edges, so no ordering of $E(v)$ is needed at this level; the maximum degree of a network without vertices is $0$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §2.1, p.16 and Definition A.1, p.49

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

/-- **Network (Boolean tensor network)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), §2.1, p.16, and Definition A.1, p.49.

A network is a graph, possibly with multiple edges but without loops: `ends e` is the pair of
endpoints of the edge `e`, and `loopless` says they are different. Every edge carries one bit,
and every vertex `v` carries a table `table v` that reads the bits on its own edges
`E(v) = {e | v is an endpoint of e}`; its values (the entries) lie in `R`.

**Formalization Note.** Vertices and edges are arbitrary types `V`, `E`; parallel edges are
distinct elements of `E`, hence distinct bits. A table is a function of the assignment to the
subtype of incident edges, so no ordering of `E(v)` is needed here (the machine encodings fix
the increasing edge order). An isolated vertex has the empty subtype and a constant table. -/
structure Net (V E R : Type*) where
  /-- the two endpoints of each edge -/
  ends : E → V × V
  /-- no loops -/
  loopless : ∀ e, (ends e).1 ≠ (ends e).2
  /-- the table of a vertex, reading the bits of its incident edges -/
  table : (v : V) → ({e : E // (ends e).1 = v ∨ (ends e).2 = v} → Bool) → R

namespace Net

variable {V E R : Type*}

/-- The degree of `v`: the number of edges incident to `v`, parallel edges counted with
multiplicity (p.16). -/
def deg [Fintype E] [DecidableEq V] (G : Net V E R) (v : V) : ℕ :=
  (Finset.univ.filter fun e => (G.ends e).1 = v ∨ (G.ends e).2 = v).card

/-- The maximum degree of `G` (`0` when `G` has no vertex). -/
def maxDeg [Fintype V] [Fintype E] [DecidableEq V] (G : Net V E R) : ℕ :=
  Finset.univ.sup G.deg

/-- **The contraction** (§2.1, p.16; Definition A.1, p.49):
`Z(G) = ∑_{x ∈ {0,1}^E} ∏_v T_v(x|_{E(v)})`. -/
def Z [Fintype V] [Fintype E] [DecidableEq E] [CommSemiring R] (G : Net V E R) : R :=
  ∑ x : E → Bool, ∏ v, G.table v (fun e => x e.1)

end Net

end ContractionLemma


