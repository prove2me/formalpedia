-- Prove2me | Definitions.Def_LovaszECCKernel_dist2Pairs
-- name    : LovaszECCKernel_dist2Pairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:30.604695+00:00
-- url     : https://prove2.me/theorems/0d59ad51-1618-42cd-8066-4860b1ff6edd
-- title:
--   Pairs at distance exactly two
-- statement:
--   For a graph $G$, the set of **pairs at distance two** is
--   $$\Bigl\{\{u,v\}\in\tbinom{V(G)}{2} : \mathrm{dist}_G(u,v)=2\Bigr\},$$
--   the non-adjacent pairs with a common neighbour. A graph is a cluster graph iff this set is empty; Lemma 2 bounds the distance to a cluster graph by three times its size.
--
--   **Formalization Note** Mathlib's `SimpleGraph.dist`, which is $0$ for unreachable pairs, so the condition $\mathrm{dist}=2$ is exactly "distinct, non-adjacent, with a common neighbour".
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 2, p.21 (= PDF p.21)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The set of **pairs at distance exactly two** (Fomin, Golovach, Khargeliia, Sagunov, Simonov,
*Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa
Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 2, p.21 (= PDF p.21)):
"pairs {u, v} ∈ (V(G) choose 2) with dist_G(u, v) = 2", where "dist_G(u, v) denotes the number of
edges in the shortest (u, v)-path in the graph G".

**Formalization Note** Unordered pairs `s(u, v)` with `G.dist u v = 2` (Mathlib's
`SimpleGraph.dist`, which is `0` for unreachable pairs, so "`= 2`" means exactly: non-adjacent,
distinct, with a common neighbour). -/
noncomputable def dist2Pairs {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => ∃ u v : V, e = s(u, v) ∧ G.dist u v = 2)

end LovaszECCKernel


