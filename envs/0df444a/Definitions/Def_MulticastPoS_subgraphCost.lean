-- Prove2me | Definitions.Def_MulticastPoS_subgraphCost
-- name    : MulticastPoS_subgraphCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:50.830779+00:00
-- url     : https://prove2.me/theorems/76f9b4d5-d8b2-47fa-b8b6-caf55979a8a0
-- title:
--   Cost $c(R)$ of a subgraph
-- statement:
--   For a subgraph $R$ of $G$ the **cost** is the total cost of its edges,
--
--   $$
--   c(R)=c(E(R))=\sum_{e\in E(R)} c_e .
--   $$
--
--   In particular $OPT=c(T^\star)$ for the optimal tree $T^\star$.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 2, p.4; Section 4.1, p.8

import Mathlib

namespace MulticastPoS

/-- The cost of a subgraph (Huang–Yuan, *An O(log log n) Upper Bound on the Price of Stability
for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256 dd0e08d0…f6d4),
Section 2, p.4 and Section 4.1, p.8): `c(F) = Σ_{e∈F} c_e` for an edge set `F`, and
`c(R) = c(E(R))` for a subgraph `R`. In particular `OPT = c(T⋆)`. -/
noncomputable def subgraphCost {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (c : Sym2 V → ℝ) (S : G.Subgraph) : ℝ :=
  ∑ e ∈ S.edgeSet.toFinite.toFinset, c e

end MulticastPoS


