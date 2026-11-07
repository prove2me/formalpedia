-- Prove2me | Definitions.Def_MulticastPoS_IsTreeSupported
-- name    : MulticastPoS_IsTreeSupported
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:37.312673+00:00
-- url     : https://prove2.me/theorems/fb7cb6d9-8716-43a2-ae7f-53330930591a
-- title:
--   Tree-supported profile
-- statement:
--   A path profile $P$ is **tree-supported** if all its paths lie in one tree, that is, the support $\operatorname{supp}(P)=\bigcup_i P_i$ contains no cycle.
--
--   Lemma 2.2 produces a tree-supported global minimizer of the potential, on which the proof of the main theorem works.
--
--   **Formalization Note** The support, viewed as a graph on $V$, is required to be acyclic. For a path profile every nonempty path ends at $t$, so the support is connected and acyclicity is the same as being a tree; an empty support is the degenerate tree $\{t\}$.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 2, p.4; Lemma 2.2, p.5; Appendix A, p.13

import Mathlib

namespace MulticastPoS

/-- A tree-supported profile (Huang–Yuan, *An O(log log n) Upper Bound on the Price of Stability
for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256 dd0e08d0…f6d4),
Section 2, p.4): the support `supp(P) = ⋃ᵢ Pᵢ`, the set of edges used by at least one player,
lies in one tree, i.e. the graph formed by the support edges has no cycle.

**Formalization Note** For a path profile every nonempty path ends at the sink `t`, so the support
is connected and "acyclic" is the same as "is a tree"; an empty support is the degenerate tree
`{t}` of Appendix A, p.13. -/
def IsTreeSupported {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : ι → Finset (Sym2 V)) : Prop :=
  (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion P) : Set (Sym2 V))).IsAcyclic

end MulticastPoS


