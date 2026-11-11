-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_DeletionDistance
-- name    : StreamTesting_Bipartiteness_DeletionDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:13.801814+00:00
-- url     : https://prove2.me/theorems/55a96a1e-6466-45f2-bada-4b307eccb0a7
-- title:
--   Minimum edge deletions to bipartiteness
-- statement:
--   For a finite simple graph $G=(V,E)$, define
--
--   $$\operatorname{del}_{\mathrm{BIP}}(G)=\min\{|E\setminus E(K)|:K\subseteq G,\ K\text{ bipartite},\ V(K)=V\}.$$
--
--   The minimum is finite and attained, since the edgeless graph is a feasible target. Edge additions cannot reduce the number of original edges that must be removed. Deletion preserves any maximum-degree bound.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §4, printed p.19 / PDF p.19.

import Definitions.Def_StreamTesting_Bipartiteness_Bipartite

noncomputable section

namespace StreamTesting.Bipartiteness

/-- The minimum number of original edges deleted to make the graph bipartite.
The empty target always witnesses feasibility. Natural-number infimum is attained. -/
def deletionDistance {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact sInf {k | ∃ K : SimpleGraph V, K ≤ G ∧ Bipartite K ∧
    k = (G.edgeFinset \ K.edgeFinset).card}

end StreamTesting.Bipartiteness


