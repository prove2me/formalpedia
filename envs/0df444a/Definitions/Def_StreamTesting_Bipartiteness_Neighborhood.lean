-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Neighborhood
-- name    : StreamTesting_Bipartiteness_Neighborhood
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:25.172206+00:00
-- url     : https://prove2.me/theorems/b649ab4c-b36c-4c86-9488-b14adcfb4ecf
-- title:
--   Full unordered graph neighborhoods
-- statement:
--   For a finite simple undirected graph $G=(V,E)$, the neighborhood of $v$ is the unordered finite set $N_G(v)=\{u:uv\in E\}$. A stream query returns this whole set, with no port ordering or additional hidden coordinates.
--
--   The degree upper bound uses the compatible published GreedyColoringLCA969 maximum-degree predicate on labeled graphs.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1 and §1.2, printed p.3 / PDF p.3.

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Full unordered neighbor-label sets; §1.2, pp.3–4. -/
def neighbors {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

end StreamTesting.Bipartiteness


