-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Bipartite
-- name    : StreamTesting_Bipartiteness_Bipartite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:25.524605+00:00
-- url     : https://prove2.me/theorems/ba1caec1-b8d6-4323-819a-72998b97c716
-- title:
--   Bipartiteness as a proper two-coloring
-- statement:
--   A simple undirected graph $G=(V,E)$ is bipartite precisely when there exists a map $c:V\to\{0,1\}$ such that
--
--   $$uv\in E\implies c(u)\ne c(v).$$
--
--   Disconnected graphs and isolated vertices are allowed. This is the property tested throughout the mission.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2 and §4, printed p.4 / PDF p.4.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness

/-- A proper two-coloring, including disconnected graphs and isolated vertices. -/
def Bipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Bool, ∀ u v, G.Adj u v → c u ≠ c v

end StreamTesting.Bipartiteness


