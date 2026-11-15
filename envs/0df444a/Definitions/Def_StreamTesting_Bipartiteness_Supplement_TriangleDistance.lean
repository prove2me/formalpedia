-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_TriangleDistance
-- name    : StreamTesting_Bipartiteness_Supplement_TriangleDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:53:28.559862+00:00
-- url     : https://prove2.me/theorems/57a3f233-f057-484e-94ed-ce618a5801cb
-- title:
--   Minimum deletions to triangle-freeness
-- statement:
--   For a simple graph $G$ on $n$ labels, let
--
--   $$\operatorname{del}_{\triangle}(G)=\min_{K\subseteq G,\ K\text{ triangle-free}} |E(G)\setminus E(K)|.$$
--
--   The target has the same labels. Unordered edges are counted once, and the empty graph is feasible, so this natural-number minimum is attained. Triangle-freeness is absence of a three-vertex clique. Deletions preserve the maximum-degree bound, and additions cannot help this monotone property. This is the distance used by the triangle tester.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2, printed/PDF p.4; §2, printed/PDF pp.10–11.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

/-- Minimum original unordered-edge deletions; the empty graph is always feasible. -/
def triangleDeletionDistance {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact sInf {k | ∃ K : SimpleGraph (Fin n), K ≤ G ∧ K.CliqueFree 3 ∧
    k = (G.edgeFinset \ K.edgeFinset).card}

end StreamTesting.Bipartiteness.Supplement


