-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_TriangleFarness
-- name    : StreamTesting_Bipartiteness_Supplement_TriangleFarness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:53:58.147024+00:00
-- url     : https://prove2.me/theorems/151b9148-26c8-4f3c-be13-b2c4098f7482
-- title:
--   Degree-normalized triangle-freeness farness
-- statement:
--   A graph $G$ on $n$ labels is $\varepsilon$-far from triangle-free at degree bound $d$ when
--
--   $$\operatorname{del}_{\triangle}(G)\ge\varepsilon dn.$$
--
--   Testing results separately require maximum degree at most $d$, $d\ge1$, and $0<\varepsilon\le1$. This retains the source's non-strict farness threshold.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2, printed/PDF p.4; §2, printed/PDF pp.10–11.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_TriangleDistance

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def TriangleFar {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (ε : ℝ) : Prop :=
  ε * (d : ℝ) * (n : ℝ) ≤ (triangleDeletionDistance G : ℝ)

end StreamTesting.Bipartiteness.Supplement


