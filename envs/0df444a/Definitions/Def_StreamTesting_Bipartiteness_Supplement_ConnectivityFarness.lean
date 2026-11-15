-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_ConnectivityFarness
-- name    : StreamTesting_Bipartiteness_Supplement_ConnectivityFarness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:54:28.308609+00:00
-- url     : https://prove2.me/theorems/b4f2bf4c-9e9b-411e-93e8-44c0520d7b0c
-- title:
--   Connectivity farness with degree-preserving edge edits
-- statement:
--   Let $G$ have $n$ labels and degree bound $d$. Connectivity farness means that every connected simple graph $K$ on the same labels, with maximum degree at most $d$, satisfies
--
--   $$|E(G)\mathbin{\triangle}E(K)|\ge\varepsilon dn.$$
--
--   Both edge insertions and deletions count, with each unordered edge counted once. If no connected target of degree at most $d$ exists, the universal condition holds, representing infinite edit distance rather than zero. This includes the degree-one regime at more than two labels.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2, printed/PDF p.4; §3, printed/PDF pp.12–15.

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

/-- Universal form of edit distance, including an empty connected target family. -/
def ConnectivityFar {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (ε : ℝ) : Prop := by
  classical
  exact ∀ K : SimpleGraph (Fin n), K.Connected →
    GreedyColoringLCA969.LowerBound.MaxDegreeAtMost K d →
    ε * (d : ℝ) * (n : ℝ) ≤
      (((G.edgeFinset \ K.edgeFinset) ∪ (K.edgeFinset \ G.edgeFinset)).card : ℝ)

end StreamTesting.Bipartiteness.Supplement


