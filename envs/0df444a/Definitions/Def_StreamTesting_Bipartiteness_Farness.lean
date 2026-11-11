-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Farness
-- name    : StreamTesting_Bipartiteness_Farness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:08.816325+00:00
-- url     : https://prove2.me/theorems/5e64f394-39a4-45ea-ae5b-11376c359373
-- title:
--   Degree-normalized bipartiteness farness
-- statement:
--   For a finite graph $G$ and parameters $d\in\mathbb N$, $\varepsilon\in\mathbb R$, the farness predicate is
--
--   $$\operatorname{del}_{\mathrm{BIP}}(G)\ge\varepsilon d|V(G)|.$$
--
--   The testing statements separately require maximum degree at most $d$ and a positive farness parameter. This predicate retains the source’s non-strict threshold and its degree normalization.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2 and §4, printed p.4 / PDF p.4.

import Definitions.Def_StreamTesting_Bipartiteness_DeletionDistance

noncomputable section

namespace StreamTesting.Bipartiteness

/-- At least ε d |V| original edges must be deleted (§1.2 and §4). -/
def Far {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) (ε : ℝ) : Prop :=
  ε * (d : ℝ) * (Fintype.card V : ℝ) ≤ (deletionDistance G : ℝ)

end StreamTesting.Bipartiteness


