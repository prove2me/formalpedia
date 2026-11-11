-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Lift
-- name    : StreamTesting_Bipartiteness_Lift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:37.285726+00:00
-- url     : https://prove2.me/theorems/e10ab57c-c906-4058-9b62-49736a6a406a
-- title:
--   Two disjoint copies and selection of the hard lift
-- statement:
--   The graph $G_0=H\sqcup H$ has vertices $(u,a)\in V(H)\times\{0,1\}$ and edges exactly when $uv\in E(H)$ and $a=b$. For $s=1$, use the published bipartite double cover, whose edges have $a\ne b$. Thus the selected graph $G_s$ obeys
--
--   $$(u,a)(v,b)\in E(G_s)\iff uv\in E(H)\text{ and }a\oplus b=s.$$
--
--   The copy bit is part of the hidden construction, never a policy input.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §4.1 and Definition 16, printed p.20 / PDF p.20.

import Definitions.Def_QGraphColl_restrict

noncomputable section

namespace StreamTesting.Bipartiteness

/-- G₀ = H ⊔ H; copy coordinates are hidden from the tester (§4.1). -/
def twoCopies {V : Type*} (H : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj u v := H.Adj u.1 v.1 ∧ u.2 = v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.1⟩

/-- False selects G₀; true selects the published bipartite double cover G₁. -/
def liftGraph {V : Type*} (H : SimpleGraph V) (s : Bool) : SimpleGraph (V × Bool) :=
  if s then QGraphColl.doubleCover H else twoCopies H

end StreamTesting.Bipartiteness


