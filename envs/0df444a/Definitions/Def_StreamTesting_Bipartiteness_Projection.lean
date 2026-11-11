-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Projection
-- name    : StreamTesting_Bipartiteness_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:51.734131+00:00
-- url     : https://prove2.me/theorems/1524a9c0-1821-4476-ba2f-81a83886e8e9
-- title:
--   Revealed edges and their projection onto the base graph
-- statement:
--   The revealed graph on observed labels contains precisely all undirected edges appearing in a returned neighborhood. Apply $\Lambda$ to both endpoints and forget their copy bits to obtain the projection $B=\pi(T_\Lambda)$ on the entire vertex set of $H$.
--
--   Repeated projected edges merge and isolated vertices remain. This object is computed from the actual transcript and labeling, not supplied as an independent graph or certificate.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §4.1–4.2, printed p.21 / PDF p.21.

import Definitions.Def_StreamTesting_Bipartiteness_InputDistribution

noncomputable section

namespace StreamTesting.Bipartiteness

/-- All and only undirected edges actually returned in this transcript. -/
def revealed {n : ℕ} (T : History n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ i x N y, T i = some (x, some N) ∧ y ∈ N ∧ e = s(x,y)}

/-- Project every revealed edge after undoing its labeling. The vertex set is all
of V(H), retaining isolated vertices and merging duplicate projected edges. -/
def projection {m : ℕ} (Λ : Labeling m) (T : History (2 * m)) : SimpleGraph (Fin m) :=
  SimpleGraph.fromEdgeSet {e | ∃ x y, (revealed T).Adj x y ∧ e = s((Λ x).1, (Λ y).1)}

end StreamTesting.Bipartiteness


