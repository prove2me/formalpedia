-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Roots
-- name    : StreamTesting_Bipartiteness_Roots
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:53.476714+00:00
-- url     : https://prove2.me/theorems/6fb2d25a-df4f-4fa9-9d28-49734d4df954
-- title:
--   Lifted roots and counts in projected components
-- statement:
--   A queried label $x$ is a root if it occurs in no earlier returned neighborhood. The root set contains the distinct lifted vertices $\Lambda(x)$, rather than their base projections. For a vertex $v$ of $B$, count the roots $r$ for which $v$ and $\pi(r)$ are connected in $B$.
--
--   Two roots with the same base projection count twice. An isolated component with no roots has count zero, as required for the forest assertion.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §4.3, printed p.23 / PDF p.23.

import Definitions.Def_StreamTesting_Bipartiteness_Projection

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Queried vertices whose labels appeared in no earlier returned neighborhood.
The finite set lives in the lift, so roots with equal base projections remain distinct. -/
def roots {m : ℕ} (Λ : Labeling m) (T : History (2 * m)) : Finset (Fin m × Bool) := by
  classical
  exact Finset.univ.filter fun r => ∃ i x N, T i = some (x, some N) ∧ Λ x = r ∧
    ∀ j, j < i → ∀ y M, T j = some (y, some M) → x ∉ M

/-- Count lifted roots in the B-component of v, using their base projections. -/
def componentRootCount {m : ℕ} (B : SimpleGraph (Fin m)) (R : Finset (Fin m × Bool))
    (v : Fin m) : ℕ := by
  classical
  exact (R.filter fun r => B.Reachable v r.1).card

end StreamTesting.Bipartiteness


