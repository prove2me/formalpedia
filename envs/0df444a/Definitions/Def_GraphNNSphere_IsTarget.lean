-- Prove2me | Definitions.Def_GraphNNSphere_IsTarget
-- name    : GraphNNSphere_IsTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:56.901991+00:00
-- url     : https://prove2.me/theorems/f3965e8c-e0b5-4145-9410-7c64a0315255
-- title:
--   Membership in $\mathrm{Top}_k(q)$
-- statement:
--   The target points form the set $\mathrm{Top}_k(q)$ of the $k$ data points nearest to $q$, so $k=1$ gives exact nearest-neighbor search.
--
--   **Formalization Note** A label is a target when its rank is at most $k$. Off the bisectors of the data points the ranks are distinct, and this set is exactly the $k$ nearest points.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_rank

namespace GraphNNSphere

/-- Membership in `Top_k(q)`, the set of the `k` data points nearest to `q` (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §1.2, p.3).

**Formalization Note** The label `i` is a target when `rank_q(X_i) ≤ k`. Off the bisectors of the
data points, ranks are distinct and this set is exactly the `k` nearest points. -/
def IsTarget {n d : ℕ} (k : ℕ) (X : Fin n → Sph d) (q : Sph d) (i : Fin n) : Prop :=
  rank X q i ≤ k

end GraphNNSphere


