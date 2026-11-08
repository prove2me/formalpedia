-- Prove2me | Definitions.Def_GraphNNSphere_rank
-- name    : GraphNNSphere_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:11.609158+00:00
-- url     : https://prove2.me/theorems/7a5d7920-9259-4070-a80f-cf3f16d08a96
-- title:
--   Rank $\mathrm{rank}_q(x)$
-- statement:
--   The rank of a data point with respect to a query $q$:
--   $$\mathrm{rank}_q(x)=1+\#\{y\in D_n:\delta(q,y)<\delta(q,x)\}.$$
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.1, p.14

import Mathlib
import Definitions.Def_GraphNNSphere_geo

namespace GraphNNSphere

/-- `rank_q(x) = 1 + #{y ∈ D_n : δ(q, y) < δ(q, x)}` (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.1, p.14). -/
noncomputable def rank {n d : ℕ} (X : Fin n → Sph d) (q : Sph d) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter (fun j => geo q (X j) < geo q (X i))).card

end GraphNNSphere


