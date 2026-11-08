-- Prove2me | Definitions.Def_GraphNNSphere_cap
-- name    : GraphNNSphere_cap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:18.103485+00:00
-- url     : https://prove2.me/theorems/c9665793-095d-4485-94e6-7cad26159eab
-- title:
--   Closed spherical cap $C(x,\theta)$
-- statement:
--   The closed spherical cap of radius $\theta$ centered at $x$:
--   $$C(x,\theta)=\{y\in S^{d-1}:\delta(x,y)\le\theta\}.$$
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_geo

namespace GraphNNSphere

/-- The closed spherical cap `C(x, θ)` of radius `θ` centered at `x` (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §1.2, p.3). -/
def cap {d : ℕ} (x : Sph d) (θ : ℝ) : Set (Sph d) := {y | geo x y ≤ θ}

end GraphNNSphere


