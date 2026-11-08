-- Prove2me | Definitions.Def_GraphNNSphere_Contains
-- name    : GraphNNSphere_Contains
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:12.566236+00:00
-- url     : https://prove2.me/theorems/62406c94-315e-4955-9abf-ebad57412070
-- title:
--   Graph containment
-- statement:
--   A graph $G$ contains a graph $H$ if $H(x)\subseteq G(x)$ for every data point $x$. The upper bound of the mission applies to every graph that contains a threshold graph $G_r$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §3, p.19

import Mathlib
import Definitions.Def_GraphNNSphere_NavGraph

namespace GraphNNSphere

/-- `G` contains `H` if `H(x) ⊆ G(x)` for every `x ∈ D_n` (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §3, p.19). -/
def Contains {n : ℕ} (G H : NavGraph n) : Prop := ∀ i, H i ⊆ G i

end GraphNNSphere


