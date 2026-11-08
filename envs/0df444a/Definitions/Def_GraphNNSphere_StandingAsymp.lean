-- Prove2me | Definitions.Def_GraphNNSphere_StandingAsymp
-- name    : GraphNNSphere_StandingAsymp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:12.131974+00:00
-- url     : https://prove2.me/theorems/1a0c1feb-3c4f-44c1-9360-b3a187ce6bf8
-- title:
--   Standing asymptotic assumptions
-- statement:
--   The assumptions under which the asymptotic bounds of the paper are stated: $d\to\infty$, $d=O(\log n)$ and $\log n=o(d^2)$. Both regimes satisfy them.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.1, p.14

import Mathlib

open Filter Asymptotics

namespace GraphNNSphere

/-- The standing assumptions for the asymptotic bounds, `d → ∞`, `d = O(log n)` and
`log n = o(d²)` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027
submission (manuscript sha256 93565bc5…), §2.1, p.14). -/
def StandingAsymp (d : ℕ → ℕ) : Prop :=
  Tendsto d atTop atTop ∧
    (fun n : ℕ => (d n : ℝ)) =O[atTop] (fun n : ℕ => Real.log (n : ℝ)) ∧
    (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (d n : ℝ) ^ 2)

end GraphNNSphere


