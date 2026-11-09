-- Prove2me | Definitions.Def_SPFacilityGraph_IsSSP
-- name    : SPFacilityGraph_IsSSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:59:44.775507+00:00
-- url     : https://prove2.me/theorems/5d8cbf57-393a-4dbb-aff1-1433cf614581
-- title:
--   Strong strategyproofness (SSP), Definition 4.4
-- statement:
--   A deterministic mechanism $M : G^n \to G$ is **strongly strategyproof** (SSP) if its cost function $C_M(\boldsymbol x, t) = d_G(M(\boldsymbol x), t)$ satisfies the constraints of Definition 4.4: for every agent $i$, true location $t$, other reports $\boldsymbol x_{-i}$ and reports $y, z$ with $d_G(t, z) = d_G(t, y) + d_G(y, z)$,
--   $$
--   d_G\big(M(z, \boldsymbol x_{-i}), t\big) \ge d_G\big(M(y, \boldsymbol x_{-i}), t\big).
--   $$
--   SSP implies SP (take $y = t$).
--
--   **Formalization Note** A point is identified with its point mass, so the cost of a deterministic outcome is its graph distance.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 4.4, p.11

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSSPCost

set_option autoImplicit false

namespace SPFacilityGraph

/-- Strong strategyproofness (SSP) of a deterministic mechanism `M : Gⁿ → G` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049),
Definition 4.4, p.11): the constraints (4.4) for its cost function
`C_M(𝒙, t) = cost(M(𝒙), t) = d_G(M(𝒙), t)` ((3.3), p.8).

**Formalization Note** As for `IsSP`, a point is identified with its point mass, so the cost of
a deterministic outcome is the graph distance. -/
def IsSSP {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt) : Prop :=
  IsSSPCost G (fun x t => G.dist (M x) t)

end SPFacilityGraph


