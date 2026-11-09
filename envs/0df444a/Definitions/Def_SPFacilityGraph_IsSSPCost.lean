-- Prove2me | Definitions.Def_SPFacilityGraph_IsSSPCost
-- name    : SPFacilityGraph_IsSSPCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:57.755391+00:00
-- url     : https://prove2.me/theorems/dbc7afce-1823-492a-897a-29f893f91f0b
-- title:
--   Strong-strategyproofness constraints (4.4) for a cost function
-- statement:
--   Let $C(\boldsymbol x, t)$ be a cost function on $G^n \times G$: the cost, at true location $t$, of the outcome at the reported profile $\boldsymbol x$ (for a mechanism $M$ this is $C_M(\boldsymbol x, t) = \mathrm{cost}(M(\boldsymbol x), t)$, (3.3)). $C$ satisfies the **strong-strategyproofness constraints** if for every agent $i$, true location $t$, other reports $\boldsymbol x_{-i}$ and reports $y, z$ with
--   $$
--   d_G(t, z) = d_G(t, y) + d_G(y, z),
--   $$
--   that is, $z$ lies beyond $y$ on a shortest path from $t$, one has
--   $$
--   C\big((z, \boldsymbol x_{-i}), t\big) - C\big((y, \boldsymbol x_{-i}), t\big) \ge 0 .
--   $$
--   Cost cannot decrease as a report moves outward from the truth along a shortest path. Taking $y = t$ gives the SP constraints.
--
--   **Formalization Note** The other reports are given as a full profile whose $i$-th entry is overwritten. The constraints are stated on an arbitrary cost function so that the locality theorem can be stated for every $C_M$.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 4.4, (4.4), p.11; C_M, (3.3), p.8

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist
import Definitions.Def_SPFacilityGraph_Profile

set_option autoImplicit false

namespace SPFacilityGraph

/-- The strong-strategyproofness constraints of Definition 4.4 (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 4.4, (4.4),
p.11), stated for a cost function `C(𝒙, t)` (the expected-cost function `C_M` of (3.3), p.8):
for every agent `i`, true location `t`, other reports `𝒙₋ᵢ` and reports `y, z` with
`d_G(t, z) = d_G(t, y) + d_G(y, z)`, `C((z, 𝒙₋ᵢ), t) − C((y, 𝒙₋ᵢ), t) ≥ 0`.

**Formalization Note** The other-report profile `𝒙₋ᵢ` is a full profile `x` whose `i`-th entry
is overwritten by `Function.update`, so it plays no role. The difference `≥ 0` is written as
`≤`. Stating the constraints on an arbitrary `C` lets Theorem 4.5 be stated for every `C_M`. -/
def IsSSPCost {k n : ℕ} (G : MetricGraph k) (C : Profile G n → G.Pt → ℝ) : Prop :=
  ∀ (i : Fin n) (t : G.Pt) (x : Profile G n) (y z : G.Pt),
    G.dist t z = G.dist t y + G.dist y z →
      C (Function.update x i y) t ≤ C (Function.update x i z) t

end SPFacilityGraph


