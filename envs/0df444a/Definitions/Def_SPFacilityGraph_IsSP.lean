-- Prove2me | Definitions.Def_SPFacilityGraph_IsSP
-- name    : SPFacilityGraph_IsSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:39.997963+00:00
-- url     : https://prove2.me/theorems/93df5cd0-0788-4004-aeeb-d60c3a5940a1
-- title:
--   Strategyproofness (2.2) of a deterministic mechanism
-- statement:
--   A deterministic mechanism $M : G^n \to G$ is **strategyproof** (SP) if no agent can lower its cost by misreporting, whatever the others report:
--   $$
--   d_G\big(M(\boldsymbol x), x_i\big) \le d_G\big(M(z, \boldsymbol x_{-i}), x_i\big) \qquad \text{for all } \boldsymbol x \in G^n,\ i \in N,\ z \in G .
--   $$
--   Here $x_i$ is agent $i$'s true location and the cost of an outcome is its graph distance from that location.
--
--   **Formalization Note** The paper's mechanisms output lotteries and the cost (2.1) is the expected distance; it identifies a point $y$ with the point mass $\delta_y$, so for a deterministic mechanism the cost of $M(\boldsymbol x)$ at $x$ is $d_G(M(\boldsymbol x), x)$.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.3, (2.2), p.4; cost (2.1), p.4

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist
import Definitions.Def_SPFacilityGraph_Profile

set_option autoImplicit false

namespace SPFacilityGraph

/-- Strategyproofness of a deterministic mechanism `M : Gⁿ → G` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.3, (2.2),
p.4): for all `𝒙 ∈ Gⁿ`, `i ∈ N`, `z ∈ G`,
`cost(M(𝒙), xᵢ) ≤ cost(M(z, 𝒙₋ᵢ), xᵢ)`.

**Formalization Note** The paper identifies a point `y` with the point mass `δ_y` (p.4), so a
deterministic mechanism is a map `Gⁿ → G` and the cost (2.1) of its outcome at `x` is
`d_G(M(𝒙), x)`. `(z, 𝒙₋ᵢ)` is `Function.update x i z`. -/
def IsSP {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt) : Prop :=
  ∀ (x : Profile G n) (i : Fin n) (z : G.Pt),
    G.dist (M x) (x i) ≤ G.dist (M (Function.update x i z)) (x i)

end SPFacilityGraph


