-- Prove2me | Definitions.Def_SPFacilityGraph_Selector_eval
-- name    : SPFacilityGraph_Selector_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:58:25.509211+00:00
-- url     : https://prove2.me/theorems/ff295e34-3bd8-44c8-a234-c16354b1693a
-- title:
--   Outcome of a selector: $\pi_i(\boldsymbol x) = x_i$, $\kappa_w(\boldsymbol x) = w$
-- statement:
--   The outcome of a selector of $\Pi(W)$ at a profile $\boldsymbol x \in G^n$:
--   $$
--   \pi_i(\boldsymbol x) = x_i, \qquad \kappa_w(\boldsymbol x) = w .
--   $$
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.5, table of reference mechanisms and (2.7), p.5

import Mathlib
import Definitions.Def_SPFacilityGraph_Selector

set_option autoImplicit false

namespace SPFacilityGraph

/-- The outcome of a selector of `Π(W)` at a profile (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.5, table and (2.7),
p.5): `πᵢ(𝒙) = xᵢ` and `κ_w(𝒙) = w`. -/
def Selector.eval {k n : ℕ} {G : MetricGraph k} {W : Finset G.Pt} :
    Selector G n W → Profile G n → G.Pt
  | .report i, x => x i
  | .const w _, _ => w

end SPFacilityGraph


