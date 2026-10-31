-- Prove2me | Definitions.Def_ReservationPolicy_Params_Valid
-- name    : ReservationPolicy_Params_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:54.808064+00:00
-- url     : https://prove2.me/theorems/bd6f726a-d1f7-4918-b692-d45a3e9dce95
-- title:
--   Standing assumptions on $(k,\phi,\alpha,z,\kappa)$
-- statement:
--   The paper assumes $k>\tfrac14$, $\phi\in(0,1)$, $\alpha\in(0,1)$, $\kappa>0$, and that the capacity satisfies
--   $$
--   \frac{4k\alpha(1-\phi^2)}{(8k-1)(4k-\phi^2)}<z<\frac12 .
--   $$
--   This domain is the one on which the equilibrium admission probabilities of the investing equilibrium lie strictly between $0$ and $1$.
--
--   **Formalization Note** The paper states the interval as equivalent to the restriction $d\in(0,1)$ on the cutoff (p.9). The two are not equivalent: at $k=1,\phi=\tfrac12,\alpha=\tfrac12,z=\tfrac7{100}$ the interval holds and $d^*=\tfrac{3427}{3300}>1$. The interval is used here, since it is the hypothesis of the proof of Proposition 1 (p.35) and contains the region $d^*\in(0,1)$. The lower bound implies $z>0$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), pp.8–9

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The standing assumptions of the paper: `k > 1/4` (p.8), `ϕ ∈ (0,1)` (p.8), `α ∈ (0,1)` (p.9),
`κ > 0` (p.8), and `4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2` (p.9). Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), pp.8–9 (PDF 8–9).

**Formalization Note** p.9 calls the `z`-interval equivalent to `d ∈ (0,1)`. It is not: at `k = 1`,
`ϕ = 1/2`, `α = 1/2`, `z = 7/100` the interval holds and `d* = 3427/3300 > 1`. The `z`-interval is
what the proof of Proposition 1 uses (p.35), and it contains the region `d* ∈ (0,1)`, so the
cutoff is not restricted here. The lower bound implies `0 < z`. -/
def Params.Valid (P : Params) : Prop :=
  1 / 4 < P.k ∧ 0 < P.ϕ ∧ P.ϕ < 1 ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.κ ∧
    4 * P.k * P.α * (1 - P.ϕ ^ 2) / ((8 * P.k - 1) * (4 * P.k - P.ϕ ^ 2)) < P.z ∧
    P.z < 1 / 2

end ReservationPolicy


