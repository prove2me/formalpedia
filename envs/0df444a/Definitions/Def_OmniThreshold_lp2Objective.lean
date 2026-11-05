-- Prove2me | Definitions.Def_OmniThreshold_lp2Objective
-- name    : OmniThreshold_lp2Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:06.051368+00:00
-- url     : https://prove2.me/theorems/e325bcc6-5abd-4113-b78a-7e0ee4b048cb
-- title:
--   Objective of LP (2), the fulfillment cost
-- statement:
--   The **objective of LP (2)** is the fulfillment cost
--   $$
--   \sum_{i=1}^n\Bigl(c_iC_i+\sum_{j=1}^ns_{ji}F_{ji}\Bigr),
--   $$
--   which is the objective of LP (1) with the missed-sales term removed. Here $c_i$ is the cost of cancelling an order at location $i$, and $s_{ji}$ is the unit shipping cost from $j$ to $i$.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, LP (2), p.9

import Mathlib

namespace OmniThreshold

/-- The **objective of LP (2)**, the second-stage problem without the missed-sales term (Jia,
Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*,
SSRN 3932692, LP (2), p.9): `∑_i ( c_i C_i + ∑_j s_ji F_ji )`.

**Formalization Note** `x = (C, R, F)` as in `IsFeasible`; `s j i` is the unit shipping cost from
`j` to `i` and `F j i` the number of orders at `i` filled from `j`. -/
def lp2Objective {n : ℕ} (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ)
    (x : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : ℝ :=
  ∑ i, (c i * x.1 i + ∑ j, s j i * x.2.2 j i)

end OmniThreshold


