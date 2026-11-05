-- Prove2me | Definitions.Def_OmniThreshold_lp1Objective
-- name    : OmniThreshold_lp1Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:59.654467+00:00
-- url     : https://prove2.me/theorems/b06e5753-6a87-405d-a80a-3c11a988501a
-- title:
--   Objective of the second-stage problem LP (1)
-- statement:
--   With the data and decision of the second-stage problem, a missed-sale penalty $p$, cancellation costs $c_i$ and unit shipping costs $s_{ji}$ from location $j$ to location $i$, the **objective of LP (1)** is
--   $$
--   p\,\min\Bigl(\sum_{i=1}^n\Bigl(\mathcal I_i-\min(\mathcal I_i,\mathcal D_i^P)-\sum_{j=1}^nF_{ij}\Bigr),\ \sum_{i=1}^n(\mathcal D_i^O-A_i^O)\Bigr)+\sum_{i=1}^n\Bigl(c_iC_i+\sum_{j=1}^ns_{ji}F_{ji}\Bigr).
--   $$
--   The first term charges $p$ for every rejected online order that could have been filled. The second term adds the cancellation penalties and the shipping costs.
--
--   **Formalization Note** The minimum is taken of the two sums, as printed. $\mathcal D_i^O$ is the online demand at $i$.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, LP (1), p.3; pp.3–4

import Mathlib

namespace OmniThreshold

/-- The **objective of the second-stage problem LP (1)** (Jia, Karp, Ravi & Tayur, *Effective
Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, LP (1), p.3):
```
p · min( ∑_i (I_i − min(I_i, D_i^P) − ∑_j F_ij), ∑_i (D_i^O − A_i^O) ) + ∑_i ( c_i C_i + ∑_j s_ji F_ji ).
```
The first term charges the penalty `p` for every rejected online order that could have been filled
(p.3–4), `c i` is the cost of cancelling an order at `i`, and `s j i` the unit shipping cost from
location `j` to location `i` (p.4).

**Formalization Note** `x = (C, R, F)` as in `IsFeasible`; `F i j` is the number of orders received
at `j` filled from `i`, so the shipping term is `∑_i ∑_j s j i * F j i`. The `min` is of the two
sums, as printed. Data in `ℕ` are cast to `ℝ`. -/
def lp1Objective {n : ℕ} (p : ℝ) (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ) (I DP DO A : Fin n → ℕ)
    (x : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : ℝ :=
  p * min (∑ i, ((I i : ℝ) - min (I i : ℝ) (DP i : ℝ) - ∑ j, x.2.2 i j))
      (∑ i, ((DO i : ℝ) - (A i : ℝ))) +
    ∑ i, (c i * x.1 i + ∑ j, s j i * x.2.2 j i)

end OmniThreshold


