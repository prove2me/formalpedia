-- Prove2me | Definitions.Def_VehicleSharePricing_DemandFree_Beta
-- name    : VehicleSharePricing_DemandFree_Beta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:41.838829+00:00
-- url     : https://prove2.me/theorems/7fcbf940-604c-4c17-bb34-d6aebd7495aa
-- title:
--   Proof of Theorem 3, p. 10 — the sequence β(K) = K/(N+K−1+∆(1−β(K−1))), β(0) = 0
-- statement:
--   For a number of locations $N\ge 1$ and a workload $\Delta$, the sequence $\beta(K)=\beta_{N,\Delta}(K)$, $K\in\mathbb N$, is defined by
--
--   $$
--   \beta(0)=0,\qquad \beta(K)=\frac{K}{N+K-1+\Delta\,(1-\beta(K-1))}\quad(K\ge 1).
--   $$
--
--   In the proof of Theorem 3 it is the availability of the same system with the total workload $\Delta$ in the transit queue; it serves as a lower bound for the availability of the static policy.
--
--   **Formalization Note** The recursion is written for $K+1$ in terms of $K$, so no natural-number subtraction occurs; all arithmetic is in $\mathbb R$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 10, proof of Theorem 3

import Mathlib

namespace VehicleSharePricing.DemandFree

/-- The sequence `β(K)` of the proof of Theorem 3 (p. 10), for `N` locations and total workload
`Δ`: `β(0) = 0` and `β(K) = K / (N + K − 1 + Δ (1 − β(K − 1)))` for `K ≥ 1`. -/
noncomputable def beta (N : ℕ) (Δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | K + 1 => ((K : ℝ) + 1) / ((N : ℝ) + ((K : ℝ) + 1) - 1 + Δ * (1 - beta N Δ K))

end VehicleSharePricing.DemandFree


