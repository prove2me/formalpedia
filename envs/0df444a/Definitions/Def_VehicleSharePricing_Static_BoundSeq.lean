-- Prove2me | Definitions.Def_VehicleSharePricing_Static_BoundSeq
-- name    : VehicleSharePricing_Static_BoundSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:42.05305+00:00
-- url     : https://prove2.me/theorems/1ff48646-f36c-4609-be87-6e718519e1a8
-- title:
--   Theorem 2, p. 9 — the bound sequences $B^K_i(q^s)$ and $B^K_i$
-- statement:
--   For a number of locations $N$ and a workload $\rho$, the **bound sequence** of Theorem 2 is defined for $K\ge 0$ and $0\le i\le K$ by
--   $$B_\rho(K,0)=0,\qquad B_\rho(K,i)=\frac{K}{N+K-1+\rho\,\bigl(1-B_\rho(K-1,i-1)\bigr)}\quad(1\le i\le K).$$
--   With $\rho=\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q^s_{ij}/\mu_{ij}$ this is the paper's $B^K_i(q^s)$, and with $\rho=\Lambda/\mu$ it is the paper's $B^K_i$.
--
--   $B^K_i(q^s)$ is obtained by iterating the availability recursion (5) $i$ times, starting from the crude value $0$; $B^K_K(q^s)$ is the availability itself.
--
--   **Formalization Note** The paper sets $B^j_0=0$ for $j=1,\dots,K$, but $B^K_K$ calls $B^0_0$; here $B(K,0)=0$ for every $K\ge 0$, including $K=0$. All arithmetic is in $\mathbb R$. Values with $i>K$ are never used by the mission's statements.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 9, Theorem 2 (definitions of B^K_i(q^s), B^K_i, B^j_0) and p. 10, proof of Theorem 2

import Mathlib

namespace VehicleSharePricing.Static

/-- The bound sequence of Theorem 2, p. 9, for `N` locations and workload `ρ`:
`B(K, 0) = 0` for every `K ≥ 0`, and
`B(K, i) = K / (N + K − 1 + ρ (1 − B(K − 1, i − 1)))` for `i ≥ 1`.
Only the values with `i ≤ K` are used; arithmetic is in `ℝ`. -/
noncomputable def Bseq (N : ℕ) (ρ : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | K, i + 1 => (K : ℝ) / ((N : ℝ) + K - 1 + ρ * (1 - Bseq N ρ (K - 1) i))

end VehicleSharePricing.Static


