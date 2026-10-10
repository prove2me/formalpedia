-- Prove2me | Definitions.Def_PriceQualityService_Oligopoly_PriceRoot
-- name    : PriceQualityService_Oligopoly_PriceRoot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:01.900403+00:00
-- url     : https://prove2.me/theorems/b8b7a1e7-4d80-4807-80f0-35ffef4b5362
-- title:
--   The price root $\varphi_i(A)$ and the aggregate equation of the proof of Theorem 2
-- statement:
--   Fix quality levels $\mathbf q$ and durations $\mathbf t$. For product $i$ let $k_i = c_i q_i^2 + t_i(a_i - b_i q_i)$ be its unit cost and $w_i = \alpha_i q_i + t_i s_i$ its price-free utility, so that its attraction at price $p_i$ is $\exp(w_i - p_i)$.
--
--   For an aggregate $A > 0$, the price $\varphi_i(A)$ is the solution $p$ of the price first-order condition
--   $$
--   1 = (p - k_i)\Big(1 - \frac{\exp(w_i - p)}{A}\Big), \qquad p > k_i,\ \exp(w_i - p) < A .
--   $$
--   The **aggregate equation** is
--   $$
--   \frac1A + \sum_{j \in \mathcal N} \frac{\exp(w_j - \varphi_j(A))}{A} = 1 .
--   $$
--
--   In the proof of Theorem 2 these objects reduce the price competition to a single equation in one unknown, the aggregate $A = 1 + \sum_j \exp(w_j - p_j)$.
--
--   **Formalization Note** $\varphi_i(A)$ is defined as the infimum of the solution set of the condition above; for $A > 0$ that set is a single point (a milestone of the mission), and for $A \le 0$ it is empty and the value is Lean's junk value $0$, which no statement uses at $A \le 0$. The region $p > k_i$, $\exp(w_i - p) < A$ is where the right-hand side increases in $p$; the paper's "the RHS is increasing in $p_i$" holds only there.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 3 (PDF p. 36), proof of Theorem 2

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_Model

namespace PriceQualityService.Oligopoly

open Finset

/-- Unit cost of product `i` at quality `q_i` and duration `t_i`:
`k_i = c_i q_i² + t_i (a_i − b_i q_i)` (Online Supplement p. 3, at `q = q*`, `t = t*`). -/
def unitCost {N : ℕ} (a b c q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  c i * q i ^ 2 + t i * (a i - b i * q i)

/-- Price-free utility of product `i`: `w_i = α_i q_i + t_i s_i`, so that the PriceQualityService.Joint.attraction of
product `i` at price `p_i` is `exp(w_i − p_i)`. -/
def baseUtility {N : ℕ} (α s q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i * q i + t i * s i

/-- `p` solves the price first-order condition of the proof of Theorem 2 (Online Supplement
p. 3) for the aggregate `A`, unit cost `k` and price-free utility `w`:
`1 = (p − k) (1 − exp(w − p) / A)`, on the region `p > k`, `exp(w − p) < A`. The region is the
one on which the right-hand side is increasing in `p`; at an equilibrium
`A = 1 + ∑_j exp(w_j − p_j) > exp(w_i − p_i)`, so the equilibrium prices lie in it. -/
def IsPriceRoot (k w A p : ℝ) : Prop :=
  k < p ∧ Real.exp (w - p) < A ∧ 1 = (p - k) * (1 - Real.exp (w - p) / A)

/-- `φ(A)` of the proof of Theorem 2 (Online Supplement p. 3): the price `p` solving
`IsPriceRoot k w A p`, taken as the infimum of the solution set. For `A > 0` the solution is
unique, so this is that solution; for `A ≤ 0` the set is empty and the value is Lean's junk
value `sInf ∅ = 0`, which no statement of the mission uses. -/
noncomputable def priceRoot (k w A : ℝ) : ℝ :=
  sInf {p : ℝ | IsPriceRoot k w A p}

/-- The aggregate equation of the proof of Theorem 2 (Online Supplement p. 3), for fixed
quality levels `q` and durations `t`:
`1/A + ∑_{j ∈ 𝒩} exp(α_j q_j − φ_j(A) + t_j s_j) / A = 1`,
where `φ_j = priceRoot (k_j) (w_j)` with `k_j` the unit cost and `w_j` the price-free utility. -/
def IsAggregateRoot {N : ℕ} (α a b c s q t : Fin N → ℝ) (A : ℝ) : Prop :=
  1 / A + ∑ j, Real.exp (baseUtility α s q t j -
      priceRoot (unitCost a b c q t j) (baseUtility α s q t j) A) / A = 1

end PriceQualityService.Oligopoly


