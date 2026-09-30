-- Prove2me | Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
-- name    : VeinottWagnerSS_RenewalCost_Demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:54:18.931068+00:00
-- url     : https://prove2.me/theorems/e769b173-c8bb-43d2-b010-4fe2d6dcf242
-- title:
--   Discrete i.i.d. demand distribution $\varphi$, its convolution powers $\varphi^i$ and their distribution functions $\Phi^i$
-- statement:
--   Following Veinott and Wagner (1965), the demands $\xi_1, \xi_2, \dots$ for a single item in periods $1, 2, \dots$ are independent, non-negative, integer-valued random variables with common probability distribution $\varphi$,
--   $$\varphi(k) = \Pr(\xi_t = k), \qquad k = 0, 1, \dots$$
--   A **demand distribution** is therefore a function $\varphi : \mathbb N \to \mathbb R$ with $\varphi(k) \ge 0$ for all $k$ and $\sum_{k \ge 0} \varphi(k) = 1$.
--
--   For any $\varphi : \mathbb N \to \mathbb R$ the **$i$-fold convolution** $\varphi^i$ is defined recursively by
--   $$\varphi^0(k) = \begin{cases} 1 & k = 0 \\ 0 & k > 0 \end{cases}, \qquad \varphi^{i+1}(k) = \sum_{j=0}^{k} \varphi(k-j)\,\varphi^i(j),$$
--   and its distribution function is
--   $$\Phi^i(k) = \sum_{t=0}^{k} \varphi^i(t).$$
--   For a demand distribution, $\varphi^i(k) = \Pr(\xi_1 + \dots + \xi_i = k)$ and $\Phi^i(k) = \Pr(\xi_1 + \dots + \xi_i \le k)$; in particular $\Phi^0 \equiv 1$, as the paper stipulates.
--
--   These objects underlie every renewal quantity of the paper: the discount renewal function $M_\alpha$, the discounted holding–penalty cost $L_\alpha$ and the discounted set-up factor $r_\alpha$.
--
--   **Formalization Note** The distribution is a real-valued function with a `HasSum φ 1` field rather than a Mathlib `PMF`, so that all costs are real numbers. `convPow φ i k` is $\varphi^i(k)$ and `cdfPow φ i k` is $\Phi^i(k)$; both are defined for an arbitrary $\varphi : \mathbb N \to \mathbb R$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 526 (demand distribution), p. 528 (convolutions φⁿ, Φⁿ), p. 533 (Φ⁰ ≡ 1)

import Mathlib

namespace VeinottWagnerSS.RenewalCost

/-- The one-period demand distribution of Veinott & Wagner (1965), p. 526: the demands
`ξ₁, ξ₂, ⋯` are independent, non-negative, integer-valued random variables with common
probability distribution `φ`, `φ(k) = Pr(ξ_t = k)` for `k = 0, 1, ⋯`. -/
structure DemandDist where
  /-- `φ k = Pr(ξ_t = k)`. -/
  φ : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ φ k
  hasSum : HasSum φ 1

/-- The `i`-fold convolution `φⁱ` of a function `φ : ℕ → ℝ` (p. 528). `φ⁰` is the point mass at
`0` (so that `Φ⁰ ≡ 1`, p. 533), and `φ^{i+1}(k) = ∑_{j=0}^{k} φ(k - j) φⁱ(j)`. For a demand
distribution, `φⁱ(k) = Pr(ξ₁ + ⋯ + ξᵢ = k)`. -/
def convPow (φ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | i + 1 => fun k => ∑ j ∈ Finset.range (k + 1), φ (k - j) * convPow φ i j

/-- `Φⁱ(k) = ∑_{t=0}^{k} φⁱ(t)` (p. 528), the distribution function of the `i`-fold convolution;
`Φ⁰ ≡ 1` (p. 533). For a demand distribution, `Φⁱ(k) = Pr(ξ₁ + ⋯ + ξᵢ ≤ k)`. -/
def cdfPow (φ : ℕ → ℝ) (i k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (k + 1), convPow φ i t

end VeinottWagnerSS.RenewalCost


