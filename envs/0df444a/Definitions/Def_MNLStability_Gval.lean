-- Prove2me | Definitions.Def_MNLStability_Gval
-- name    : MNLStability_Gval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:05.480111+00:00
-- url     : https://prove2.me/theorems/20a52fee-e746-4a8a-808a-829afcde1875
-- title:
--   The separable surrogate $G(U)$ of the DP-amenable regime
-- statement:
--   When every product weight is negligible against $w_0$, each product sells as if offered alone, with purchase probability $p_i=w_i/w_0$ per customer while in stock. Define
--
--   $$\mathbb E\bigl[\min(u,\mathrm{Bin}(m,p))\bigr]=\sum_{k=0}^{m}\binom mk p^k(1-p)^{m-k}\min(u,k),$$
--
--   and
--
--   $$G(U)=\sum_{i}r_i\sum_m p_M(m)\,\mathbb E\bigl[\min(U_i,\mathrm{Bin}(m,w_i/w_0))\bigr].$$
--
--   $G$ is separable over products, so it can be maximized under the capacity constraint by a knapsack recursion.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.3, p.13 (the DP-amenable regime)

import Mathlib
import Definitions.Def_MNLStability_Weights

namespace MNLStability

variable {n : ℕ}

/-- `E[min(u, Bin(m, p))]`, the expected number of units sold from `u` units when each of `m`
customers buys independently with probability `p`. -/
noncomputable def binMinExp (p : ℝ) (m u : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (min u k : ℕ)

/-- The separable surrogate of the expected revenue in the DP-amenable regime (SSRN:3498325, §2.3,
p.13): each product is sold as if it were offered by itself, with purchase probability
`p_i = w_i / w₀` per customer, `G(U) = Σ_i r_i · E[min(U_i, Bin(M, w_i/w₀))]`. -/
noncomputable def Gval (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) : ℝ :=
  ∑ i, r i * ∑ m ∈ pM.support, pM m * binMinExp (wts.w i / wts.w0) m (U i)

end MNLStability


