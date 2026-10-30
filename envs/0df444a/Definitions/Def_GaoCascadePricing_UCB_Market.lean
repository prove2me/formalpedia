-- Prove2me | Definitions.Def_GaoCascadePricing_UCB_Market
-- name    : GaoCascadePricing_UCB_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:13:39.915992+00:00
-- url     : https://prove2.me/theorems/c9aa2f4a-0eba-431d-8a5b-a42de174f439
-- title:
--   Finite prices, cascade revenue and regret coefficient
-- statement:
--   There are positive finite numbers $J$ and $K$ of products and prices. A market supplies strictly increasing nonnegative real prices $q_1<\cdots<q_K$. All $K^J$ price vectors are feasible, with the product ranking fixed. This adds monetary rewards to the separately defined general cascade.
--
--   For a vector $p$, its maximum price magnitude is $\|p\|_\infty$, and its expected revenue is
--   $$\rho(p;\theta)=\sum_{j=1}^J\Bigl(\prod_{i<j}\mu_i(p_i;\theta)\Bigr)\beta_{j,k(j,p)}\alpha_{j,k(j,p)}p_j.$$
--   This is the expansion of the backward recursion with terminal revenue zero. The optimal revenue is the maximum over all feasible price vectors. The maximum price is $q_K$. Define $\underline\beta=\min_{j,k}\beta_{j,k}$, $\overline\beta=\max_{j,k}\beta_{j,k}$ and $\overline\alpha=\max_{j,k}\alpha_{j,k}$, and the coefficient
--   $$\min\{1/\underline\beta,\;1/(1-\overline\beta),\;1/[\underline\beta(1-\overline\alpha)]\}.$$
--
--   **Formalization Note.** Suprema and infima are over nonempty finite sets whenever a positive market is supplied. Nonnegative prices are the standing economic convention. The coefficient uses extended nonnegative reals, so a reciprocal of zero is infinity, and zero times infinity is zero. This declares a reading at undefined boundary expressions while preserving all finite-defined cases.
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; §3, pp. 9–11; Theorem 1, p. 16

import Definitions.Def_GaoCascadePricing_UCB_Cascade

open scoped BigOperators

namespace GaoCascadePricing.UCB

/-- Public market data: positive product and price counts and ordered nonnegative prices. -/
structure Market (J K : ℕ) where
  products_pos : 0 < J
  prices_pos : 0 < K
  price : Fin K → ℝ
  price_nonneg : ∀ k, 0 ≤ price k
  price_strictMono : StrictMono price

/-- Maximum of finitely many nonnegative prices on the chosen vector. -/
noncomputable def priceNorm {J K : ℕ} (M : Market J K) (p : Action J K) : ℝ :=
  sSup (Set.range fun j => |M.price (p j)|)

noncomputable def largestPrice {J K : ℕ} (M : Market J K) : ℝ :=
  M.price ⟨K - 1, by have := M.prices_pos; omega⟩

/-- Expected revenue, the expansion of the backward revenue recursion. -/
noncomputable def revenue {J K : ℕ} (M : Market J K) (θ : Cascade J K)
    (p : Action J K) : ℝ :=
  ∑ j, reach θ p j * θ.beta j (p j) * θ.alpha j (p j) * M.price (p j)

/-- Finite nonempty feasible set; its supremum is attained. -/
noncomputable def optimalRevenue {J K : ℕ} (M : Market J K) (θ : Cascade J K) : ℝ :=
  sSup (Set.range (revenue M θ))

noncomputable def betaLower {J K : ℕ} (θ : Cascade J K) : ℝ :=
  sInf (Set.range fun jk : Fin J × Fin K => θ.beta jk.1 jk.2)

noncomputable def betaUpper {J K : ℕ} (θ : Cascade J K) : ℝ :=
  sSup (Set.range fun jk : Fin J × Fin K => θ.beta jk.1 jk.2)

noncomputable def alphaUpper {J K : ℕ} (θ : Cascade J K) : ℝ :=
  sSup (Set.range fun jk : Fin J × Fin K => θ.alpha jk.1 jk.2)

/-- Extended nonnegative reciprocals preserve boundary parameters, with 1/0 = infinity. -/
noncomputable def regretCoefficient {J K : ℕ} (θ : Cascade J K) : ENNReal :=
  min (ENNReal.ofReal (betaLower θ))⁻¹
    (min (ENNReal.ofReal (1 - betaUpper θ))⁻¹
      (ENNReal.ofReal (betaLower θ * (1 - alphaUpper θ)))⁻¹)

end GaoCascadePricing.UCB


