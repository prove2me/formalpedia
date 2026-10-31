-- Prove2me | Definitions.Def_NetServicePricing_fixedPriceRevenue
-- name    : NetServicePricing_fixedPriceRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:30.091872+00:00
-- url     : https://prove2.me/theorems/07698a12-8fec-4620-9487-6f15b1726dfe
-- title:
--   Fixed-price revenue $\Gamma(x;p)$
-- statement:
--   The firm's total discounted revenue when the initial consumption vector is $x$ and the fixed price $p$ is charged from the start is
--
--   $$\Gamma(x;p)=\sum_{t=1}^{\infty}\delta^{t}\,p\,\langle x_t\mid x_0=x,\mathbf 1\rangle .$$
--
--   **Formalization Note** A real `tsum` with the paper's index $t$ shifted to $t+1$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, §4.1, p.12

import Mathlib
import Definitions.Def_NetServicePricing_fixedPriceTraj

namespace NetServicePricing

/-- **Fixed-price revenue `Γ(x; p)`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, §4.1, p.12: "let Γ(x;p) denote the firm's total discounted revenue where x = (x1,...,xn) is
the initial consumption vector and a fixed price p is charged at τ = 0. That is,
Γ(x;p) = ∑_{t=1}^∞ δ^t p⟨xt|x0 = x,1⟩".

**Formalization Note** A real `tsum` over `t ∈ ℕ`, with the paper's `t` shifted to `t + 1`;
`⟨y, 𝟏⟩ = ∑ᵢ yᵢ`. -/
noncomputable def fixedPriceRevenue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ α β δ p : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑' t : ℕ, δ ^ (t + 1) * p * ∑ i, fixedPriceTraj M μ α β p x (t + 1) i

end NetServicePricing


