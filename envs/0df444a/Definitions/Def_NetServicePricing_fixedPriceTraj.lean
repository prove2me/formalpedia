-- Prove2me | Definitions.Def_NetServicePricing_fixedPriceTraj
-- name    : NetServicePricing_fixedPriceTraj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:25.199484+00:00
-- url     : https://prove2.me/theorems/2c97d2b2-6021-46b3-94fb-06cb0148eb56
-- title:
--   Consumption trajectory $x_t\mid x_0=x$ at a fixed price
-- statement:
--   For a fixed price $p$ and an initial consumption vector $x$, consumption evolves as
--
--   $$x_0=x,\qquad x_t=(\alpha-\beta p)\mathbf 1+\widehat M x_{t-1}\quad(t\ge1).$$
--
--   This is the trajectory $x_t\mid x_0=x$ used in the fixed-price revenue $\Gamma(x;p)$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, §4.1, p.12; vector form, p.11

import Mathlib
import Definitions.Def_NetServicePricing_adjusted

open Matrix

namespace NetServicePricing

/-- **Consumption trajectory at a fixed price `p` from the initial consumption `x`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, §4.1, p.12 ("x = (x1,...,xn) is the initial consumption vector and a fixed price p is
charged at τ = 0 … where xt evolves according to (2) (or equivalently, (4))"), with the vector form
"xt|xt−1 = (α −βp)1 + M̂xt−1" of p.11.

`fixedPriceTraj M μ α β p x t` is `x_t | x_0 = x`: `x_0 = x` and `x_{t+1} = (α − β p) 𝟏 + M̂ x_t`.

**Formalization Note** `𝟏` is the constant function `1 : Fin n → ℝ`. -/
noncomputable def fixedPriceTraj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ α β p : ℝ) (x : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x
  | t + 1 => (α - β * p) • (1 : Fin n → ℝ) + adjusted M μ *ᵥ fixedPriceTraj M μ α β p x t

end NetServicePricing


