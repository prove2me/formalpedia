-- Prove2me | Definitions.Def_NetServicePricing_consumption
-- name    : NetServicePricing_consumption
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:07.536097+00:00
-- url     : https://prove2.me/theorems/87043ffc-9a0b-4fd9-9c97-ce136f9169f3
-- title:
--   Consumption trajectory $x_t$ under a policy $(\tau,p)$
-- statement:
--   Under the policy $(\tau,p)$ and starting from zero consumption, consumption evolves by the linear rule (2) in vector form:
--
--   $$x_0=0,\qquad x_t=(\alpha-\beta p_t)\mathbf 1+\widehat M x_{t-1}\quad(t\ge1),$$
--
--   with $p_t=0$ for $t\le\tau$ and $p_t=p$ for $t>\tau$, where $\mathbf 1=(1,\dots,1)$ and $\widehat M=M+\mu I_n$. Coordinatewise, $x_{i,t}=\mu x_{i,t-1}+\alpha-\beta p_t+\sum_j m_{ij}x_{j,t-1}$.
--
--   **Formalization Note** Periods are natural numbers with $x_0=0$; the vector at period $t+1$ is computed from that at period $t$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, (2), p.9; p.10; vector form, p.11

import Mathlib
import Definitions.Def_NetServicePricing_adjusted

open Matrix

namespace NetServicePricing

/-- **Consumption trajectory under the policy `(τ, p)`, from `x₀ = 0`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, (2), p.9, in the vector form of p.11, "xt|xt−1 = (α −βp)1 + M̂xt−1", with "x0 = 0" and
"p1 = ... = pτ = 0 and pτ+1 = pτ+2 = ... = p" (p.10).

`consumption M μ α β τ p t` is the vector `x_t`: `x₀ = 0` and
`x_{t+1} = (α − β p_{t+1}) 𝟏 + M̂ x_t`, where `p_s = 0` for `s ≤ τ` and `p_s = p` for `s > τ`.

**Formalization Note** `𝟏` is the constant function `1 : Fin n → ℝ`. The paper's periods are
`t = 1, 2, …`; here period `t + 1` is computed from period `t`, with `x 0 = 0`. -/
noncomputable def consumption {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ α β : ℝ) (τ : ℕ) (p : ℝ) :
    ℕ → Fin n → ℝ
  | 0 => 0
  | t + 1 => (α - β * (if t + 1 ≤ τ then 0 else p)) • (1 : Fin n → ℝ) +
      adjusted M μ *ᵥ consumption M μ α β τ p t

end NetServicePricing


