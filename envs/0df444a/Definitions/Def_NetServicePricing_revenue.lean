-- Prove2me | Definitions.Def_NetServicePricing_revenue
-- name    : NetServicePricing_revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:09.166994+00:00
-- url     : https://prove2.me/theorems/c1539ae8-c245-43f1-affb-bc8eeaed785b
-- title:
--   Discounted revenue $J(\mathbf 0;\tau,p)$ of a policy
-- statement:
--   The firm's **total discounted revenue** of the policy $(\tau,p)$, starting from $x_0=0$, is
--
--   $$J(\mathbf 0;\tau,p)=\sum_{t=1}^{\infty}\delta^{\tau+t}\,p\,\langle x_{\tau+t},\mathbf 1\rangle,$$
--
--   where $\langle x_t,\mathbf 1\rangle=\sum_i x_{i,t}$ is the total consumption in period $t$ and $\delta$ is the discount factor. This is the objective of the firm's pricing problem (3).
--
--   **Formalization Note** The series is a real `tsum` with the paper's index $t$ shifted to $t+1$. Under Assumption 1 it converges absolutely, so the value is the genuine sum.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, (3), p.10; notation J(0;τ,p), p.ec4

import Mathlib
import Definitions.Def_NetServicePricing_consumption

namespace NetServicePricing

/-- **Total discounted revenue `J(0; τ, p)` of the policy `(τ, p)`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, (3), p.10: "J(x0) = max_{π∈Π} { ∑_{t=1}^∞ δ^{τ+t} p⟨xτ+t,1⟩ }", the objective of (3) for
the policy `(τ, p)` from `x0 = 0`; the notation `J(0;τ,p)` is that of p.ec4.

$$J(0;\tau,p)=\sum_{t=1}^\infty \delta^{\tau+t}\,p\,\langle x_{\tau+t},\mathbf 1\rangle.$$

**Formalization Note** The sum is a real `tsum` over `t ∈ ℕ` with the paper's `t` shifted to
`t + 1`; `⟨x, 𝟏⟩ = ∑ᵢ xᵢ`. Under Assumption 1 the series converges absolutely (the theorems of the
mission state this), so the `tsum` is the genuine sum. -/
noncomputable def revenue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ α β δ : ℝ) (τ : ℕ) (p : ℝ) : ℝ :=
  ∑' t : ℕ, δ ^ (τ + t + 1) * p * ∑ i, consumption M μ α β τ p (τ + t + 1) i

end NetServicePricing


