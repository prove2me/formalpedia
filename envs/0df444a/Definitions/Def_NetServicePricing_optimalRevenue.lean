-- Prove2me | Definitions.Def_NetServicePricing_optimalRevenue
-- name    : NetServicePricing_optimalRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:10.606995+00:00
-- url     : https://prove2.me/theorems/2ba2d3a8-c9c6-495b-8799-c6b9b3458532
-- title:
--   Optimal revenue $J(\mathbf 0)=\max_{\pi\in\Pi}J(\mathbf 0;\pi)$
-- statement:
--   The firm's **optimal revenue** from zero initial consumption is the best revenue over all policies with one price adjustment:
--
--   $$J(\mathbf 0)=\max_{\pi\in\Pi}J(\mathbf 0;\pi).$$
--
--   **Formalization Note** The maximum is written as a real supremum over all policies $(\tau,p)$, $\tau\in\mathbb N$, $p\in[0,\alpha/\beta]$, a nonempty set; under the standing assumptions the revenues are bounded above, so the supremum is genuine.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, (3), p.10

import Mathlib
import Definitions.Def_NetServicePricing_Policy
import Definitions.Def_NetServicePricing_revenue

namespace NetServicePricing

/-- **Optimal revenue `J(0) = max_{π ∈ Π} J(0; π)`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, (3), p.10: "J(x0) = max_{π∈Π} { ∑_{t=1}^∞ δ^{τ+t} p⟨xτ+t,1⟩ } … J(.) is the firm's optimal
value function", at "x0 = 0".

**Formalization Note** The maximum is a real supremum over the policy class `Policy α β`
(`τ ∈ ℕ`, `p ∈ [0, α/β]`), which is nonempty. Under the standing assumptions the revenues are
bounded above, so this is the genuine supremum. -/
noncomputable def optimalRevenue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ α β δ : ℝ) : ℝ :=
  ⨆ π : Policy α β, revenue M μ α β δ π.1 π.2

end NetServicePricing


