-- Prove2me | Definitions.Def_NetServicePricing_IsOptimal
-- name    : NetServicePricing_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:05.461897+00:00
-- url     : https://prove2.me/theorems/a309aa6c-c755-4796-9778-0ba64b73694f
-- title:
--   Optimal pricing policy
-- statement:
--   A policy $\pi^*=(\tau^*,p^*)$ is **optimal** for a network when its revenue is at least that of every policy:
--
--   $$J(\mathbf 0;\pi)\le J(\mathbf 0;\pi^*)\qquad\text{for all }\pi\in\Pi.$$
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, p.11

import Mathlib
import Definitions.Def_NetServicePricing_Policy
import Definitions.Def_NetServicePricing_revenue

namespace NetServicePricing

/-- **Optimal pricing policy `π* = (τ*, p*)`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, p.11: "The firm's optimal policy that solves problem (3) when consumption grows according to
(2) is denoted by π∗ = (τ∗,p∗) ∈ Π".

A policy is optimal when its revenue is at least the revenue of every policy of the class. -/
def IsOptimal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ α β δ : ℝ) (π : Policy α β) : Prop :=
  ∀ π' : Policy α β, revenue M μ α β δ π'.1 π'.2 ≤ revenue M μ α β δ π.1 π.2

end NetServicePricing


