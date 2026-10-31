-- Prove2me | Definitions.Def_NetServicePricing_Policy
-- name    : NetServicePricing_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:10.15768+00:00
-- url     : https://prove2.me/theorems/0b1d1420-f7f5-4379-a924-a74b5b46430b
-- title:
--   Pricing policies $(\tau,p)$ with one price adjustment
-- statement:
--   A **policy** with one price adjustment is a pair $(\tau,p)$: the firm offers the service for free in periods $1,\dots,\tau$ and charges the price $p$ from period $\tau+1$ on,
--
--   $$p_1=\dots=p_\tau=0,\qquad p_{\tau+1}=p_{\tau+2}=\dots=p.$$
--
--   The free-offering length is any $\tau\in\{0,1,2,\dots\}$ and the price lies in $[0,\alpha/\beta]$.
--
--   **Formalization Note** The price range $[0,\alpha/\beta]$ is a reading: the consumer's optimal consumption (2) is valid "provided that $x^*_{i,t}>0$", and the paper writes the dynamics "for any fixed price $p\le\alpha/\beta$". The paper's Proposition 1 shows the optimal price is at most $\alpha/\beta$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, §3.3, p.10; (4), p.11

import Mathlib

namespace NetServicePricing

/-- **Policies with one price adjustment, `(τ, p)`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, §3.3, p.10: "Let Π denote the class of all policies with only one price adjustment. …
it is represented by the dual (τ,p) where τ is the period in which the firm decides to end the
free-offering … Hence, p1 = ... = pτ = 0 and pτ+1 = pτ+2 = ... = p under policy π."

A policy is a pair of a free-offering length `τ ∈ ℕ` (`τ = 0` allowed) and a price `p ∈ [0, α/β]`.

**Formalization Note** The price domain `[0, α/β]` is a reading of the paper: the consumption
rule (2) is the consumer's optimum "provided that x*i,t > 0" and the closed form (4) is written
"for any fixed price p ≤ α/β" (p.11); prices are nonnegative. -/
abbrev Policy (α β : ℝ) : Type := ℕ × Set.Icc (0 : ℝ) (α / β)

end NetServicePricing


