-- Prove2me | Definitions.Def_LNChannels_Exact_IsUniCostFn
-- name    : LNChannels_Exact_IsUniCostFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:21.031036+00:00
-- url     : https://prove2.me/theorems/4f7b40ef-fa1e-466d-b22c-7b5d640f6022
-- title:
--   §5.2, p. 10 — the cost function of a unidirectional channel
-- statement:
--   In a unidirectional channel only node 2 pays, one unit at each jump of a Poisson process with rate $\lambda_2$, and only node 2 commits capital, $l_2$ units. Locked capital costs $r\,l_2$ per unit of time, discounted at the rate $r$; when the balance reaches $l_2$ the channel is reset at cost $B$ and the balance restarts at $0$.
--
--   The expected total future cost $J(n)$ at balance $n$ is characterized by
--
--   $$J(n)=l_2\frac{r}{r+\lambda_2}+J(n+1)\frac{\lambda_2}{r+\lambda_2},\qquad 0\le n<l_2,$$
--
--   together with the reset condition $J(l_2)=J(0)+B$. A function $J:\mathbb Z\to\mathbb R$ satisfying these equations is a **unidirectional cost function**, and the channel's cost $c^{0,l_2}(0,\lambda_2)$ is $J(0)$.
--
--   **Formalization Note** This is a separate definition and not the bidirectional one at $l_1=\lambda_1=0$: with $l_1=0$ the bidirectional boundary condition $J(-0)=J(0)+B$ would force $B=0$. The size $l_2$ is a natural number; values of $J$ outside $\{0,\dots,l_2\}$ are unconstrained.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), pp. 10–11 (PDF pp. 11–12), §5.2

import Mathlib

set_option autoImplicit false

namespace LNChannels.Exact

/-- The expected discounted cost `J : ℤ → ℝ` of a unidirectional channel of size `l₂` in which
only node 2 pays, at rate `λ₂` (§5.2, pp. 10–11): the first-step equation
`J(n) = l₂ r/(r + λ₂) + J(n + 1) λ₂/(r + λ₂)` holds at every balance `0 ≤ n < l₂`, and the reset
condition `J(l₂) = J(0) + B` holds. Values of `J` outside `{0, …, l₂}` are unconstrained. -/
def IsUniCostFn (lam₂ r B : ℝ) (l₂ : ℕ) (J : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, 0 ≤ n → n < (l₂ : ℤ) →
      J n = (l₂ : ℝ) * (r / (r + lam₂)) + J (n + 1) * (lam₂ / (r + lam₂))) ∧
  J (l₂ : ℤ) = J 0 + B

end LNChannels.Exact


