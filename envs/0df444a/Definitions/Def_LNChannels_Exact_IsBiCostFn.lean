-- Prove2me | Definitions.Def_LNChannels_Exact_IsBiCostFn
-- name    : LNChannels_Exact_IsBiCostFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:22.315771+00:00
-- url     : https://prove2.me/theorems/6c84f08e-e157-4e63-bb72-4426ef66e2af
-- title:
--   (15) and §5.1, p. 10 — the cost function of a bidirectional channel
-- statement:
--   Node 1 pays node 2 one unit at the jumps of a Poisson process with rate $\lambda_1$, node 2 pays node 1 one unit at the jumps of an independent Poisson process with rate $\lambda_2$, and the net balance of node 1 is $X_t=N^{\lambda_2}_t-N^{\lambda_1}_t$, starting at $0$. Node 1 commits $l_1$ units and node 2 commits $l_2$ units to a channel; capital locked in the channel costs $r(l_1+l_2)$ per unit of time, discounted at the rate $r$. When the balance reaches $-l_1$ or $+l_2$ the channel is reset at cost $B$ and the balance restarts at $0$.
--
--   The expected total future cost $J(n)$ when the balance equals $n$ is characterized by the first-step equation (15) at every interior balance,
--
--   $$J(n)=(l_1+l_2)\frac{r}{r+\lambda_2+\lambda_1}+J(n+1)\frac{\lambda_2}{r+\lambda_2+\lambda_1}+J(n-1)\frac{\lambda_1}{r+\lambda_2+\lambda_1},\qquad -l_1<n<l_2,$$
--
--   together with the reset (boundary) conditions
--
--   $$J(-l_1)=J(0)+B,\qquad J(+l_2)=J(0)+B.$$
--
--   A function $J:\mathbb Z\to\mathbb R$ is a **bidirectional cost function** with data $(\lambda_1,\lambda_2,r,B,l_1,l_2)$ if it satisfies these equations. The cost of the channel, $c^{l_1,l_2}(\lambda_1,\lambda_2)$, is $J(0)$.
--
--   **Formalization Note** The commitments $l_1,l_2$ are natural numbers because payments are of one unit and the balance lives on the lattice $\{-l_1,\dots,l_2\}$. Values of $J$ off the lattice are unconstrained. The cost is defined by the equations, not by its closed form (3); theorems about "the cost" assert both that a solution exists and that every solution has the stated value at $0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 10 (PDF p. 11), proof of Theorem 1, equation (15) and §5.1 boundary conditions; model p. 5 (PDF p. 6), §3

import Mathlib

set_option autoImplicit false

namespace LNChannels.Exact

/-- The expected discounted cost `J : ℤ → ℝ` of a bidirectional channel with commitments
`l₁, l₂` (proof of Theorem 1, p. 10): the first-step equation (15) holds at every balance
`−l₁ < n < l₂`, and the reset conditions `J(−l₁) = J(0) + B`, `J(+l₂) = J(0) + B` of §5.1 hold.
Values of `J` outside `{−l₁, …, l₂}` are unconstrained. -/
def IsBiCostFn (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ) (J : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
      J n = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
            + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
            + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) ∧
  J (-(l₁ : ℤ)) = J 0 + B ∧ J (l₂ : ℤ) = J 0 + B

end LNChannels.Exact


