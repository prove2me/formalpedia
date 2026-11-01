-- Prove2me | Definitions.Def_ResetInventory_policy
-- name    : ResetInventory_policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:43.755031+00:00
-- url     : https://prove2.me/theorems/4fef1499-77a1-4361-994e-d2b7d1fa2ce6
-- title:
--   The four-threshold reset-and-order policy (23)
-- statement:
--   Fix an age $t$, thresholds $\sigma_t,s_t,\Sigma_t\in[0,+\infty]$, an order-up-to level $S_t$ and a reset order $\varphi$. The **four-threshold policy** (23) prescribes the action $(r,u)$ (reset flag, order quantity) at the stock $x$:
--   $$
--   \pi^*(x,t)=\begin{cases}
--   r=1,\ u=\varphi, & x\in[0,\sigma_t),\\
--   r=0,\ u=S_t-x, & x\in[\sigma_t,s_t),\\
--   r=0,\ u=0, & x\in[s_t,\Sigma_t),\\
--   r=1,\ u=\varphi, & x\in[\Sigma_t,\infty).
--   \end{cases}
--   $$
--   Little stock: reset. Some stock: order up to $S_t$. Enough stock: do nothing. Too much stock: reset.
--
--   **Formalization Note** The thresholds are extended reals ($+\infty$ occurs, e.g. "always reset" is $\sigma_t=s_t=\Sigma_t=+\infty$). The cases are read in the order of (23); when $\sigma_t\le s_t\le\Sigma_t$, which the theorems assert, the four intervals partition $[0,\infty)$ and this is exactly (23). In Lean $\Sigma_t$ is called `Sg` (the letter $\Sigma$ is reserved), and $r=1$ is `true`.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, (23), p.14; Proposition 5, p.19

import Mathlib

namespace ResetInventory

/-- The four-threshold policy (23) of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.14,
at a fixed age `t`, returning the action `(r, u)` (reset flag, order quantity):

* `(r, u) = (1, ϕ)` for `x ∈ [0, σ_t)`;
* `(r, u) = (0, S_t − x)` for `x ∈ [σ_t, s_t)`;
* `(r, u) = (0, 0)` for `x ∈ [s_t, Σ_t)`;
* `(r, u) = (1, ϕ)` for `x ∈ [Σ_t, ∞)`.

Here `σ = σ_t`, `s = s_t`, `Sg = Σ_t` (the letter `Σ` is reserved in Lean), `S = S_t`, and `ϕ` is
the order placed after a reset.

**Formalization Note** The thresholds `σ_t, s_t, Σ_t` lie in `[0, +∞]` and are elements of
`EReal` (`+∞` occurs, e.g. "always reset": `σ_t = s_t = Σ_t = +∞`, p.33). The cases are read in
the order of (23); when `σ_t ≤ s_t ≤ Σ_t` (which the theorems assert) the four intervals partition
`[0, ∞)` and the definition is exactly (23). `true` encodes `r = 1`. -/
noncomputable def policy (σ s Sg : EReal) (S ϕ x : ℝ) : Bool × ℝ :=
  if (x : EReal) < σ then (true, ϕ)
  else if (x : EReal) < s then (false, S - x)
  else if (x : EReal) < Sg then (false, 0)
  else (true, ϕ)

end ResetInventory


