-- Prove2me | Definitions.Def_ResetInventory_form28
-- name    : ResetInventory_form28
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:02.056993+00:00
-- url     : https://prove2.me/theorems/c6ec8d04-cda9-4679-a06e-249e88cdb757
-- title:
--   The four-piece value function (28)
-- statement:
--   Given a cost-to-go $J$, thresholds $\sigma_t,s_t,\Sigma_t\in[0,+\infty]$ and a level $S_t$, the right side of (28) at the stock $x$ is
--   $$
--   \begin{cases}
--   J_0+\mathbb E\,s(x,t,w), & x\in[0,\sigma_t),\\
--   c(S_t-x)+K+H(S_t,t)+\gamma\,\mathbb E\big(J((S_t-w)^+,t+1)\big), & x\in[\sigma_t,s_t),\\
--   H(x,t)+\gamma\,\mathbb E\big(J((x-w)^+,t+1)\big), & x\in[s_t,\Sigma_t),\\
--   J_0+\mathbb E\,s(x,t,w), & x\ge\Sigma_t,
--   \end{cases}
--   $$
--   with $J_0=J(0,0)$ and $\mathbb E\,s(x,t,w)=R(x,t)$. The pieces are the values of the four actions of the policy (23).
--
--   **Formalization Note** Thresholds are extended reals and the cases are read in the order of (28), as for the policy (23).
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, (28), Proposition 6, p.21

import Mathlib
import Definitions.Def_ResetInventory_ResetModel
import Definitions.Def_ResetInventory_expectedNext

namespace ResetInventory

/-- The right-hand side of (28) (Proposition 6, Lee, Mintz, Aswani, Shen, Yang,
arXiv:2209.03571v1, p.21): with `J₀ = J(0, 0)`,

* `J₀ + E(s(x, t, w))` for `x ∈ [0, σ_t)`;
* `c(S_t − x) + K + H(S_t, t) + γ E(J((S_t − w)⁺, t + 1))` for `x ∈ [σ_t, s_t)`;
* `H(x, t) + γ E(J((x − w)⁺, t + 1))` for `x ∈ [s_t, Σ_t)`;
* `J₀ + E(s(x, t, w))` for `x ≥ Σ_t`.

Here `σ = σ_t`, `s = s_t`, `Sg = Σ_t` and `S = S_t`, and `E s(x, t, w) = R(x, t)`.

**Formalization Note** Thresholds in `EReal`, cases read in the order of (28), as in `policy`. -/
noncomputable def form28 (mdl : ResetModel) (J : ℝ → ℕ → ℝ) (σ s Sg : EReal) (S x : ℝ)
    (t : ℕ) : ℝ :=
  if (x : EReal) < σ then J 0 0 + mdl.R x t
  else if (x : EReal) < s then
    mdl.c * (S - x) + mdl.K + mdl.H S t + mdl.γ * expectedNext mdl.f (fun y => J y (t + 1)) S
  else if (x : EReal) < Sg then
    mdl.H x t + mdl.γ * expectedNext mdl.f (fun y => J y (t + 1)) x
  else J 0 0 + mdl.R x t

end ResetInventory


