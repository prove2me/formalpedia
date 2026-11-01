-- Prove2me | Definitions.Def_ResetInventory_expectedNext
-- name    : ResetInventory_expectedNext
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:42.207987+00:00
-- url     : https://prove2.me/theorems/6c4d5e5c-6a89-4b04-bd31-ba942e0c3778
-- title:
--   Expected cost-to-go $\mathbb E\,V((z-w)^+)$
-- statement:
--   Let $f$ be the demand density and $V$ a function of the stock. For a post-order stock level $z$, the **expected cost-to-go** is
--   $$
--   \mathbb E\,V\big((z-w)^+\big)=\int_{\mathbb R}V\big(\max(z-w,0)\big)\,f(w)\,dw .
--   $$
--   With $V=J(\cdot,t+1)$ this is the term $\mathbb E\big(J((z-w)^+,t+1)\big)$ of the dynamic programming equations (22) and of the function $G$, under the lost-sales dynamics $x_{n+1}=(\xi_n+u_n-w_n)^+$ of Assumption 1.
--
--   **Formalization Note** When $f$ vanishes on $(-\infty,0)$ (Assumption 5) and $0\le z\le c_{\max}$, only the values of $V$ on $[0,c_{\max}]$ enter: the integrand is $0$ for $w<0$, and $\max(z-w,0)\in[0,z]$ for $w\ge0$.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, (22), p.14; G, p.16; Assumption 1, p.15

import Mathlib

open MeasureTheory

namespace ResetInventory

/-- The expected cost-to-go `E(V((z − w)⁺))` after the post-order stock `z`, when the demand `w`
has density `f` (Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, the term
`E(J((z − w)⁺, t + 1))` of `G` on p.16 and of (22), p.14, with the dynamics of Assumption 1,
p.15: `x_{n+1} = (ξ_n + u_n − w_n)⁺`).

**Formalization Note** The expectation over the demand is the Lebesgue integral
`∫ V(max(z − w, 0)) f(w) dw`. With `f` a density vanishing on `(-∞, 0)` (Assumption 5) and
`0 ≤ z ≤ c_max`, only the values of `V` on `[0, c_max]` enter, since the integrand is `0` for
`w < 0` and `max(z − w, 0) ∈ [0, z]` for `w ≥ 0`. -/
noncomputable def expectedNext (f V : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ w, V (max (z - w) 0) * f w

end ResetInventory


