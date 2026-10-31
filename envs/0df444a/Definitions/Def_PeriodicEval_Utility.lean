-- Prove2me | Definitions.Def_PeriodicEval_Utility
-- name    : PeriodicEval_Utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:00.861983+00:00
-- url     : https://prove2.me/theorems/a6673983-05b7-4629-8cfc-30ab1f5da598
-- title:
--   The S-shaped utility $U$ and the one-period reward $G_a(y)=U(y-\gamma)+ay^\alpha$
-- statement:
--   The agent's utility is the Tversky–Kahneman piecewise power function
--
--   $$U(x)=\begin{cases}x^\alpha,&x\ge0,\\-k|x|^\alpha,&x<0,\end{cases}$$
--
--   concave on gains and convex on losses, with loss coefficient $k\ge0$. For a parameter $a\in\mathbb R$, the one-period reward of the auxiliary problem is
--
--   $$G_a(y):=U(y-\gamma)+a\,y^\alpha,\qquad y\ge0.$$
--
--   $G_a$ combines the utility of the period's performance relative to the target $\gamma$ with $a$ times the scaled continuation value $y^\alpha$; it is neither concave nor monotone in general.
--
--   **Formalization Note** $G_a$ is defined on all of $\mathbb R$ in Lean but used only at $y\ge0$.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), eq. (3), p.8 and eq. (13), p.13

import Mathlib
import Definitions.Def_PeriodicEval_Params

namespace PeriodicEval

/-- The S-shaped (Tversky–Kahneman) utility (3), SSRN 3971852 (June 20, 2023), p.8:
`U(x) = x^α` for `x ≥ 0` and `U(x) = −k|x|^α` for `x < 0`.

**Formalization Note** `x ^ α` is `Real.rpow`, applied only to the nonnegative base `x` or
`|x|`. -/
noncomputable def U (p : Params) (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ p.α else -(p.k * |x| ^ p.α)

/-- The one-period reward `G_a(y) := U(y − γ) + a y^α` of (13), SSRN 3971852
(June 20, 2023), p.13, for a parameter `a ∈ ℝ`.

**Formalization Note** The paper defines `G_a` on `ℝ₊`; the Lean function is defined on all
of `ℝ` but is only ever used at `y ≥ 0` (where `y ^ α` is the usual power). -/
noncomputable def G (p : Params) (a y : ℝ) : ℝ := U p (y - p.γ) + a * y ^ p.α

end PeriodicEval


