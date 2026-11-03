-- Prove2me | Definitions.Def_RegimeDRCVaR_lossG
-- name    : RegimeDRCVaR_lossG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:40.800737+00:00
-- url     : https://prove2.me/theorems/f507c874-1e6b-47b1-a982-f515bf8c503f
-- title:
--   The CVaR loss $G(x,r)=(-x'r-v)^+$
-- statement:
--   For a portfolio $x\in\mathbb R^I$, a return $r\in\mathbb R^I$ and the auxiliary level $v\in\mathbb R$ of the Rockafellar–Uryasev formula,
--   $$
--   G(x,r)=\min\{y \mid y\ge -x'r-v,\ y\ge 0\}=(-x'r-v)^+ .
--   $$
--   The CVaR of the loss $-x'r$ at level $\eta$ is $\min_v\, v+(1-\eta)^{-1}\mathbb E[G(x,r)]$; problems (5), (8) and (11) are built on $G$.
--
--   **Formalization Note** The paper writes $G(x,r)$ and leaves the dependence on $v$ implicit; $v$ is an explicit argument here.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (6), p.10

import Mathlib

open Matrix

namespace RegimeDRCVaR

/-- **The CVaR loss** `G(x, r) = min{y | y ≥ −x′r − v, y ≥ 0} = (−x′r − v)⁺`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, display (6), p.10).

**Formalization Note** `G` depends on the auxiliary variable `v` of the Rockafellar–Uryasev
formula (5), which the paper leaves implicit in the notation `G(x, r)`; here it is an explicit
argument. The minimum over `𝒴` is written in closed form as `max (−x′r − v) 0`. -/
def lossG {I : ℕ} (x : Fin I → ℝ) (v : ℝ) (r : Fin I → ℝ) : ℝ :=
  max (-(x ⬝ᵥ r) - v) 0

end RegimeDRCVaR


