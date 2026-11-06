-- Prove2me | Definitions.Def_RandomLPIPM_dTildeDeriv
-- name    : RandomLPIPM_dTildeDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:20.04297+00:00
-- url     : https://prove2.me/theorems/bd4976b8-e951-41e2-a3af-7f02eef8ea7c
-- title:
--   Derivative $\tilde d'$ of the quadratic extension
-- statement:
--   The derivative of $\tilde d$ (at $\rho=1/4$) is
--   $$\tilde d'(u)=\begin{cases}\dfrac{u}{1+u}, & |u|\le 1/4,\\[4pt] \dfrac15+\dfrac{16}{25}\Big(u-\dfrac14\Big), & u>1/4,\\[4pt] -\dfrac13+\dfrac{16}{9}\Big(u+\dfrac14\Big), & u<-1/4.\end{cases}$$
--   It is the coordinate function of $\nabla\Phi_{x,\mu}$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (115)–(116), p.78

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **The derivative `d̃′` of the quadratic extension (115) at `ρ = 1/4`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (115)–(116),
p.78: `d̃′(u) = d′(u) = u/(1 + u)` for `|u| ≤ 1/4`, `d′(1/4) + d″(1/4)(u − 1/4) = 1/5 + (16/25)(u − 1/4)`
for `u > 1/4`, and `d′(−1/4) + d″(−1/4)(u + 1/4) = −1/3 + (16/9)(u + 1/4)` for `u < −1/4`. It is the
coordinate function of `∇Φ_{x,μ}`. -/
noncomputable def dTildeDeriv (u : ℝ) : ℝ :=
  if |u| ≤ 1 / 4 then u / (1 + u)
  else if 1 / 4 < u then 1 / 5 + 16 / 25 * (u - 1 / 4)
  else -1 / 3 + 16 / 9 * (u + 1 / 4)

end RandomLPIPM


