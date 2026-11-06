-- Prove2me | Definitions.Def_RandomLPIPM_dTilde
-- name    : RandomLPIPM_dTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:36.946203+00:00
-- url     : https://prove2.me/theorems/e62bdd22-6a6d-4773-ae83-d6979bd3504e
-- title:
--   Quadratic extension $\tilde d$ of $d$ at $\rho=1/4$, (115)
-- statement:
--   With $\rho=1/4$, the quadratic extension of $d(u)=u-\log(1+u)$ is
--   $$\tilde d(u)=\begin{cases} d(u), & |u|\le\rho,\\ d(\rho)+d'(\rho)(u-\rho)+\tfrac12 d''(\rho)(u-\rho)^2, & u>\rho,\\ d(-\rho)+d'(-\rho)(u+\rho)+\tfrac12 d''(-\rho)(u+\rho)^2, & u<-\rho.\end{cases}$$
--   With $d'(u)=u/(1+u)$ and $d''(u)=(1+u)^{-2}$: $d'(1/4)=1/5$, $d''(1/4)=16/25$, $d'(-1/4)=-1/3$, $d''(-1/4)=16/9$.
--
--   $\tilde d$ is $C^1$ with $\tilde d''\in[16/25,16/9]$, which makes the re-centering objective $\Phi_{x,\mu}$ globally well conditioned while agreeing with the log-barrier on the box $\|u\|_\infty\le1/4$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (115), p.78

import Mathlib
import Definitions.Def_RandomLPIPM_dDiv

open Matrix

namespace RandomLPIPM

/-- **The quadratic extension `d̃` of `d` at `ρ = 1/4`, (115).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (115), p.78:
`d̃(u) = d(u)` for `|u| ≤ ρ`; `d(ρ) + d′(ρ)(u − ρ) + ½d″(ρ)(u − ρ)²` for `u > ρ`;
`d(−ρ) + d′(−ρ)(u + ρ) + ½d″(−ρ)(u + ρ)²` for `u < −ρ`; "For the remaining section, we consider
`d̃` at `ρ = 1/4`".

**Formalization Note.** The derivatives are written out: `d′(u) = u/(1 + u)` and
`d″(u) = (1 + u)⁻²`, so `d′(1/4) = 1/5`, `d″(1/4) = 16/25`, `d′(−1/4) = −1/3`, `d″(−1/4) = 16/9`. -/
noncomputable def dTilde (u : ℝ) : ℝ :=
  if |u| ≤ 1 / 4 then dDiv u
  else if 1 / 4 < u then dDiv (1 / 4) + 1 / 5 * (u - 1 / 4) + 1 / 2 * (16 / 25) * (u - 1 / 4) ^ 2
  else dDiv (-1 / 4) + (-1 / 3) * (u + 1 / 4) + 1 / 2 * (16 / 9) * (u + 1 / 4) ^ 2

end RandomLPIPM


