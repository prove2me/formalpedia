-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_powerPerspective
-- name    : KuhnWass2019_Reformulation_powerPerspective
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:14:33.62398+00:00
-- url     : https://prove2.me/theorems/f55396ec-ff1d-419b-b07c-75dd3c3df6d5
-- title:
--   Closed conjugate-power penalty and the order-one endpoint
-- statement:
--   For $p>1$, put $q=p/(p-1)$ and $\varphi(q)=(q-1)^{q-1}/q^q$. For $\gamma>0$, the penalty is $\varphi(q)\gamma(\|u\|_*/\gamma)^q$. At $\gamma=0$ it is zero for $u=0$ and $+\infty$ otherwise. For $p=1$, it is zero when $\|u\|_*\le\gamma$ and $+\infty$ otherwise. Negative multipliers have value $+\infty$. Only $p\ge1$ is used in the theorem; the total function outside that domain carries no claim. The dual norm is the operator norm of a continuous linear functional.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 11, equation (11) and Remark 1

import Mathlib

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Equation (11) and Remark 1: the conjugate power penalty, for p ≥ 1.
At p=1 this is the dual-norm-ball indicator. For p>1 its zero-multiplier
value is the closed perspective, not real division by zero. Negative multipliers
are outside the feasible domain and assigned positive infinity. -/
noncomputable def powerPerspective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p γ : ℝ) (u : StrongDual ℝ E) : EReal :=
  if γ < 0 then ⊤ else
  if p = 1 then (if ‖u‖ ≤ γ then 0 else ⊤) else
  if γ = 0 then (if u = 0 then 0 else ⊤) else
  let q := p / (p - 1)
  (((q - 1) ^ (q - 1) / q ^ q * γ * (‖u‖ / γ) ^ q : ℝ) : EReal)

end KuhnWass2019.Reformulation


