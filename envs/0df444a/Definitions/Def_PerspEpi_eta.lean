-- Prove2me | Definitions.Def_PerspEpi_eta
-- name    : PerspEpi_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:33.432333+00:00
-- url     : https://prove2.me/theorems/888a67da-d7d0-4027-b9c0-2372d4822b8b
-- title:
--   Proximal value function $\eta^f_{\bar x}$
-- statement:
--   For $f \in \Gamma_0(E)$ and $\bar x \in E$ the **proximal value function** is
--
--   $$
--   \eta^f_{\bar x}(\lambda) = \begin{cases} f(P_\lambda f(\bar x)) & \lambda > 0,\\ f(P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x)) & \lambda \le 0. \end{cases}
--   $$
--
--   Its root-finding role is the content of Corollary 14: the epigraphical projection is found at the root of $\lambda \mapsto \eta^f_{\bar x}(\lambda) - \lambda - \bar\alpha$.
--
--   **Formalization Note** Values in `EReal`; $f(P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x))$ may be $+\infty$.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §5, p.19

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox

namespace PerspEpi

/-- **Proximal value function** `η^f_x̄`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §5, p.19:
"η^f_x̄ : λ ∈ ℝ ↦ f(P_λ f(x̄)) if λ > 0; f(P_cl(dom f)(x̄)) if λ ≤ 0."

**Formalization Note.** Values in `EReal`: `f(P_cl(dom f)(x̄))` may be `+∞`. -/
noncomputable def eta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal)
    (xbar : E) (lam : ℝ) : EReal :=
  if 0 < lam then f (prox f lam xbar) else f (projC (closure (AubinLipschitz.effDom f)) xbar)

end PerspEpi


