-- Prove2me | Definitions.Def_PerspEpi_phiBar
-- name    : PerspEpi_phiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:55.507047+00:00
-- url     : https://prove2.me/theorems/dd28a68f-b856-43ae-bd54-32ba0ebd7715
-- title:
--   The function $\bar\varphi^f_{\bar x}$ of display (27)
-- statement:
--   For $f \in \Gamma_0(E)$ and $\bar x \in E$, with $C = \operatorname{cl}(\operatorname{dom} f)$ and $d_C$ the distance to $C$, display (27) defines
--
--   $$
--   \bar\varphi^f_{\bar x}(\lambda) = \begin{cases} -\lambda\, e_\lambda f(\bar x) & \lambda > 0,\\ -\tfrac12 d_C^2(\bar x) & \lambda = 0,\\ -\lambda f(P_C(\bar x)) - \tfrac12 d_C^2(\bar x) & \lambda < 0. \end{cases}
--   $$
--
--   It is a convex function whose derivative is $-\eta^f_{\bar x}$ (Corollary 12), and the scalar problem $\min_{\lambda\ge0}\{\bar\varphi^f_{\bar x}(\lambda) + \bar\alpha\lambda + \frac12\lambda^2\}$ determines the epigraphical projection (Corollary 14).
--
--   **Formalization Note** Values in `EReal`. For $\lambda < 0$ and $f(P_C(\bar x)) = +\infty$ the value is $+\infty$, as on the page. $d_C$ is `Metric.infDist`.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §5, p.20, display (27)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_MoreauChance_Consistency_Basic

namespace PerspEpi

/-- **The function φ̄^f_x̄**, display (27). Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §5, p.20:
"φ̄^f_x̄ : λ ∈ ℝ ↦ −λe_λ f(x̄) if λ > 0; −½d²_cl(dom f)(x̄) if λ = 0;
−λf(P_cl(dom f)(x̄)) − ½d²_cl(dom f)(x̄) if λ < 0".

**Formalization Note.** Values in `EReal`. For `λ < 0`, `−λ > 0` and `(−λ) · (+∞) = +∞`, so
`φ̄(λ) = +∞` when `f(P_cl(dom f)(x̄)) = +∞`, as on the page. `d_C(x̄)` is `Metric.infDist x̄ C`; `e_λ f` is the published
`MoreauChance.Consistency.moreauEnv` and `dom f` the published `AubinLipschitz.effDom f`. -/
noncomputable def phiBar {E : Type*} [NormedAddCommGroup E] (f : E → EReal) (xbar : E)
    (lam : ℝ) : EReal :=
  if 0 < lam then ((-lam : ℝ) : EReal) * MoreauChance.Consistency.moreauEnv f lam xbar
  else if lam = 0 then ((-(1 / 2) * Metric.infDist xbar (closure (AubinLipschitz.effDom f)) ^ 2 : ℝ) : EReal)
  else ((-lam : ℝ) : EReal) * f (projC (closure (AubinLipschitz.effDom f)) xbar) -
    ((1 / 2 * Metric.infDist xbar (closure (AubinLipschitz.effDom f)) ^ 2 : ℝ) : EReal)

end PerspEpi


