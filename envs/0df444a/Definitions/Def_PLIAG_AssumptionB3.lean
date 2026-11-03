-- Prove2me | Definitions.Def_PLIAG_AssumptionB3
-- name    : PLIAG_AssumptionB3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:29.18526+00:00
-- url     : https://prove2.me/theorems/efbfbd8e-8efb-442c-8629-2f75d2ead1b1
-- title:
--   Assumption B3: Bregman distance growth condition (2.3)
-- statement:
--   **Assumption B3 (Bregman distance growth condition).** There is $\mu>0$ such that
--
--   $$
--   \Phi(y)-\Phi^*\ \ge\ \mu\inf_{z\in\mathcal X}D_w(z,y)\qquad\text{for all }y\in\operatorname{int}\operatorname{dom}w, \tag{2.3}
--   $$
--
--   where $\mathcal X$ is the optimal solution set of (1.1).
--
--   With $w=\tfrac12\|x\|^2$ this is the quadratic growth condition; it is weaker than strong convexity of $\Phi$ and is the only curvature assumption behind the linear rate of Theorem 4.2.
--
--   **Formalization Note** Everything is in `EReal`; $D_w(z,y)=+\infty$ for $z\notin\operatorname{dom}w$, so the infimum is the paper's (as the paper remarks, (2.3) implicitly requires $\mathcal X\cap\operatorname{dom}w\neq\emptyset$). The constant $\mu$ is the argument.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Assumption B3, (2.3), §2.3, p.7

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_Phi
import Definitions.Def_PLIAG_PhiStar
import Definitions.Def_PLIAG_optSet

namespace PLIAG

/-- **Assumption B3, the Bregman distance growth condition** (Zhang–Dai–Guo–Peng,
arXiv:1711.01136v3, §2.3, (2.3), p.7): there is `μ > 0` with
`Φ(y) − Φ* ≥ μ inf_{z ∈ X} D_w(z, y)` for all `y ∈ int dom w`, `X` the optimal solution set.

**Formalization Note.** Everything is in `EReal`; `D_w(z, y) = +∞` for `z ∉ dom w`, so the
infimum over `X` is the paper's (and is `+∞` if `X ∩ dom w = ∅`, which the condition then rules
out at any point of finite `Φ`, as the paper remarks). The constant `μ` is the argument. -/
def AssumptionB3 {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ y ∈ interior (AubinLipschitz.effDom w),
    (μ : EReal) * (⨅ z ∈ optSet w f h, bregman w z y) ≤ Phi f h y - PhiStar w f h

end PLIAG


