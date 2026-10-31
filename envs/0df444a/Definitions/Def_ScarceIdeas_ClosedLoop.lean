-- Prove2me | Definitions.Def_ScarceIdeas_ClosedLoop
-- name    : ScarceIdeas_ClosedLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:00.121179+00:00
-- url     : https://prove2.me/theorems/49d81174-0e65-45d3-8fe2-9e042e487c92
-- title:
--   Closed-loop path $d\varphi/dt=F(p(\varphi(t)))$ of a feedback reward
-- statement:
--   For a feedback reward rule $p:\phi\mapsto p(\phi)$, a path $\varphi$ is a **closed-loop path** from $\phi_0$ when $\varphi(0)=\phi_0$ and
--
--   $$\frac{d\varphi(t)}{dt}=F\bigl(p(\varphi(t))\bigr)\qquad(t\ge0),$$
--
--   with a one-sided derivative at $t=0$.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, (2), p.13; §4.1, p.18

import Mathlib
import Definitions.Def_ScarceIdeas_costCDF

namespace ScarceIdeas

/-- **Closed-loop state path of a feedback reward rule.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
(2), p.13 ("dϕ(t)/dt = F(p(t))") with the feedback form of §4.1, p.18 ("the value function and
the optimal policy are functions of ϕ").

For a feedback rule `p : ϕ ↦ p(ϕ)`, a path `φ` is a closed-loop path from `ϕ₀` if `φ(0) = ϕ₀` and
`dφ/dt = F(p(φ(t)))` for every `t ≥ 0` (one-sided at `t = 0`).

**Formalization Note** Derivatives within `[0, ∞)`. -/
def ClosedLoop (cL : ℝ) (f : ℝ → ℝ) (p : ℝ → ℝ) (ϕ₀ : ℝ) (φ : ℝ → ℝ) : Prop :=
  φ 0 = ϕ₀ ∧ ∀ t, 0 ≤ t → HasDerivWithinAt φ (costCDF cL f (p (φ t))) (Set.Ici 0) t

end ScarceIdeas


