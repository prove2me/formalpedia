-- Prove2me | Definitions.Def_ScarceIdeas_statePath
-- name    : ScarceIdeas_statePath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:57.547983+00:00
-- url     : https://prove2.me/theorems/604bd6fd-294d-4bab-b68a-e0611eed3f58
-- title:
--   State path $\Phi(t)=\phi+\int_0^tF(u(s))ds$
-- statement:
--   Starting from the state $\phi$ and following the reward policy $u$, the cumulative innovation incentive at time $t$ is
--
--   $$\Phi(t)=\phi+\int_0^tF(u(s))\,ds ,$$
--
--   so that $d\Phi/dt=F(u(t))$, as in (2). The paper starts at $\phi(0)=0$; the value function needs every starting state.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §3, (1)–(2), pp.12–13; §4.1, p.18

import Mathlib
import Definitions.Def_ScarceIdeas_costCDF

namespace ScarceIdeas

/-- **Cumulative innovation incentive along a policy.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§3, (1)–(2), pp.12–13: "ϕ(t) = ∫_0^t F(p(s))ds", "dϕ(t)/dt = F(p(t))"; §4.1, p.18, where `ϕ`
is the state variable.

Started from the state `ϕ` at time `0` and driven by the reward policy `u`, the state at time `t` is

$$\Phi(t)=\phi+\int_0^t F(u(s))\,ds .$$

**Formalization Note** The paper's path starts at `ϕ(0) = 0`; the value function `V(ϕ)` of every
state needs the path started at an arbitrary state `ϕ ≥ 0`. -/
noncomputable def statePath (cL : ℝ) (f : ℝ → ℝ) (ϕ : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ϕ + ∫ s in (0 : ℝ)..t, costCDF cL f (u s)

end ScarceIdeas


