-- Prove2me | Definitions.Def_ScarceIdeas_IsOptimalPolicy
-- name    : ScarceIdeas_IsOptimalPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:59.231175+00:00
-- url     : https://prove2.me/theorems/ec6921aa-bac0-447f-b3c4-7b13a38485b1
-- title:
--   Optimal reward policy (feedback form)
-- statement:
--   A feedback reward rule $p:\phi\mapsto p(\phi)$ is an **optimal reward policy** when, from every state $\phi_0\ge0$,
--
--   1. a closed-loop path exists, and
--   2. along every closed-loop path $\varphi$, the reward $t\mapsto p(\varphi(t))$ is admissible and its welfare $J(\phi_0,p\circ\varphi)$ equals $V(\phi_0)$, the supremum over all admissible policies.
--
--   **Formalization Note** Changing $p$ at a single state changes no closed-loop welfare, so this notion does not determine $p$ pointwise; Theorem 3 pins the optimal reward by (22).
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.1, p.18; §4.2, (16)–(17), pp.20–21

import Mathlib
import Definitions.Def_ScarceIdeas_valueFn
import Definitions.Def_ScarceIdeas_ClosedLoop

namespace ScarceIdeas

/-- **Optimal reward policy (feedback form).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.1, p.18 ("the value function and the optimal policy are functions of ϕ") and §4.2, (16)–(17).

A feedback rule `p : ϕ ↦ p(ϕ)` is optimal if from every state `ϕ₀ ≥ 0`
1. a closed-loop path exists, and
2. along **every** closed-loop path `φ`, the reward `t ↦ p(φ(t))` is an admissible policy whose
   welfare equals the value `V(ϕ₀)`, the supremum over **all** admissible policies.

**Formalization Note** Optimality is measured against the supremum over all admissible open-loop
policies (`valueFn`), not against a restricted class. Changing `p` at one state does not change
any closed-loop welfare, so this notion does not pin `p` down pointwise; the goal theorem pins
the optimal reward through (22). -/
def IsOptimalPolicy (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (p : ℝ → ℝ) : Prop :=
  ∀ ϕ₀, 0 ≤ ϕ₀ → (∃ φ, ClosedLoop cL f p ϕ₀ φ) ∧
    ∀ φ, ClosedLoop cL f p ϕ₀ φ → IsAdmissible cL cH (fun t => p (φ t)) ∧
      welfare r v cL f h0 ϕ₀ (fun t => p (φ t)) = valueFn r v cL cH f h0 ϕ₀

end ScarceIdeas


