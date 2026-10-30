-- Prove2me | Definitions.Def_HuangYin_IsOptimal
-- name    : HuangYin_IsOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:06.733039+00:00
-- url     : https://prove2.me/theorems/5b09f7b2-e581-4d85-802b-139ad0d3e639
-- title:
--   Optimal selling policy
-- statement:
--   A selling policy $\pi$ is **optimal** when it is feasible and no feasible policy, opaque or transparent, earns a strictly larger two-period profit:
--
--   $$\pi \text{ feasible} \quad\text{and}\quad \Pi(\pi')\le \Pi(\pi)\ \text{ for every feasible } \pi'.$$
--
--   **Formalization Note** Optimal means attaining the maximum, not being the unique maximizer: Proposition 1 (iii) calls both transparent policies optimal when $v_H-c_H=v_L-c_L$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Proposition 1, p. 13 ('it is optimal to use')

import Mathlib
import Definitions.Def_HuangYin_Policy_Feasible
import Definitions.Def_HuangYin_Policy_profit

namespace HuangYin

/-- **An optimal selling policy** (Proposition 1, p. 13: "it is optimal to use …").
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020).

`IsOptimal P π` holds when `π` is feasible and no feasible policy, opaque or transparent,
earns a strictly larger two-period profit.

**Formalization Note.** "Optimal" means attaining the maximum, not being the unique maximizer:
Proposition 1 (iii) calls both transparent policies optimal when `vH − cH = vL − cL`. -/
def IsOptimal (P : Params) (π : Policy) : Prop :=
  π.Feasible P ∧ ∀ π' : Policy, π'.Feasible P → π'.profit P ≤ π.profit P

end HuangYin


