-- Prove2me | Definitions.Def_EngageInfo_designValue
-- name    : EngageInfo_designValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:28.689667+00:00
-- url     : https://prove2.me/theorems/ec84e873-0a03-40d5-baf0-108fa1241a05
-- title:
--   The seller's value $W(\pi)=\Pr(h)\,v^*(\alpha_h)+\Pr(l)\,v^*(\alpha_l)$ and optimal designs
-- statement:
--   For a prior $\alpha^0$ and a design $\pi$, the seller's expected value is
--
--   $$W(\pi)=\Pr(h)\,v^*(\alpha_h)+\Pr(l)\,v^*(\alpha_l).$$
--
--   A design $\pi$ is **optimal** at $\alpha^0$ if it is feasible and $W(\pi')\le W(\pi)$ for every feasible $\pi'$.
--
--   This is the seller's first-stage problem: the seller commits to the design that maximizes its expected equilibrium payoff.
--
--   **Formalization Note** The tie-break of p.6 (the prior is selected when it is as good as another design) is not built into optimality; Proposition 1 states which designs are optimal, so the selection can be read off.
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §2, p.8 ("We focus on the information structure that maximizes the seller's expected value"); §3.2, p.12

import Mathlib
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_designs

namespace EngageInfo

/-- **The seller's expected value of a design, and optimal designs.**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §2, p.8: "We focus on
the information structure that maximizes the seller's expected value"; §3.2, p.12: the seller's
expected value integrates its equilibrium payoff `v∗` over the posterior beliefs.

For a prior `a0 = α⁰` and a design `π`, the seller's expected value is
`W(π) = Pr(h)·v*(α_h) + Pr(l)·v*(α_l)`. A design `π` is **optimal** at `α⁰` if it is feasible and
`W(π') ≤ W(π)` for every feasible `π'`.

**Formalization Note** `v*` is the seller-preferred SPE payoff `vstar`. The paper's tie-break
("the prior is selected … when it is as optimal as some other information structure", p.6) is not
part of `IsOptimal`; the goal theorem states which designs are optimal, so the tie-break can be read
off. -/
noncomputable def designValue (M : Params) (a0 : ℝ) (π : ℝ × ℝ) : ℝ :=
  probH a0 π * vstar M (postH a0 π) + probL a0 π * vstar M (postL a0 π)

/-- `π` is an optimal design for the seller at the prior `a0`. -/
def IsOptimal (M : Params) (a0 : ℝ) (π : ℝ × ℝ) : Prop :=
  π ∈ designs ∧ ∀ π' ∈ designs, designValue M a0 π' ≤ designValue M a0 π

end EngageInfo


