-- Prove2me | Definitions.Def_CloudCostOpt_piStar
-- name    : CloudCostOpt_piStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:09:57.379988+00:00
-- url     : https://prove2.me/theorems/977ec794-045f-4b77-8082-919e8b0ff90a
-- title:
--   Policy $\pi^*$
-- statement:
--   The policy $\pi^*$ uses the assignments of $\hat\pi$, reserves
--
--   $$
--   M_j=\big(\mu_j+z_j\sqrt{\mu_j}\big)^{+}
--   $$
--
--   resources of each type $j$, and in period $t$ rents the excess on demand, $m_{j,t}=(u_{j,t}-M_j)^{+}$.
--
--   The paper defines $M_j=\mu_j+z_j\sqrt{\mu_j}$ and proceeds under the assumption $M_j\ge0$, noting that "it is easy to account for such cases by defining $M^{\pi^*}_j=(\mu_j+z_j\sqrt{\mu_j})^+$" (p.16); where $M_j\ge0$ the two definitions agree.
--
--   **Formalization Note** $\mu_j$ enters through its real value; it is finite by Lemma 3.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §4, pp.16–17

import Mathlib
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Policy `π*`** (§4, pp.16–17): the assignments of `π̂`, the reservation
`M_j = (μ_j + z_j √μ_j)⁺`, and on-demand capacity `m_{j,t} = (u_{j,t} − M_j)⁺`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §4, p.16 (`a^{π*} = a^{π̂}`, `z_j`, `M^{π*}_j := μ_j + z_j·√μ_j`, and the Note: "It is easy to
account for such cases by defining `M^{π*}_j = (μ_j + z_j·√μ_j)⁺`"), p.17 (`m^{π*}_{j,t}`).

Formalization Note: the positive part is the paper's own alternative; where the paper assumes
`M^{π*}_j ≥ 0` the two definitions agree.  `μ_j` enters through `ENNReal.toReal`; it is finite by
Lemma 3. -/
noncomputable def piStar (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) : Policy S where
  M j := Real.toNNReal ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))
  m n h j := (usage S sel n (h (Fin.last n)) j : ℝ≥0) -
    Real.toNNReal ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))
  a := (piHat S sel).a
  assign_sum := (piHat S sel).assign_sum
  capacity n h j := by
    refine ((piHat S sel).capacity n h j).trans ?_
    simp only [piHat, Pi.zero_apply, zero_add]
    exact le_add_tsub

end CloudCostOpt


