-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_Allocation
-- name    : OpaquePricing_Dominance_Supplement_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:30:52.437917+00:00
-- url     : https://prove2.me/theorems/352b8771-f075-47c2-84da-bc884a9d0734
-- title:
--   Two-item opaque revenue with announced allocation probability
-- statement:
--   For two items and a risk-neutral customer, an announced opaque allocation yields item 1 with probability $\beta$ and item 2 with probability $1-\beta$. Items cost $p\ge0$, and the opaque option costs $r\ge0$. Its value and optimized revenue are
--   $$v^{opaque}=\beta v_1+(1-\beta)v_2,\qquad R_{OPQ}(\mu;\cdot,\beta)=\sup_{p,r\ge0}\mathbb E_\mu[\operatorname{rev}(\beta,p,r;v)].$$
--   The finite menu has two deterministic options and one lottery, with the same published utility and highest-price tie rule. Each allocation probability has its own independent price optimization. For $\beta=1/2$ the lottery is the published risk-neutral full-set opaque option; when $N=2$ there are no other opaque subsets.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix A, pp. 33–34

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Two deterministic options and the announced lottery; none denotes the opaque option. -/
def allocationPrice (p r : ℝ) : Option (Fin 2) → ℝ
  | none => r
  | some _ => p

def allocationValue (β : ℝ) (v : Fin 2 → ℝ) : Option (Fin 2) → ℝ
  | none => β * v 0 + (1 - β) * v 1
  | some i => v i

noncomputable def allocationRevenue (β p r : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  menuRevenue Finset.univ
    (fun o => allocationValue β v o - allocationPrice p r o) (allocationPrice p r)

noncomputable def expAllocation (μ : Measure (Fin 2 → ℝ)) (β p r : ℝ) : ENNReal :=
  ∫⁻ v, ENNReal.ofReal (allocationRevenue β p r v) ∂μ

noncomputable def optAllocation (μ : Measure (Fin 2 → ℝ)) (β : ℝ) : ENNReal :=
  ⨆ (p : ℝ) (r : ℝ) (_ : 0 ≤ p ∧ 0 ≤ r), expAllocation μ β p r

end OpaquePricing.Dominance.Supplement


