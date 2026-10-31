-- Prove2me | Definitions.Def_PlatformPreannouncement_SHNSW_Market
-- name    : PlatformPreannouncement_SHNSW_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:17:50.201956+00:00
-- url     : https://prove2.me/theorems/2f805c54-17cb-42c9-a89e-36bc1a8b50f7
-- title:
--   Fulfilled expectations and feasible joint tariff best responses
-- statement:
--   Fix the SH-NSW primitives, an announcement history $h$, and the two firms' price/fee pairs $r$. A feasible market has nonnegative tariffs and a covered uniform Hotelling allocation on each side. The values used to determine those allocations are computed from the allocations themselves, so network expectations are fulfilled. Both shares lie in $[0,1]$, each new side has mass one, and every positive-mass customer interval satisfies participation and utility-maximizing choice.
--
--   A demand selection $D$ assigns an allocation to every history and tariff profile. It is valid when it selects a feasible allocation whenever any feasible allocation exists at that history and those tariffs. Its arbitrary values at infeasible profiles never enter payoff comparisons. Thus a selection cannot hide a feasible deviation by selecting an infeasible outcome.
--
--   A pricing equilibrium at a history has a feasible selected market and nonnegative net profit for both firms. For each firm and every alternative real price/fee pair admitting some feasible market when the other firm's tariffs are held fixed, the deviating profit, evaluated at the same selection $D$, is at most the current profit. The two tariffs can change jointly and demand is re-evaluated. Nonnegative profit is an equilibrium admissibility condition, not a deviation constraint.
--
--   This is the covered-market reading of the paper's interior demand calculation: endpoint shares and asymmetric histories are included explicitly, with no invented uncovered-market demand law. One selection is used across all comparisons. Its existence will be concluded by the theorem rather than assumed as model data satisfying optimality.
-- source:
--   Chellappa and Mukherjee (2020), DOI 10.1287/mnsc.2020.3606, held source.pdf pp. 17, 19–25, equations (2)–(16); economic conditions pp. 46–47. Explicit covered-market off-path reading.

import Definitions.Def_PlatformPreannouncement_SHNSW_Hotelling
import Definitions.Def_PlatformPreannouncement_SHNSW_Primitives

namespace PlatformPreannouncement.SHNSW

/-- Nonnegative tariffs, covered adoption, and fulfilled network expectations
on both sides. Profit nonnegativity is not a deviation feasibility condition. -/
def FeasibleMarket (P : Parameters) (h : History) (r : Prices) (q : Allocation) : Prop :=
  (∀ i, 0 ≤ (r i).1 ∧ 0 ≤ (r i).2) ∧
  CoveredHotellingSplit P.t (userValue P h r q 0) (userValue P h r q 1) q.users ∧
  CoveredHotellingSplit P.t (developerValue P h r q 0) (developerValue P h r q 1)
    q.developers

abbrev DemandSelection := History → Prices → Allocation

/-- Every tariff profile admitting a feasible market must receive such an
allocation. Values at infeasible profiles never enter incentive comparisons. -/
def ValidSelection (P : Parameters) (D : DemandSelection) : Prop :=
  ∀ h r, (∃ q, FeasibleMarket P h r q) → FeasibleMarket P h r (D h r)

def deviatePrice (r : Prices) (i : Firm) (z : Tariff) : Prices :=
  fun j => if j = i then z else r j

/-- Joint price/fee best responses over every unilateral feasible tariff pair,
with demand re-evaluated using the fixed selection. Nonnegative equilibrium
profits implement the source's separate economic admissibility convention. -/
def PricingEquilibrium (P : Parameters) (D : DemandSelection)
    (h : History) (r : Prices) : Prop :=
  FeasibleMarket P h r (D h r) ∧
  (∀ i, 0 ≤ profit P h r (D h r) i) ∧
  ∀ i z, (∃ q, FeasibleMarket P h (deviatePrice r i z) q) →
    profit P h (deviatePrice r i z) (D h (deviatePrice r i z)) i ≤
      profit P h r (D h r) i

end PlatformPreannouncement.SHNSW


