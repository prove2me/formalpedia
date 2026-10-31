-- Prove2me | Definitions.Def_DeepTierFinance_Direct_Direct
-- name    : DeepTierFinance_Direct_Direct
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:24:33.049388+00:00
-- url     : https://prove2.me/theorems/22027305-fc8f-4cf0-b502-73451bd64560
-- title:
--   Direct-finance payoffs, strict feasibility, and global optimality
-- statement:
--   The direct advance is B=(y-θ₂)⁺ and never subtracts θ₁. Manufacturer success profit is 1-w+rB, and failure profit is -B below the emergency price and 1-w-B at or above it. Tier-1 incremental profit is P(y)(w-v)+(1-P(y))(w-e)⁺; tier-2 profit is its actual optimal terminal cash minus θ₂. The Table 3 failure-row Bs/Bm symbols are read as the single direct advance specified in its caption. DirectFeasible requires a nonnegative implementing rate, an actual tier-2 best response, and strict profit improvement for each of the three agents. DirectOptimal requires an attained global maximum against every feasible direct contract. The low-price tier-1 participation boundary is specified without dividing by P(y): P(y)(w-v)=π₁_old. This equality is not declared feasible. Theorem 3 asserts both the printed boundary and strict improvement; their tension is retained in INSIGHTS.yaml.
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Section 6.1–6.2, printed/PDF pp. 21–23, Table 3 and (12)–(14)

import Definitions.Def_DeepTierFinance_Direct_Delegate

namespace DeepTierFinance.Direct
noncomputable section

/-- Equations (12)-(13) and Table 3; the only principal is (y-theta2)^+. -/
def directProfits (p : Primitives) (e b : ℝ) (m : Contract) (y : ℝ) : Profits :=
  let B := advance b y
  ![p.P y * (1 - m.w + m.r * B) +
      (1 - p.P y) * (if e ≤ m.w then 1 - m.w - B else -B),
    p.P y * (m.w - p.v) + (1 - p.P y) * positivePart (m.w - e),
    supplierCash p b m.r y - b]

/-- Direct-finance feasibility includes implementation and all three strict inequalities (14). -/
def DirectFeasible (p : Primitives) (s : Responses) (T : TraditionalPolicy)
    (e a b : ℝ) (m : Contract) : Prop :=
  p.v ≤ m.w ∧ m.w ≤ 1 ∧ 0 ≤ m.r ∧
  InvestmentResponse p b m.r (s.investment b m.r) ∧
  StrictGain (realizedBenchmark p T e a b) (directProfits p e b m (s.investment b m.r))

/-- Attained global maximum of (13)-(14), not a supremum or KKT definition. -/
def DirectOptimal (p : Primitives) (s : Responses) (T : TraditionalPolicy)
    (e a b : ℝ) (m : Contract) : Prop :=
  DirectFeasible p s T e a b m ∧
  ∀ n, DirectFeasible p s T e a b n →
    directProfits p e b n (s.investment b n.r) 0 ≤ directProfits p e b m (s.investment b m.r) 0

/-- The low-price participation boundary from (12), stated without division by P(y). -/
def DirectParticipationBoundary (p : Primitives) (T : TraditionalPolicy)
    (e a b y w : ℝ) : Prop :=
  p.P y * (w - p.v) = realizedBenchmark p T e a b 1

/-- Data for direct contracts, whose optimality and adoption will be conclusions. -/
abbrev DirectPolicy := ℝ → ℝ → ℝ → Contract

end
end DeepTierFinance.Direct


