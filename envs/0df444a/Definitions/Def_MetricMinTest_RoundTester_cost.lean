-- Prove2me | Definitions.Def_MetricMinTest_RoundTester_cost
-- name    : MetricMinTest_RoundTester_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:25.88178+00:00
-- url     : https://prove2.me/theorems/49b2b73e-e0c8-4709-b812-03e5816c5130
-- title:
--   Total number of queries $\tau$ of a round tester
-- statement:
--   The total number of queries of a round tester is $\tau=\sum_s\sum_j n^{(s)}_j$. For a nonadaptive (one-round) tester this is $N(\xi)=\sum_j n_j(\xi)$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition C.6, p.25; Definition 4.4, p.9

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_totalCount

namespace MetricMinTest

/-- **Total number of queries `τ`** of a round tester. Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition C.6
p.25 (there is no stopping inside a round, so `τ = ∑_s ∑_j n^(s)_j`); for a one-round tester
this is `N(ξ) = ∑_j n_j(ξ)` of Definition 4.4, p.9. -/
def RoundTester.cost {ι : Type} [Fintype ι] {q : ℕ} (T : RoundTester ι q) (ξ : T.Ξ)
    (ω : ι → ℕ → ℝ) : ℕ :=
  ∑ i, T.totalCount ξ ω i

end MetricMinTest


